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

@[expose]
noncomputable def g_fdprj1valV (x : Var) (C : Class) (D : Class)
    (_dv_C_D : Disjoint C.fv D.fv) (_dv_C_x : x ∉ C.fv) (_dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
          (.classEq (.cv x) (syn_csn (syn_csn D))))) :=
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
  have dv_cache_0004 : a ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0005 : b ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0006 : c ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0007 : a ∉ ((syn_cidk)).fv :=
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
  have dv_cache_0008 : b ∉ ((syn_cidk)).fv :=
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
  have dv_cache_0009 : c ∉ ((syn_cidk)).fv :=
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
    a ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv :=
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
    b ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv :=
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
    c ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv :=
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
      ((syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))).fv :=
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
      ((syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D))).fv :=
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
  have dv_cache_0021 : a ∉ ((Wff.classEq (.cv x) (syn_csn (syn_csn D)))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfdprj1))
  have p0001 :=
    @g_eleq2i (syn_cfdprj1) (syn_cins2k (syn_cidk)) (syn_copk (.cv x) (syn_copk C D))
      p0000
  have p0002 := @g_vex x
  have p0003 := @g_opkex C D
  have p0004 :=
    @g_opkelins2kg a b c (.cv x) (syn_copk C D) (syn_cidk) (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0005 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (syn_copk C D) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cins2k (syn_cidk))) (syn_wex a
          (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
                (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk)))))))
      p0002 p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cins2k (syn_cidk)))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
              (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk))))))
      p0001 p0005
  have p0007 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1)) (syn_wex a (syn_wex b
            (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
                (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk)))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0006
  have p0008 := @g_biid (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
  have p0009 :=
    @g_a1i
      (syn_wb (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0008
  have p0010 := @g_vex c
  have p0011 := @g_opkthg C D (.cv b) (.cv c) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp3an3 (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
      (.classMem (.cv c) (syn_cvv))
      (syn_wb (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
        (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c))))
      p0010 p0011
  have p0013 := @g_eqcom C (.cv b)
  have p0014 := @g_eqcom D (.cv c)
  have p0015 :=
    @g_anbi12i (.classEq C (.cv b)) (.classEq (.cv b) C) (.classEq D (.cv c))
      (.classEq (.cv c) D) p0013 p0014
  have p0016 :=
    @g_a1i
      (syn_wb (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c)))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0015
  have p0017 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
      (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c)))
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) p0012 p0016
  have p0018 := @g_vex a
  have p0020 := @g_opkelidkg (.cv a) (.cv c) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (.cv c) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk)) (.classEq (.cv a) (.cv c)))
      p0018 p0010 p0020
  have p0022 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk)) (.classEq (.cv a) (.cv c)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0021
  have p0023 :=
    @g_n_3anbi123d (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D))
      (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk)) (.classEq (.cv a) (.cv c)) p0009
      p0017 p0022
  have p0024 :=
    @g_n_3exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
        (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk)))
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0023
  have p0025 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
              (.classMem (syn_copk (.cv a) (.cv c)) (syn_cidk))))))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))))))
      p0007 p0024
  have p0026 :=
    @g_n_3anass (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))
  have p0027 :=
    @g_anass (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))
  have p0028 :=
    @g_anbi2i
      (syn_wa (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0027
  have p0029 :=
    @g_bitri
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      p0026 p0028
  have p0030 :=
    @g_an12 (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv b) C)
      (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))
  have p0031 :=
    @g_bitri
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      p0029 p0030
  have p0032 :=
    @g_a1i
      (syn_wb (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
        (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0031
  have p0033 :=
    @g_n_3exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0032
  have p0034 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))))))
      (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv b) C)
              (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      p0025 p0033
  have p0035 :=
    @g_excom
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      b c
  have p0036 :=
    @g_exbii
      (syn_wex b (syn_wex c (syn_wa (.classEq (.cv b) C)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))
      (syn_wex c (syn_wex b (syn_wa (.classEq (.cv b) C)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))
      a p0035
  have p0037 :=
    @g_a1i
      (syn_wb (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv b) C)
                (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                  (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))) (syn_wex a
          (syn_wex c (syn_wex b (syn_wa (.classEq (.cv b) C)
                (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                  (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0036
  have p0038 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv b) C)
              (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      (syn_wex a (syn_wex c (syn_wex b (syn_wa (.classEq (.cv b) C)
              (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      p0034 p0037
  have p0039 := @g_simpl (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0040 :=
    @g_biidd (.classEq (.cv b) C)
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
  have p0041 :=
    @g_ceqsexgv
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      b C (syn_cvv) dv_cache_0016 dv_cache_0017 p0040
  have p0042 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem C (syn_cvv))
      (syn_wb (syn_wex b (syn_wa (.classEq (.cv b) C)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
        (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      p0039 p0041
  have p0043 :=
    @g_n_2exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wex b (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      a c dv_cache_0013 dv_cache_0015 p0042
  have p0044 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wex c (syn_wex b (syn_wa (.classEq (.cv b) C)
              (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      (syn_wex a (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      p0038 p0043
  have p0045 :=
    @g_an12 (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv c) D)
      (.classEq (.cv a) (.cv c))
  have p0046 :=
    @g_a1i
      (syn_wb (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))) (syn_wa (.classEq (.cv c) D)
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv c)))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0045
  have p0047 :=
    @g_n_2exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (.classEq (.cv a) (.cv c))))
      a c dv_cache_0013 dv_cache_0015 p0046
  have p0048 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      (syn_wex a (syn_wex c (syn_wa (.classEq (.cv c) D)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (.cv a) (.cv c))))))
      p0044 p0047
  have p0049 := @g_simpr (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0050 := @g_eqeq2 (.cv c) D (.cv a)
  have p0051 :=
    @g_anbi2d (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)) (.classEq (.cv a) D)
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0050
  have p0052 :=
    @g_ceqsexgv
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv c)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)) c D
      (syn_cvv) dv_cache_0018 dv_cache_0019 p0051
  have p0053 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem D (syn_cvv))
      (syn_wb (syn_wex c (syn_wa (.classEq (.cv c) D)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv c)))))
        (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)))
      p0049 p0052
  have p0054 :=
    @g_exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wex c (syn_wa (.classEq (.cv c) D)
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv c)))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)) a
      dv_cache_0013 p0053
  have p0055 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wex c (syn_wa (.classEq (.cv c) D)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (.cv a) (.cv c))))))
      (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)))
      p0048 p0054
  have p0056 :=
    @g_ancom (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)
  have p0057 :=
    @g_exbii (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D))
      (syn_wa (.classEq (.cv a) D) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))) a p0056
  have p0058 :=
    @g_a1i
      (syn_wb (syn_wex a
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)))
        (syn_wex a
          (syn_wa (.classEq (.cv a) D) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0057
  have p0059 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) D)))
      (syn_wex a (syn_wa (.classEq (.cv a) D) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))
      p0055 p0058
  have p0061 := @g_sneq (.cv a) D
  have p0062 := @g_sneqd (.classEq (.cv a) D) (syn_csn (.cv a)) (syn_csn D) p0061
  have p0063 :=
    @g_eqeq2d (.classEq (.cv a) D) (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn D))
      (.cv x) p0062
  have p0064 :=
    @g_ceqsexgv (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (.classEq (.cv x) (syn_csn (syn_csn D))) a D (syn_cvv) dv_cache_0020 dv_cache_0021
      p0063
  have p0065 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem D (syn_cvv))
      (syn_wb (syn_wex a
          (syn_wa (.classEq (.cv a) D) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))
        (.classEq (.cv x) (syn_csn (syn_csn D))))
      p0049 p0064
  have p0066 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (syn_wex a (syn_wa (.classEq (.cv a) D) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))
      (.classEq (.cv x) (syn_csn (syn_csn D))) p0059 p0065
  exact p0066

@[expose]
noncomputable def g_fde1valJp (A : Class) (B : Class) (C : Class) (D : Class) (e : Var)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (_dv_A_e : e ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_D : Disjoint B.fv D.fv) (_dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (_dv_C_e : e ∉ C.fv) (_dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C B) (.classMem D B))
        (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))
          (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) :=
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
  have dv_cache_0001 : x ∉ ((syn_csn (.cv e))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_e,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cfdprj1)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cfdmem)).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_wa (.classMem C B) (.classMem D B))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_csn (syn_csn D))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfde1 A B))
  have p0001 :=
    @g_eleq2i (syn_cfde1 A B)
      (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0001
  have p0003 :=
    @g_elin (syn_copk (syn_csn (.cv e)) (syn_copk C D))
      (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)
  have p0004 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B))) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
            (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)))
      p0002 p0004
  have p0006 := @g_snex (.cv e)
  have p0007 := @g_opkex C D
  have p0008 :=
    @g_opkelcok x (syn_csn (.cv e)) (syn_copk C D) (syn_cfdprj1) (syn_cfdmem)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_ccomk (syn_cfdprj1) (syn_cfdmem))) (syn_wex x
          (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1)))))
      (syn_wa (.classMem C B) (.classMem D B)) p0008
  have p0010 := @g_biid (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
  have p0011 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))
      (syn_wa (.classMem C B) (.classMem D B)) p0010
  have p0012 := @g_simpl (.classMem C B) (.classMem D B)
  have p0013 := @g_elex C B
  have p0014 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B)
      (.classMem C (syn_cvv)) p0012 p0013
  have p0015 := @g_simpr (.classMem C B) (.classMem D B)
  have p0016 := @g_elex D B
  have p0017 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B)
      (.classMem D (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem C B) (.classMem D B)) (.classMem C (syn_cvv))
      (.classMem D (syn_cvv)) p0014 p0017
  have p0019 := @g_fdprj1valV x C D dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0020 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
        (.classEq (.cv x) (syn_csn (syn_csn D))))
      p0018 p0019
  have p0021 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))
      (.classEq (.cv x) (syn_csn (syn_csn D))) p0011 p0020
  have p0022 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classEq (.cv x) (syn_csn (syn_csn D))))
      x dv_cache_0008 p0021
  have p0023 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj1))))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classEq (.cv x) (syn_csn (syn_csn D)))))
      p0009 p0022
  have p0024 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classEq (.cv x) (syn_csn (syn_csn D)))
  have p0025 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classEq (.cv x) (syn_csn (syn_csn D))))
        (syn_wa (.classEq (.cv x) (syn_csn (syn_csn D)))
          (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
      (syn_wa (.classMem C B) (.classMem D B)) p0024
  have p0026 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classEq (.cv x) (syn_csn (syn_csn D))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn D)))
        (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))
      x dv_cache_0008 p0025
  have p0027 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classEq (.cv x) (syn_csn (syn_csn D)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn D)))
          (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
      p0023 p0026
  have p0028 := @g_snex (syn_csn D)
  have p0029 := @g_opkeq2 (.cv x) (syn_csn (syn_csn D)) (syn_csn (.cv e))
  have p0030 :=
    @g_eleq1d (.classEq (.cv x) (syn_csn (syn_csn D)))
      (syn_copk (syn_csn (.cv e)) (.cv x))
      (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem) p0029
  have p0031 :=
    @g_ceqsexgv (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem)) x
      (syn_csn (syn_csn D)) (syn_cvv) dv_cache_0009 dv_cache_0010 p0030
  have p0032 := Nominal.mp p0028 p0031
  have p0033 :=
    @g_a1i
      (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn D)))
            (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem)))
      (syn_wa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn D)))
          (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem)) p0027
      p0033
  have p0036 := @g_fdmemvalC B D e
  have p0037 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B)
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem))
        (.classMem D (.cv e)))
      p0015 p0036
  have p0038 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn D))) (syn_cfdmem))
      (.classMem D (.cv e)) p0034 p0037
  have p0039 := (Nominal.classEqRefl (syn_cfddom A B))
  have p0040 :=
    @g_eleq2i (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0039
  have p0041 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0040
  have p0044 :=
    @g_opkelxpk (syn_csn (.cv e)) (syn_copk C D) (syn_cpw1 A) (syn_cxpk B B) p0006 p0007
  have p0045 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)))
        (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A))
          (.classMem (syn_copk C D) (syn_cxpk B B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)))
      (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A))
        (.classMem (syn_copk C D) (syn_cxpk B B)))
      p0041 p0045
  have p0047 := @g_snelpw1 (.cv e) A
  have p0048 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (.cv e) A))
      (syn_wa (.classMem C B) (.classMem D B)) p0047
  have p0056 := @g_opkelxpkg C D B B (syn_cvv) (syn_cvv)
  have p0057 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wb (.classMem (syn_copk C D) (syn_cxpk B B))
        (syn_wa (.classMem C B) (.classMem D B)))
      p0018 p0056
  have p0058 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (.cv e) A)
      (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B))
      p0048 p0057
  have p0059 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A))
        (.classMem (syn_copk C D) (syn_cxpk B B)))
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) p0046 p0058
  have p0060 := @g_iba (syn_wa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
  have p0061 :=
    @g_bicomd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) p0060
  have p0062 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (.cv e) A) p0059 p0061
  have p0063 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
      (.classMem D (.cv e))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (.classMem (.cv e) A) p0038 p0062
  have p0064 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_ccomk (syn_cfdprj1) (syn_cfdmem)))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)))
      (syn_wa (.classMem D (.cv e)) (.classMem (.cv e) A)) p0005 p0063
  have p0065 := @g_ancom (.classMem D (.cv e)) (.classMem (.cv e) A)
  have p0066 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem D (.cv e)) (.classMem (.cv e) A))
        (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))
      (syn_wa (.classMem C B) (.classMem D B)) p0065
  have p0067 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))
      (syn_wa (.classMem D (.cv e)) (.classMem (.cv e) A))
      (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))) p0064 p0066
  exact p0067

@[expose]
noncomputable def g_sep2valJp (C : Class) (D : Class) (e : Var)
    (dv_C_D : Disjoint C.fv D.fv) (_dv_C_e : e ∉ C.fv) (_dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv e) (syn_csep2 C D))
        (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))) :=
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
      ((syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sep2 z C D
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_csep2 C D)
      (.cab z (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
          (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))))
      (.cv e) p0000
  have p0002 := @g_vex e
  have p0003 := @g_eleq2 (.cv z) (.cv e) C
  have p0004 := @g_eleq2 (.cv z) (.cv e) D
  have p0005 :=
    @g_notbid (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e)) p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e))
      (.neg (.classMem D (.cv z))) (.neg (.classMem D (.cv e))) p0003 p0005
  have p0009 :=
    @g_notbid (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e)) p0003
  have p0010 :=
    @g_anbi12d (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e))
      (.neg (.classMem C (.cv z))) (.neg (.classMem C (.cv e))) p0004 p0009
  have p0011 :=
    @g_orbi12d (.classEq (.cv z) (.cv e))
      (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
      (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
      (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))
      (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))) p0006 p0010
  have p0012 :=
    @g_elab
      (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
        (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      z (.cv e) dv_cache_0004 dv_cache_0005 p0002 p0011
  have p0013 :=
    @g_bitri (.classMem (.cv e) (syn_csep2 C D))
      (.classMem (.cv e) (.cab z
          (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
            (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))))
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
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

@[expose]
noncomputable def g_fdsepvalJ (A : Class) (B : Class) (C : Class) (D : Class) (e : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_D : Disjoint B.fv D.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_e : e ∉ C.fv) (dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C B) (.classMem D B))
        (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B))
          (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))) :=
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
      ((syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfdsep A B))
  have p0001 :=
    @g_eleq2i (syn_cfdsep A B) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_elsymdif (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B)
      (syn_cfde1 A B)
  have p0003 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B)))
      (.neg (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))))
      p0001 p0002
  have p0004 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg
          (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
            (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B)))))
      (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_fde0valJp A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0006 :=
    @g_fde1valJp A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0007 :=
    @g_bibi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
      (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))
      (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))) p0005 p0006
  have p0008 :=
    @g_notbid (syn_wa (.classMem C B) (.classMem D B))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B)))
      (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
        (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))
      p0007
  have p0009 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B))
      (.neg (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde1 A B))))
      (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      p0004 p0008
  have p0010 := @g_xordi (.classMem (.cv e) A) (.classMem C (.cv e)) (.classMem D (.cv e))
  have p0011 :=
    @g_bicomi
      (syn_wa (.classMem (.cv e) A) (.neg (syn_wb (.classMem C (.cv e)) (.classMem D (.cv e)))))
      (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      p0010
  have p0012 := @g_xor (.classMem C (.cv e)) (.classMem D (.cv e))
  have p0013 :=
    @g_anbi2i (.neg (syn_wb (.classMem C (.cv e)) (.classMem D (.cv e))))
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      (.classMem (.cv e) A) p0012
  have p0014 :=
    @g_bitri
      (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      (syn_wa (.classMem (.cv e) A) (.neg (syn_wb (.classMem C (.cv e)) (.classMem D (.cv e)))))
      (syn_wa (.classMem (.cv e) A)
        (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
      p0011 p0013
  have p0015 :=
    @g_a1i
      (syn_wb (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
            (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e))))) (syn_wa (.classMem (.cv e) A)
          (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
            (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))))
      (syn_wa (.classMem C B) (.classMem D B)) p0014
  have p0016 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B))
      (.neg (syn_wb (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (syn_wa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      (syn_wa (.classMem (.cv e) A)
        (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
      p0009 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sep2 z C D
      dv_cache_0008 dv_cache_0011 dv_cache_0012
  have p0018 :=
    @g_eleq2i (syn_csep2 C D)
      (.cab z (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
          (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))))
      (.cv e) p0017
  have p0019 := @g_vex e
  have p0020 := @g_eleq2 (.cv z) (.cv e) C
  have p0021 := @g_eleq2 (.cv z) (.cv e) D
  have p0022 :=
    @g_notbid (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e)) p0021
  have p0023 :=
    @g_anbi12d (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e))
      (.neg (.classMem D (.cv z))) (.neg (.classMem D (.cv e))) p0020 p0022
  have p0026 :=
    @g_notbid (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e)) p0020
  have p0027 :=
    @g_anbi12d (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e))
      (.neg (.classMem C (.cv z))) (.neg (.classMem C (.cv e))) p0021 p0026
  have p0028 :=
    @g_orbi12d (.classEq (.cv z) (.cv e))
      (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
      (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
      (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))
      (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))) p0023 p0027
  have p0029 :=
    @g_elab
      (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
        (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      z (.cv e) dv_cache_0013 dv_cache_0014 p0019 p0028
  have p0030 :=
    @g_bitri (.classMem (.cv e) (syn_csep2 C D))
      (.classMem (.cv e) (.cab z
          (syn_wo (syn_wa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
            (syn_wa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))))
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      p0018 p0029
  have p0031 :=
    @g_bicomi (.classMem (.cv e) (syn_csep2 C D))
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      p0030
  have p0032 :=
    @g_anbi2i
      (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      (.classMem (.cv e) (syn_csep2 C D)) (.classMem (.cv e) A) p0031
  have p0033 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv e) A)
          (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
            (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
        (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))
      (syn_wa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B))
      (syn_wa (.classMem (.cv e) A)
        (syn_wo (syn_wa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (syn_wa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) p0016 p0033
  exact p0034

@[expose]
noncomputable def g_strictbr (R : Class) (e : Var) (c : Var) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)))) :=
  by
  have p0000 := @g_brdif (.cv c) (.cv e) R (syn_cid)
  have p0001 := @g_vex e
  have p0002 := @g_ideq (.cv c) (.cv e) p0001
  have p0003 :=
    @g_notbii (syn_wbr (.cv c) (syn_cid) (.cv e)) (.classEq (.cv c) (.cv e)) p0002
  have p0004 := (Nominal.biimpRefl (syn_wne (.cv c) (.cv e)))
  have p0005 :=
    @g_bicomi (syn_wne (.cv c) (.cv e)) (.neg (.classEq (.cv c) (.cv e))) p0004
  have p0006 :=
    @g_bitri (.neg (syn_wbr (.cv c) (syn_cid) (.cv e))) (.neg (.classEq (.cv c) (.cv e)))
      (syn_wne (.cv c) (.cv e)) p0003 p0005
  have p0007 :=
    @g_anbi2i (.neg (syn_wbr (.cv c) (syn_cid) (.cv e))) (syn_wne (.cv c) (.cv e))
      (syn_wbr (.cv c) R (.cv e)) p0006
  have p0008 :=
    @g_bitri (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (.neg (syn_wbr (.cv c) (syn_cid) (.cv e))))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_fdnonminval0J (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv)
    (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv)
    (_dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (_dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (_dv_B_e : e ∉ B.fv)
    (dv_C_D : Disjoint C.fv D.fv) (_dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv)
    (_dv_C_e : e ∉ C.fv) (_dv_D_R : Disjoint D.fv R.fv) (dv_D_c : c ∉ D.fv)
    (_dv_D_e : e ∉ D.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C B) (.classMem D B)) (syn_wb
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
          (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
              (.classMem (.cv c) (syn_csep2 C D)))))) :=
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
  have dv_cache_0011 : c ∉ ((syn_wa (.classMem C B) (.classMem D B))).fv :=
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
  have dv_cache_0012 : x ∉ ((syn_csn (.cv e))).fv :=
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
  have dv_cache_0013 : x ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0014 : x ∉ ((syn_cfdsep A B)).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))).fv :=
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
  have dv_cache_0016 : c ∉ ((syn_cdif R (syn_cid))).fv :=
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
  have dv_cache_0017 : e ∉ ((syn_cdif R (syn_cid))).fv :=
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
  have dv_cache_0018 : x ∉ ((syn_cdif R (syn_cid))).fv :=
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
    c ∉ ((Wff.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))).fv :=
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
  have dv_cache_0023 : x ∉ ((syn_csn (.cv c))).fv :=
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
      ((syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))).fv :=
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
    @g_fdsepvalJ A B C D c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_anbi2d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))
      (syn_wa (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0000
  have p0002 :=
    @g_an12 (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) A)
      (.classMem (.cv c) (syn_csep2 C D))
  have p0003 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (syn_wa (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D))))
        (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      (syn_wa (.classMem C B) (.classMem D B)) p0002
  have p0004 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (syn_wa (.classMem (.cv c) A) (.classMem (.cv c) (syn_csep2 C D))))
      (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (.cv c) (syn_csep2 C D))))
      p0001 p0003
  have p0005 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wa (.classMem (.cv c) A) (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (.cv c) (syn_csep2 C D))))
      c dv_cache_0011 p0004
  have p0006 := (Nominal.classEqRefl (syn_cfdnonmin R A B))
  have p0007 :=
    @g_eleq2i (syn_cfdnonmin R A B)
      (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0006
  have p0008 := @g_snex (.cv e)
  have p0009 := @g_opkex C D
  have p0010 :=
    @g_opkelcok x (syn_csn (.cv e)) (syn_copk C D) (syn_cfdsep A B)
      (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))) dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 p0008 p0009
  have p0011 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid))))))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x))
            (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      p0007 p0010
  have p0013 := @g_vex x
  have p0014 :=
    @g_opkelcnvk (syn_csn (.cv e)) (.cv x) (syn_cfdlift (syn_cdif R (syn_cid))) p0008
      p0013
  have p0015 := @g_biid (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
  have p0016 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv x))
        (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))
      (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid))))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) p0014 p0015
  have p0017 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x))
          (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e)))
          (syn_cfdlift (syn_cdif R (syn_cid))))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      x p0016
  have p0018 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x))
            (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      (syn_wex x (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e)))
            (syn_cfdlift (syn_cdif R (syn_cid))))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      p0011 p0017
  have p0019 :=
    @g_fdliftval1 x (syn_cdif R (syn_cid)) e c dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0021 :=
    @g_anbi12i
      (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift (syn_cdif R (syn_cid))))
      (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) p0019 p0015
  have p0022 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e)))
          (syn_cfdlift (syn_cdif R (syn_cid))))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      x p0021
  have p0023 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wex x (syn_wa (.classMem (syn_copk (.cv x) (syn_csn (.cv e)))
            (syn_cfdlift (syn_cdif R (syn_cid))))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      (syn_wex x (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
              (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      p0018 p0022
  have p0024 :=
    @g_n_19_41v
      (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)) c dv_cache_0022
  have p0025 :=
    @g_bicomi
      (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      p0024
  have p0026 :=
    @g_exbii
      (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      x p0025
  have p0027 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wex x (syn_wa (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
              (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      (syn_wex x (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
              (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))
      p0023 p0026
  have p0028 :=
    @g_excom
      (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      x c
  have p0029 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wex x (syn_wex c (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
              (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))
      (syn_wex c (syn_wex x (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
              (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))
      p0027 p0028
  have p0030 :=
    @g_anass (.classEq (.cv x) (syn_csn (.cv c)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
  have p0031 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
        (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      x p0030
  have p0032 :=
    @g_exbii
      (syn_wex x (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))
      c p0031
  have p0033 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wex c (syn_wex x (syn_wa (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
              (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))
      (syn_wex c (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
              (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))))
      p0029 p0032
  have p0034 := @g_snex (.cv c)
  have p0035 := @g_opkeq1 (.cv x) (syn_csn (.cv c)) (syn_copk C D)
  have p0036 :=
    @g_eleq1d (.classEq (.cv x) (syn_csn (.cv c))) (syn_copk (.cv x) (syn_copk C D))
      (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B) p0035
  have p0037 :=
    @g_anbi2d (.classEq (.cv x) (syn_csn (.cv c)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))
      (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0036
  have p0038 :=
    @g_ceqsexv
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))
      x (syn_csn (.cv c)) dv_cache_0023 dv_cache_0024 p0034 p0037
  have p0039 :=
    @g_exbii
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B)))))
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B)))
      c p0038
  have p0040 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wex c (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
              (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdsep A B))))))
      (syn_wex c (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))))
      p0033 p0039
  have p0041 :=
    (Nominal.biimpRefl (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (.cv c) (syn_csep2 C D)))))
  have p0042 :=
    @g_n_3bitr4g (syn_wa (.classMem C B) (.classMem D B))
      (syn_wex c (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (syn_copk (syn_csn (.cv c)) (syn_copk C D)) (syn_cfdsep A B))))
      (syn_wex c (syn_wa (.classMem (.cv c) A)
          (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (.cv c) (syn_csep2 C D))))
      p0005 p0040 p0041
  exact p0042

@[expose]
noncomputable def g_kqrelex (A : Class)
    (hyp_kqrelex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ckqrel A) (syn_cvv)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_kqrel x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_setconslem4 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_eqtr4i (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))
      (syn_cuni1 (syn_cuni1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
                      (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A)))
      p0000 p0001
  have p0003 := @g_vvex
  have p0005 := @g_xpkex (syn_cvv) (syn_cvv) p0003 p0003
  have p0007 := @g_xpkex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv) p0005 p0003
  have p0008 := @g_setconslem5
  have p0009 :=
    @g_cnvkex
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
      p0008
  have p0010 :=
    @g_inex (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv))
      (syn_ccnvk (syn_ccompl (syn_cimak
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
      p0007 p0009
  have p0011 :=
    @g_imakex
      (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl
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
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      A p0010 hyp_kqrelex_1
  have p0012 :=
    @g_uni1ex
      (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
                  (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A)
      p0011
  have p0013 :=
    @g_uni1ex
      (syn_cuni1 (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv))
            (syn_ccnvk (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
                      (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A))
      p0012
  have p0014 :=
    @g_eqeltri (syn_ckqrel A)
      (syn_cuni1 (syn_cuni1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
                      (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) A)))
      (syn_cvv) p0002 p0013
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

@[expose]
noncomputable def g_kqrelbr (A : Class) (B : Class) (C : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (hyp_kqrelbr_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_kqrelbr_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop B C) (syn_ckqrel A)) (.classMem (syn_copk B C) A)) :=
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
  have dv_cache_0008 : x ∉ ((Wff.classMem (syn_copk B C) A)).fv :=
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
  have dv_cache_0009 : y ∉ ((Wff.classMem (syn_copk B C) A)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_kqrel x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))
      (syn_cop B C) p0000
  have p0002 := @g_opkeq1 (.cv x) B (.cv y)
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_copk (.cv x) (.cv y)) (syn_copk B (.cv y)) A p0002
  have p0004 := @g_opkeq2 (.cv y) C B
  have p0005 := @g_eleq1d (.classEq (.cv y) C) (syn_copk B (.cv y)) (syn_copk B C) A p0004
  have p0006 :=
    @g_opelopab (.classMem (syn_copk (.cv x) (.cv y)) A)
      (.classMem (syn_copk B (.cv y)) A) (.classMem (syn_copk B C) A) x y B C
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0003 hyp_kqrelbr_1 hyp_kqrelbr_2 p0003 p0005
  have p0007 :=
    @g_bitri (.classMem (syn_cop B C) (syn_ckqrel A))
      (.classMem (syn_cop B C) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A)))
      (.classMem (syn_copk B C) A) p0001 p0006
  exact p0007

@[expose]
noncomputable def g_fdminvalpex (A : Class) (B : Class) (C : Class) (R : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (_dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdminvalpex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdminvalpex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdminvalpex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdminvalp R A B C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdminvalp R A B C))
  have p0001 := @g_fdminsepex A B R hyp_fdminvalpex_1 hyp_fdminvalpex_2 hyp_fdminvalpex_3
  have p0002 := @g_cnvkex (syn_cfdminsep R A B) p0001
  have p0003 := @g_snex C
  have p0004 := @g_imakex (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C) p0002 p0003
  have p0005 := @g_uni1ex (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) p0004
  have p0006 :=
    @g_eqeltri (syn_cfdminvalp R A B C)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cvv)
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_fdminvalpbr (z : Var) (A : Class) (B : Class) (C : Class) (R : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_A_z : z ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (_dv_B_z : z ∉ B.fv) (_dv_C_R : Disjoint C.fv R.fv)
    (_dv_C_z : z ∉ C.fv) (_dv_R_z : z ∉ R.fv)
    (hyp_fdminvalpbr_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cfdminvalp R A B C))
        (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdminvalp R A B C))
  have p0001 :=
    @g_eleq2i (syn_cfdminvalp R A B C)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (.cv z) p0000
  have p0002 := @g_vex z
  have p0003 :=
    @g_eluni1 (.cv z) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) p0002
  have p0004 :=
    @g_bitri (.classMem (.cv z) (syn_cfdminvalp R A B C))
      (.classMem (.cv z) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))))
      (.classMem (syn_csn (.cv z)) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))
      p0001 p0003
  have p0005 := @g_snex (.cv z)
  have p0006 :=
    @g_elimaksn (syn_ccnvk (syn_cfdminsep R A B)) C (syn_csn (.cv z)) hyp_fdminvalpbr_1
      p0005
  have p0007 :=
    @g_bitri (.classMem (.cv z) (syn_cfdminvalp R A B C))
      (.classMem (syn_csn (.cv z)) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))
      (.classMem (syn_copk C (syn_csn (.cv z))) (syn_ccnvk (syn_cfdminsep R A B))) p0004
      p0006
  have p0009 :=
    @g_opkelcnvk C (syn_csn (.cv z)) (syn_cfdminsep R A B) hyp_fdminvalpbr_1 p0005
  have p0010 :=
    @g_bitri (.classMem (.cv z) (syn_cfdminvalp R A B C))
      (.classMem (syn_copk C (syn_csn (.cv z))) (syn_ccnvk (syn_cfdminsep R A B)))
      (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B)) p0007 p0009
  exact p0010

@[expose]
noncomputable def g_fdminqex (A : Class) (B : Class) (R : Class)
    (hyp_fdminqex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdminqex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdminqex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdminq R A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdminq R A B))
  have p0001 := @g_fdminsepex A B R hyp_fdminqex_1 hyp_fdminqex_2 hyp_fdminqex_3
  have p0002 := @g_kqrelex (syn_cfdminsep R A B) p0001
  have p0003 :=
    @g_eqeltri (syn_cfdminq R A B) (syn_ckqrel (syn_cfdminsep R A B)) (syn_cvv) p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_fdpivmap2ex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdpivmap2 R A B) (syn_cvv)) :=
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
  have dv_cache_0007 : Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv from (by
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
  have dv_cache_0008 : Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv from (by
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
  have dv_cache_0009 : Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv from (by
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
  have dv_cache_0017 : p ∉ ((syn_cxpk B B)).fv :=
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
  have dv_cache_0018 : p ∉ ((syn_cfdminq R A B)).fv :=
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
  have dv_cache_0019 : z ∉ ((syn_cfdminq R A B)).fv :=
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
  have dv_cache_0020 : z ∉ ((syn_cfdminvalp R A B (.cv p))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := (Nominal.classEqRefl (syn_cfdminq R A B))
  have p0002 :=
    @g_eleq2i (syn_cfdminq R A B) (syn_ckqrel (syn_cfdminsep R A B))
      (syn_cop (syn_csn (.cv z)) (.cv p)) p0001
  have p0003 := @g_snex (.cv z)
  have p0004 := @g_vex p
  have p0005 :=
    @g_kqrelbr (syn_cfdminsep R A B) (syn_csn (.cv z)) (.cv p) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_ckqrel (syn_cfdminsep R A B)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0002 p0005
  have p0008 :=
    @g_fdminvalpbr z A B (.cv p) R dv_cache_0001 dv_cache_0010 dv_cache_0002 dv_cache_0011
      dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      p0004
  have p0009 :=
    @g_bicomi (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0008
  have p0010 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B))
      (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p))) p0006 p0009
  have p0011 :=
    @g_releqmpt p z (syn_cxpk B B) (syn_cfdminq R A B) (syn_cfdminvalp R A B (.cv p))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0010
  have p0012 :=
    @g_eqtr4i (syn_cfdpivmap2 R A B)
      (syn_cmpt p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)))
      (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B)))
              (syn_c1c)))))
      p0000 p0011
  have p0013 := @g_xpkex B B hyp_fdpivmap2ex_3 hyp_fdpivmap2ex_3
  have p0014 := @g_fdminqex A B R hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0015 := @g_mptexlem (syn_cxpk B B) (syn_cfdminq R A B) p0013 p0014
  have p0016 :=
    @g_eqeltri (syn_cfdpivmap2 R A B)
      (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B)))
              (syn_c1c)))))
      (syn_cvv) p0012 p0015
  exact p0016

@[expose]
noncomputable def g_fdpivmap2fn (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cfdpivmap2 R A B) (syn_cxpk B B)) :=
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
  have dv_cache_0010 : p ∉ ((syn_cxpk B B)).fv :=
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
    @g_fdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p
      dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_fnmpti p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)) (syn_cfdpivmap2 R A B)
      dv_cache_0010 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fdpivrange2ex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdpivrange2 R A B) (syn_cvv)) :=
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
  have dv_cache_0007 : Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((syn_cfdminsep R A B)).fv ((syn_csn (.cv z))).fv from (by
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
  have dv_cache_0008 : Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((syn_cfdminsep R A B)).fv ((Class.cv p)).fv from (by
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
  have dv_cache_0009 : Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((syn_csn (.cv z))).fv ((Class.cv p)).fv from (by
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
  have dv_cache_0017 : p ∉ ((syn_cxpk B B)).fv :=
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
  have dv_cache_0018 : p ∉ ((syn_cfdminq R A B)).fv :=
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
  have dv_cache_0019 : z ∉ ((syn_cfdminq R A B)).fv :=
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
  have dv_cache_0020 : z ∉ ((syn_cfdminvalp R A B (.cv p))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfdpivrange2 R A B))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 := (Nominal.classEqRefl (syn_cfdminq R A B))
  have p0003 :=
    @g_eleq2i (syn_cfdminq R A B) (syn_ckqrel (syn_cfdminsep R A B))
      (syn_cop (syn_csn (.cv z)) (.cv p)) p0002
  have p0004 := @g_snex (.cv z)
  have p0005 := @g_vex p
  have p0006 :=
    @g_kqrelbr (syn_cfdminsep R A B) (syn_csn (.cv z)) (.cv p) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0004 p0005
  have p0007 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_ckqrel (syn_cfdminsep R A B)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0003 p0006
  have p0009 :=
    @g_fdminvalpbr z A B (.cv p) R dv_cache_0001 dv_cache_0010 dv_cache_0002 dv_cache_0011
      dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      p0005
  have p0010 :=
    @g_bicomi (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B)) p0009
  have p0011 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (.cv p)) (syn_cfdminq R A B))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv p)) (syn_cfdminsep R A B))
      (.classMem (.cv z) (syn_cfdminvalp R A B (.cv p))) p0007 p0010
  have p0012 :=
    @g_releqmpt p z (syn_cxpk B B) (syn_cfdminq R A B) (syn_cfdminvalp R A B (.cv p))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0011
  have p0013 :=
    @g_eqtr4i (syn_cfdpivmap2 R A B)
      (syn_cmpt p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)))
      (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B)))
              (syn_c1c)))))
      p0001 p0012
  have p0014 := @g_xpkex B B hyp_fdpivmap2ex_3 hyp_fdpivmap2ex_3
  have p0015 := @g_fdminqex A B R hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0016 := @g_mptexlem (syn_cxpk B B) (syn_cfdminq R A B) p0014 p0015
  have p0017 :=
    @g_eqeltri (syn_cfdpivmap2 R A B)
      (syn_cin (syn_cxp (syn_cxpk B B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdminq R A B)))
              (syn_c1c)))))
      (syn_cvv) p0013 p0016
  have p0018 := @g_rnex (syn_cfdpivmap2 R A B) p0017
  have p0019 :=
    @g_eqeltri (syn_cfdpivrange2 R A B) (syn_crn (syn_cfdpivmap2 R A B)) (syn_cvv) p0000
      p0018
  exact p0019

@[expose]
noncomputable def g_fdpivmap2onto (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) :=
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
  have dv_cache_0010 : p ∉ ((syn_cxpk B B)).fv :=
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
    @g_fdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p
      dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_fnmpti p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)) (syn_cfdpivmap2 R A B)
      dv_cache_0010 p0000 p0001
  have p0003 := @g_dffn4 (syn_cxpk B B) (syn_cfdpivmap2 R A B)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cfdpivmap2 R A B) (syn_cxpk B B))
      (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_crn (syn_cfdpivmap2 R A B)))
      p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cfdpivrange2 R A B))
  have p0006 := @g_eqcomi (syn_cfdpivrange2 R A B) (syn_crn (syn_cfdpivmap2 R A B)) p0005
  have p0007 :=
    @g_foeq3 (syn_crn (syn_cfdpivmap2 R A B)) (syn_cfdpivrange2 R A B) (syn_cxpk B B)
      (syn_cfdpivmap2 R A B)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbi
      (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_crn (syn_cfdpivmap2 R A B)))
      (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) p0004 p0008
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

@[expose]
noncomputable def g_fdpivmap2val (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv)
    (hyp_fdpivmap2val_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivmap2val_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivmap2val_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv p) (syn_cxpk B B))
        (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) (syn_cfdminvalp R A B (.cv p)))) :=
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
  have dv_cache_0010 : p ∉ ((syn_cxpk B B)).fv :=
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
  have p0000 := @g_id (.classMem (.cv p) (syn_cxpk B B))
  have p0001 :=
    @g_fdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdpivmap2val_1 hyp_fdpivmap2val_2 hyp_fdpivmap2val_3
  have p0002 :=
    @g_a1i (.classMem (syn_cfdminvalp R A B (.cv p)) (syn_cvv))
      (.classMem (.cv p) (syn_cxpk B B)) p0001
  have p0003 :=
    @g_jca (.classMem (.cv p) (syn_cxpk B B)) (.classMem (.cv p) (syn_cxpk B B))
      (.classMem (syn_cfdminvalp R A B (.cv p)) (syn_cvv)) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdpivmap2 A B R p
      dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0005 :=
    @g_fvmpt2 p (syn_cxpk B B) (syn_cfdminvalp R A B (.cv p)) (syn_cvv)
      (syn_cfdpivmap2 R A B) dv_cache_0010 p0004
  have p0006 :=
    @g_syl (.classMem (.cv p) (syn_cxpk B B))
      (syn_wa (.classMem (.cv p) (syn_cxpk B B))
        (.classMem (syn_cfdminvalp R A B (.cv p)) (syn_cvv)))
      (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) (syn_cfdminvalp R A B (.cv p)))
      p0003 p0005
  exact p0006

@[expose]
noncomputable def g_fdpivrange2br (A : Class) (B : Class) (C : Class) (R : Class)
    (p : Var) (dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (_dv_C_R : Disjoint C.fv R.fv)
    (dv_C_p : p ∉ C.fv) (dv_R_p : p ∉ R.fv)
    (hyp_fdpivrange2br_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivrange2br_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivrange2br_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_cfdpivrange2 R A B))
        (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) C))) :=
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
  have dv_cache_0004 : p ∉ ((syn_cxpk B B)).fv :=
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
  have dv_cache_0006 : p ∉ ((syn_cfdpivmap2 R A B)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfdpivrange2 R A B))
  have p0001 :=
    @g_eleq2i (syn_cfdpivrange2 R A B) (syn_crn (syn_cfdpivmap2 R A B)) C p0000
  have p0002 :=
    @g_fdpivmap2fn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdpivrange2br_1
      hyp_fdpivrange2br_2 hyp_fdpivrange2br_3
  have p0003 :=
    @g_fvelrnb p (syn_cxpk B B) C (syn_cfdpivmap2 R A B) dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_fdpivmap2val A B R p dv_cache_0001 dv_cache_0002 dv_cache_0007 dv_cache_0003
      dv_cache_0008 dv_cache_0009 hyp_fdpivrange2br_1 hyp_fdpivrange2br_2
      hyp_fdpivrange2br_3
  have p0006 :=
    @g_eqeq1d (.classMem (.cv p) (syn_cxpk B B)) (syn_cfv (syn_cfdpivmap2 R A B) (.cv p))
      (syn_cfdminvalp R A B (.cv p)) C p0005
  have p0007 :=
    @g_rexbiia (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) C)
      (.classEq (syn_cfdminvalp R A B (.cv p)) C) p (syn_cxpk B B) p0006
  have p0008 :=
    @g_bitri (.classMem C (syn_crn (syn_cfdpivmap2 R A B)))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfv (syn_cfdpivmap2 R A B) (.cv p)) C))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) C)) p0004 p0007
  have p0009 :=
    @g_bitri (.classMem C (syn_cfdpivrange2 R A B))
      (.classMem C (syn_crn (syn_cfdpivmap2 R A B)))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) C)) p0001 p0008
  exact p0009

@[expose]
noncomputable def g_fdminvalpss (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdminvalpss_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wss (syn_cfdminvalp R A B C) A) :=
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
  have dv_cache_0011 : z ∉ ((syn_cfdminvalp R A B C)).fv :=
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
    @g_fdminvalpbr z A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      hyp_fdminvalpss_1
  have p0001 :=
    @g_biimpi (.classMem (.cv z) (syn_cfdminvalp R A B C))
      (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B)) p0000
  have p0002 := (Nominal.classEqRefl (syn_cfdminsep R A B))
  have p0003 := @g_difss (syn_cfdsep A B) (syn_cfdnonmin R A B)
  have p0004 :=
    @g_eqsstri (syn_cfdminsep R A B) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B))
      (syn_cfdsep A B) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cfdsep A B))
  have p0006 := (Nominal.classEqRefl (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B)))
  have p0007 :=
    @g_eqtri (syn_cfdsep A B) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B))
      (syn_cun (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B))
        (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B)))
      p0005 p0006
  have p0008 := @g_difss (syn_cfde0 A B) (syn_cfde1 A B)
  have p0009 := (Nominal.classEqRefl (syn_cfde0 A B))
  have p0010 := @g_inss2 (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)
  have p0011 :=
    @g_eqsstri (syn_cfde0 A B)
      (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)) (syn_cfddom A B)
      p0009 p0010
  have p0012 :=
    @g_sstri (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cfde0 A B) (syn_cfddom A B)
      p0008 p0011
  have p0013 := @g_difss (syn_cfde1 A B) (syn_cfde0 A B)
  have p0014 := (Nominal.classEqRefl (syn_cfde1 A B))
  have p0015 := @g_inss2 (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)
  have p0016 :=
    @g_eqsstri (syn_cfde1 A B)
      (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)) (syn_cfddom A B)
      p0014 p0015
  have p0017 :=
    @g_sstri (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B)) (syn_cfde1 A B) (syn_cfddom A B)
      p0013 p0016
  have p0018 :=
    @g_unssi (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B))
      (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B)) (syn_cfddom A B) p0012 p0017
  have p0019 :=
    @g_eqsstri (syn_cfdsep A B)
      (syn_cun (syn_cdif (syn_cfde0 A B) (syn_cfde1 A B))
        (syn_cdif (syn_cfde1 A B) (syn_cfde0 A B)))
      (syn_cfddom A B) p0007 p0018
  have p0020 :=
    @g_sstri (syn_cfdminsep R A B) (syn_cfdsep A B) (syn_cfddom A B) p0004 p0019
  have p0021 :=
    @g_sseli (syn_cfdminsep R A B) (syn_cfddom A B) (syn_copk (syn_csn (.cv z)) C) p0020
  have p0022 :=
    @g_syl (.classMem (.cv z) (syn_cfdminvalp R A B C))
      (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfdminsep R A B))
      (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B)) p0001 p0021
  have p0023 := (Nominal.classEqRefl (syn_cfddom A B))
  have p0024 :=
    @g_eleq2i (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))
      (syn_copk (syn_csn (.cv z)) C) p0023
  have p0025 := @g_snex (.cv z)
  have p0026 :=
    @g_opkelxpk (syn_csn (.cv z)) C (syn_cpw1 A) (syn_cxpk B B) p0025 hyp_fdminvalpss_1
  have p0027 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B))
      (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)))
      (syn_wa (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem C (syn_cxpk B B)))
      p0024 p0026
  have p0028 :=
    @g_simplbi (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem C (syn_cxpk B B)) p0027
  have p0029 := @g_snelpw1 (.cv z) A
  have p0030 :=
    @g_biimpi (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem (.cv z) A) p0029
  have p0031 :=
    @g_n_3syl (.classMem (.cv z) (syn_cfdminvalp R A B C))
      (.classMem (syn_copk (syn_csn (.cv z)) C) (syn_cfddom A B))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 A)) (.classMem (.cv z) A) p0022 p0028 p0030
  have p0032 := @g_ssriv z (syn_cfdminvalp R A B C) A dv_cache_0011 dv_cache_0004 p0031
  exact p0032

@[expose]
noncomputable def g_elfpiv (A : Class) (B : Class) (C : Class) (R : Class) (e : Var)
    (c : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (_dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv)
    (_dv_B_e : e ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv)
    (_dv_C_e : e ∉ C.fv) (dv_R_c : c ∉ R.fv) (_dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv e) (syn_cfpiv R A B C))
        (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 B C))) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))) :=
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
      ((syn_wa (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))).fv :=
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
  have p0000 := @g_id (.classEq (.cv b) (.cv e))
  have p0001 := @g_eleq1d (.classEq (.cv b) (.cv e)) (.cv b) (.cv e) (syn_csep2 B C) p0000
  have p0003 := @g_breq1d (.classEq (.cv b) (.cv e)) (.cv b) (.cv e) (.cv c) R p0000
  have p0004 :=
    @g_imbi2d (.classEq (.cv b) (.cv e)) (syn_wbr (.cv b) R (.cv c))
      (syn_wbr (.cv e) R (.cv c)) (.classMem (.cv c) (syn_csep2 B C)) p0003
  have p0005 :=
    @g_ralbidv (.classEq (.cv b) (.cv e))
      (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c)))
      (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))) c A
      dv_cache_0001 p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv b) (.cv e)) (.classMem (.cv b) (syn_csep2 B C))
      (.classMem (.cv e) (syn_csep2 B C))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c))))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))))
      p0001 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fpiv A B C R b c
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0008 :=
    @g_elrab2
      (syn_wa (.classMem (.cv b) (syn_csep2 B C)) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv b) R (.cv c)))))
      (syn_wa (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))
      b (.cv e) A (syn_cfpiv R A B C) dv_cache_0017 dv_cache_0005 dv_cache_0018 p0006
      p0007
  have p0009 :=
    @g_anass (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 B C))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))))
  have p0010 :=
    @g_bitr4i (.classMem (.cv e) (syn_cfpiv R A B C))
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem (.cv e) (syn_csep2 B C)) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c))))))
      (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 B C))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 B C)) (syn_wbr (.cv e) R (.cv c)))))
      p0008 p0009
  exact p0010

@[expose]
noncomputable def g_fdminsepval0J (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv)
    (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (dv_B_e : e ∉ B.fv)
    (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv)
    (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv) (dv_D_c : c ∉ D.fv)
    (dv_D_e : e ∉ D.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C B) (.classMem D B)) (syn_wb
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
          (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg
              (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
                  (.classMem (.cv c) (syn_csep2 C D)))))))) :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfdminsep R A B))
  have p0001 :=
    @g_eleq2i (syn_cfdminsep R A B) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_eldif (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)
      (syn_cfdnonmin R A B)
  have p0003 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))))
      p0001 p0002
  have p0004 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
        (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg
            (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)))))
      (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_fdsepvalJ A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0006 :=
    @g_fdnonminval0J A B C D R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0011
      dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0013 dv_cache_0014
      dv_cache_0007 dv_cache_0008 dv_cache_0015 dv_cache_0016 dv_cache_0009 dv_cache_0017
      dv_cache_0018 dv_cache_0010 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0007 :=
    @g_notbid (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))
      (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (.cv c) (syn_csep2 C D))))
      p0006
  have p0008 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B))
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
      (.neg (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B)))
      (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      p0005 p0007
  have p0009 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdsep A B)) (.neg
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdnonmin R A B))))
      (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg
          (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
              (.classMem (.cv c) (syn_csep2 C D))))))
      p0004 p0008
  exact p0009

@[expose]
noncomputable def g_wppwepo (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cpartial) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cfound) A) p0003
  have p0005 := @g_sopc A R
  have p0006 :=
    @g_simplbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A)
      (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cpartial) A) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_wppweref (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cref) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cfound) A) p0003
  have p0005 := @g_sopc A R
  have p0006 :=
    @g_simplbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A)
      (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cpartial) A) p0004 p0006
  have p0008 := @g_porta A R
  have p0009 :=
    @g_simp1bi (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A)
      (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) p0008
  have p0010 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A)
      p0007 p0009
  exact p0010

@[expose]
noncomputable def g_wppweconnex (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cconnex) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cfound) A) p0003
  have p0005 := @g_sopc A R
  have p0006 :=
    @g_simprbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A)
      (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cconnex) A)
      p0004 p0006
  exact p0007

@[expose]
noncomputable def g_wppweantisym (A : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cantisym) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0001 p0002
  have p0004 :=
    @g_simplbi (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cfound) A) p0003
  have p0005 := @g_sopc A R
  have p0006 :=
    @g_simplbi (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cpartial) A)
      (syn_wbr R (syn_cconnex) A) p0005
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cstrict) A)
      (syn_wbr R (syn_cpartial) A) p0004 p0006
  have p0008 := @g_porta A R
  have p0009 :=
    @g_simp3bi (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cref) A)
      (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) p0008
  have p0010 :=
    @g_syl (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cpartial) A)
      (syn_wbr R (syn_cantisym) A) p0007 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end
