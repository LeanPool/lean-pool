/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part065`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppstopgammafixedhwdndv (x : Var) (y : Var) (C : Class) (F : Class)
    (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_p_x : p ≠ x)
    (_dv_p_y : p ≠ y) (_dv_x_y : x ≠ y)
    (hyp_wppstopgammafixedhwdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopgammafixedhwdndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammafixedhwdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammafixedhwdndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C))
    (hyp_wppstopgammafixedhwdndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppstopgammafixedhwdndv_6 : Nominal.NPrf (syn_wral x (syn_cdm (syn_cwppstopstep F C))
          (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))))) :
    Nominal.NPrf
      (.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa
          (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
          (.classEq (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C))
            (syn_cwppgamma (syn_cwppstopstep F C) C)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ C.fv ∪ F.fv ∪ ({ p } : Finset Var)
  let r : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let m : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_p : r ≠ p := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_r : p ≠ r := Ne.symm fresh_r_ne_p
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_y : n ≠ y := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_n : y ≠ n := Ne.symm fresh_n_ne_y
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_n : r ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have dv_cache_0001 : r ∉ ((syn_chwcards (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : p ≠ r := by
    clear dv_cache_0001
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0003 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0004 : r ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_p, dv_F_p, or_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_x, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_p,
          dv_F_p, or_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_x,
          dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0012 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0013 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0015 : k ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0016 : k ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0017 : k ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_k_not_C,
          not_false_eq_true])
  have dv_cache_0018 :
    p ∉
      ((syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
              (syn_chwcards (syn_cvv)))
            (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
          (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_C_p,
          dv_F_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0020 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa
                (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (.classMem
            (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)
            (syn_cdm (syn_cwppstopstep F C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, dv_C_p,
          dv_F_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : n ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_n_not_C,
          not_false_eq_true])
  have dv_cache_0022 :
    n ∉
      ((syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
              (syn_chwcards (syn_cvv)))
            (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
          (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0023 : n ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_n_not_C, fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0024 :
    y ∉
      ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_n, dv_C_y, dv_F_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_cdm (syn_cwppstopstep F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_y, dv_F_y, or_false, not_false_eq_true])
  have dv_cache_0026 :
    y ∉
      ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                      (syn_chwcards (syn_cvv)))
                    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                  (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                        (syn_chwcards (syn_cvv)))
                      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                    (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_y, fresh_y_ne_n, dv_F_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0027 : m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
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
  have dv_cache_0028 : m ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0029 :
    m ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                    (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
            (syn_cplc (.cv n) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 :
    n ∉
      ((syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                      (syn_chwcards (syn_cvv)))
                    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                  (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 :
    n ∉
      ((syn_wral y (syn_cdm (syn_cwppstopstep F C))
          (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F,
          fresh_n_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 : n ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0033 :
    n ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                    (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0034 :
    m ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                    (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 :
    r ∉
      ((Wff.classEq (.cv p) (syn_cif (syn_wa
              (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                (syn_chwcards (syn_cvv)))
              (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
            (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_p, fresh_r_not_C, fresh_r_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa
                (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C)
          (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                    (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                        (syn_chwcards (syn_cvv)))
                      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                    (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r))
              (syn_cncs))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_p, dv_F_p, fresh_p_ne_r,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0037 : r ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_n, not_false_eq_true])
  have dv_cache_0038 : r ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0039 :
    r ∉
      ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
                    (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))
          (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_C, fresh_r_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0040 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_C, not_false_eq_true])
  have dv_cache_0041 : k ∉ ((syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0042 : k ∉ ((syn_cwppcand (syn_cwppstopstep F C) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0043 :
    k ∉
      ((syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec)
          (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0044 :
    p ∉
      ((syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
            (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_C_p,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0045 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (.classMem
            (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)
            (syn_cdm (syn_cwppstopstep F C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_p, dv_F_p, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0046 :
    n ∉
      ((syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
            (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_n_not_C, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0047 :
    y ∉
      ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
              (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_n, dv_C_y, dv_F_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0048 :
    y ∉
      ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                    (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv
                (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                    (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                      (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_y, fresh_y_ne_n, dv_F_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0049 :
    m ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
            (syn_cplc (.cv n) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0050 :
    n ∉
      ((syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                    (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0051 :
    n ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0052 :
    m ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0053 :
    r ∉
      ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
              (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_p, fresh_r_not_C, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0054 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C)
          (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                    (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                      (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r))
              (syn_cncs))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_p, fresh_p_ne_r, dv_F_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0055 :
    r ∉
      ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))
          (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_C, fresh_r_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0056 :
    k ∉ ((syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0057 :
    p ∉
      ((syn_cif (syn_wa
            (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
            (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
          (syn_cwppgamma (syn_cwppstopstep F C) C) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_C_p,
          dv_F_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0058 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (.classMem (syn_cif
              (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) C) C)
            (syn_cdm (syn_cwppstopstep F C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, dv_C_p,
          dv_F_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0059 :
    n ∉
      ((syn_cif (syn_wa
            (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
            (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
          (syn_cwppgamma (syn_cwppstopstep F C) C) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0060 :
    y ∉
      ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_n, dv_C_y, dv_F_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0061 :
    y ∉
      ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                      (syn_chwcards (syn_cvv)))
                    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr C (syn_clec)
            (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif
                    (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                        (syn_chwcards (syn_cvv)))
                      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_y, fresh_y_ne_n, dv_F_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0062 :
    m ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_cplc (.cv n) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0063 :
    n ∉
      ((syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C)
                (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                      (syn_chwcards (syn_cvv)))
                    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                  (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0064 :
    n ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0065 :
    m ∉
      ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0066 :
    r ∉
      ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                (syn_chwcards (syn_cvv)))
              (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
            (syn_cwppgamma (syn_cwppstopstep F C) C) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_p, fresh_r_not_C, fresh_r_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0067 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                  (syn_chwcards (syn_cvv)))
                (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
              (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wral r (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
                        (syn_chwcards (syn_cvv)))
                      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_p, dv_F_p, fresh_p_ne_r,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0068 :
    r ∉
      ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa
                  (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
                  (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
                (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_C, fresh_r_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0069 : k ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0070 : k ∉ ((syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0071 :
    k ∉
      ((syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec)
          (syn_cwppgamma (syn_cwppstopstep F C) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))
  let syntaxFormula0001 : Wff := (syn_wral p (syn_chwcards (syn_cvv)) syntaxFormula0000)
  let syntaxFormula0002 : Wff := (.imp (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0000)
  let syntaxFormula0003 : Wff :=
    (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
  let syntaxFormula0004 : Wff :=
    (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
  let syntaxFormula0005 : Wff := (syn_wa syntaxFormula0004 (.classMem (.cv r) (syn_cnnc)))
  let syntaxFormula0006 : Wff :=
    (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
      (syn_cdm (syn_cwppstopstep F C)))
  let syntaxFormula0007 : Wff :=
    (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
      (syn_chwcards (syn_cvv)))
  let syntaxFormula0008 : Wff :=
    (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))
  let syntaxFormula0009 : Wff := (syn_wral r (syn_cnnc) syntaxFormula0008)
  let syntaxFormula0010 : Wff := (.imp (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0009)
  let syntaxFormula0011 : Wff := (.imp syntaxFormula0009 syntaxFormula0010)
  let syntaxFormula0012 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C))
  let syntaxFormula0013 : Wff :=
    (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C)
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  let syntaxFormula0014 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0015 : Wff :=
    (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  let syntaxFormula0016 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv)))
  let syntaxFormula0017 : Wff :=
    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  let syntaxFormula0018 : Wff := (syn_wa syntaxFormula0016 syntaxFormula0017)
  let syntaxFormula0019 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0020 : Wff := (syn_wa syntaxFormula0018 syntaxFormula0019)
  let syntaxFormula0021 : Wff :=
    (syn_wa syntaxFormula0016
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
  let syntaxClass0022 : Class :=
    (syn_cif syntaxFormula0021 (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)
  let syntaxFormula0023 : Wff := (syn_wbr syntaxClass0022 (syn_clec) C)
  let syntaxFormula0024 : Wff := (.neg syntaxFormula0021)
  let syntaxFormula0025 : Wff := (syn_wa syn_wtru syntaxFormula0021)
  let syntaxFormula0026 : Wff := (syn_wa syn_wtru syntaxFormula0024)
  let syntaxFormula0027 : Wff :=
    (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))
  let syntaxFormula0028 : Wff := (.classMem syntaxClass0022 (syn_chwcards (syn_cvv)))
  let syntaxFormula0029 : Wff := (syn_wral p (syn_chwcards (syn_cvv)) syntaxFormula0027)
  let syntaxFormula0030 : Wff := (.classEq (.cv p) syntaxClass0022)
  let syntaxFormula0031 : Wff :=
    (.classMem syntaxClass0022 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxClass0032 : Class := (syn_cfrec (syn_cwppstopstep F C) syntaxClass0022)
  let syntaxClass0033 : Class := (syn_cfv syntaxClass0032 (.cv n))
  let syntaxFormula0034 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0033)
  let syntaxFormula0035 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0034)
  let syntaxFormula0036 : Wff :=
    (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0031
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
  let syntaxFormula0037 : Wff := (syn_wa syntaxFormula0036 (.classMem (.cv n) (syn_cnnc)))
  let syntaxFormula0038 : Wff :=
    (.classMem syntaxClass0033 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxFormula0039 : Wff :=
    (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))
  let syntaxFormula0040 : Wff :=
    (syn_wral y (syn_cdm (syn_cwppstopstep F C)) syntaxFormula0039)
  let syntaxFormula0041 : Wff := (syn_wa syntaxFormula0038 syntaxFormula0040)
  let syntaxFormula0042 : Wff := (.classEq (.cv y) syntaxClass0033)
  let syntaxClass0043 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0033)
  let syntaxFormula0044 : Wff := (syn_wbr C (syn_clec) syntaxClass0043)
  let syntaxFormula0045 : Wff := (.imp syntaxFormula0034 syntaxFormula0044)
  let syntaxClass0046 : Class := (syn_cfv syntaxClass0032 (syn_cplc (.cv n) (syn_c1c)))
  let syntaxFormula0047 : Wff := (syn_wbr C (syn_clec) syntaxClass0046)
  let syntaxFormula0048 : Wff :=
    (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0047)
  let syntaxClass0049 : Class := (syn_cfv syntaxClass0032 (.cv m))
  let syntaxFormula0050 : Wff := (syn_wbr C (syn_clec) syntaxClass0049)
  let syntaxFormula0051 : Wff := (syn_wrex m (syn_cnnc) syntaxFormula0050)
  let syntaxFormula0052 : Wff := (syn_wbr C (syn_clec) syntaxClass0033)
  let syntaxFormula0053 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0052)
  let syntaxFormula0054 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0034)
  let syntaxFormula0055 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0052)
  let syntaxFormula0056 : Wff := (syn_wral p (syn_chwcards (syn_cvv)) syntaxFormula0010)
  let syntaxClass0057 : Class := (syn_cfv syntaxClass0032 (.cv r))
  let syntaxFormula0058 : Wff := (.classMem syntaxClass0057 (syn_cncs))
  let syntaxFormula0059 : Wff := (syn_wral r (syn_cnnc) syntaxFormula0058)
  let syntaxFormula0060 : Wff := (.classMem syntaxClass0033 (syn_cncs))
  let syntaxFormula0061 : Wff :=
    (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0052)
  let syntaxFormula0062 : Wff :=
    (.classMem syntaxClass0022 (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0063 : Wff :=
    (.classMem syntaxClass0022 (syn_cwppreach (syn_cwppstopstep F C) C))
  let syntaxFormula0064 : Wff :=
    (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) syntaxClass0022)
  let syntaxFormula0065 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppreach (syn_cwppstopstep F C) C))
  let syntaxFormula0066 : Wff := (syn_wb syntaxFormula0019 syntaxFormula0065)
  let syntaxFormula0067 : Wff := (syn_wb syntaxFormula0062 syntaxFormula0063)
  let syntaxFormula0068 : Wff :=
    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec)
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0069 : Wff :=
    (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))
  let syntaxClass0070 : Class := (syn_cif syntaxFormula0069 (syn_ctc C) C)
  let syntaxFormula0071 : Wff := (syn_wbr syntaxClass0070 (syn_clec) C)
  let syntaxFormula0072 : Wff := (.neg syntaxFormula0069)
  let syntaxFormula0073 : Wff := (.classEq (.cv p) syntaxClass0070)
  let syntaxFormula0074 : Wff :=
    (.classMem syntaxClass0070 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxClass0075 : Class := (syn_cfrec (syn_cwppstopstep F C) syntaxClass0070)
  let syntaxClass0076 : Class := (syn_cfv syntaxClass0075 (.cv n))
  let syntaxFormula0077 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0076)
  let syntaxFormula0078 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0077)
  let syntaxFormula0079 : Wff :=
    (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0074
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
  let syntaxFormula0080 : Wff := (syn_wa syntaxFormula0079 (.classMem (.cv n) (syn_cnnc)))
  let syntaxFormula0081 : Wff :=
    (.classMem syntaxClass0076 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxFormula0082 : Wff := (syn_wa syntaxFormula0081 syntaxFormula0040)
  let syntaxFormula0083 : Wff := (.classEq (.cv y) syntaxClass0076)
  let syntaxClass0084 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0076)
  let syntaxFormula0085 : Wff := (syn_wbr C (syn_clec) syntaxClass0084)
  let syntaxFormula0086 : Wff := (.imp syntaxFormula0077 syntaxFormula0085)
  let syntaxClass0087 : Class := (syn_cfv syntaxClass0075 (syn_cplc (.cv n) (syn_c1c)))
  let syntaxFormula0088 : Wff := (syn_wbr C (syn_clec) syntaxClass0087)
  let syntaxFormula0089 : Wff :=
    (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0088)
  let syntaxClass0090 : Class := (syn_cfv syntaxClass0075 (.cv m))
  let syntaxFormula0091 : Wff := (syn_wbr C (syn_clec) syntaxClass0090)
  let syntaxFormula0092 : Wff := (syn_wrex m (syn_cnnc) syntaxFormula0091)
  let syntaxFormula0093 : Wff := (syn_wbr C (syn_clec) syntaxClass0076)
  let syntaxFormula0094 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0093)
  let syntaxFormula0095 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0077)
  let syntaxFormula0096 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0093)
  let syntaxClass0097 : Class := (syn_cfv syntaxClass0075 (.cv r))
  let syntaxFormula0098 : Wff := (.classMem syntaxClass0097 (syn_cncs))
  let syntaxFormula0099 : Wff := (syn_wral r (syn_cnnc) syntaxFormula0098)
  let syntaxFormula0100 : Wff := (.classMem syntaxClass0076 (syn_cncs))
  let syntaxFormula0101 : Wff :=
    (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0093)
  let syntaxFormula0102 : Wff :=
    (.classMem syntaxClass0070 (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0103 : Wff :=
    (.classMem syntaxClass0070 (syn_cwppreach (syn_cwppstopstep F C) C))
  let syntaxFormula0104 : Wff := (.classEq (syn_ctc C) syntaxClass0070)
  let syntaxFormula0105 : Wff :=
    (syn_wb (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
      (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)))
  let syntaxFormula0106 : Wff := (syn_wb syntaxFormula0102 syntaxFormula0103)
  let syntaxFormula0107 : Wff :=
    (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
  let syntaxFormula0108 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppreach (syn_cwppstopstep F C) C))
  let syntaxFormula0109 : Wff := (syn_wa syntaxFormula0107 syntaxFormula0108)
  let syntaxClass0110 : Class :=
    (syn_cif syntaxFormula0107 (syn_cwppgamma (syn_cwppstopstep F C) C) C)
  let syntaxFormula0111 : Wff := (syn_wbr syntaxClass0110 (syn_clec) C)
  let syntaxFormula0112 : Wff := (.neg syntaxFormula0107)
  let syntaxFormula0113 : Wff := (syn_wa syn_wtru syntaxFormula0107)
  let syntaxFormula0114 : Wff := (syn_wa syn_wtru syntaxFormula0112)
  let syntaxFormula0115 : Wff := (.classMem syntaxClass0110 (syn_chwcards (syn_cvv)))
  let syntaxFormula0116 : Wff := (.classEq (.cv p) syntaxClass0110)
  let syntaxFormula0117 : Wff :=
    (.classMem syntaxClass0110 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxClass0118 : Class := (syn_cfrec (syn_cwppstopstep F C) syntaxClass0110)
  let syntaxClass0119 : Class := (syn_cfv syntaxClass0118 (.cv n))
  let syntaxFormula0120 : Wff := (syn_wbr (syn_ctc C) (syn_clec) syntaxClass0119)
  let syntaxFormula0121 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0120)
  let syntaxFormula0122 : Wff :=
    (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0117
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
  let syntaxFormula0123 : Wff := (syn_wa syntaxFormula0122 (.classMem (.cv n) (syn_cnnc)))
  let syntaxFormula0124 : Wff :=
    (.classMem syntaxClass0119 (syn_cdm (syn_cwppstopstep F C)))
  let syntaxFormula0125 : Wff := (syn_wa syntaxFormula0124 syntaxFormula0040)
  let syntaxFormula0126 : Wff := (.classEq (.cv y) syntaxClass0119)
  let syntaxClass0127 : Class := (syn_cfv (syn_cwppstopstep F C) syntaxClass0119)
  let syntaxFormula0128 : Wff := (syn_wbr C (syn_clec) syntaxClass0127)
  let syntaxFormula0129 : Wff := (.imp syntaxFormula0120 syntaxFormula0128)
  let syntaxClass0130 : Class := (syn_cfv syntaxClass0118 (syn_cplc (.cv n) (syn_c1c)))
  let syntaxFormula0131 : Wff := (syn_wbr C (syn_clec) syntaxClass0130)
  let syntaxFormula0132 : Wff :=
    (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0131)
  let syntaxClass0133 : Class := (syn_cfv syntaxClass0118 (.cv m))
  let syntaxFormula0134 : Wff := (syn_wbr C (syn_clec) syntaxClass0133)
  let syntaxFormula0135 : Wff := (syn_wrex m (syn_cnnc) syntaxFormula0134)
  let syntaxFormula0136 : Wff := (syn_wbr C (syn_clec) syntaxClass0119)
  let syntaxFormula0137 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0136)
  let syntaxFormula0138 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0120)
  let syntaxFormula0139 : Wff := (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0136)
  let syntaxClass0140 : Class := (syn_cfv syntaxClass0118 (.cv r))
  let syntaxFormula0141 : Wff := (.classMem syntaxClass0140 (syn_cncs))
  let syntaxFormula0142 : Wff := (syn_wral r (syn_cnnc) syntaxFormula0141)
  let syntaxFormula0143 : Wff := (.classMem syntaxClass0119 (syn_cncs))
  let syntaxFormula0144 : Wff :=
    (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0136)
  let syntaxFormula0145 : Wff :=
    (.classMem syntaxClass0110 (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0146 : Wff :=
    (.classMem syntaxClass0110 (syn_cwppreach (syn_cwppstopstep F C) C))
  let syntaxFormula0147 : Wff :=
    (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) syntaxClass0110)
  let syntaxFormula0148 : Wff :=
    (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  let syntaxFormula0149 : Wff := (syn_wb syntaxFormula0148 syntaxFormula0108)
  let syntaxFormula0150 : Wff := (syn_wb syntaxFormula0145 syntaxFormula0146)
  let syntaxFormula0151 : Wff :=
    (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec)
      (syn_cwppgamma (syn_cwppstopstep F C) C))
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0001 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0002 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammafixedhwdndv_1
      hyp_wppstopgammafixedhwdndv_2
  have p0003 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammafixedhwdndv_1
      hyp_wppstopgammafixedhwdndv_2
  have p0004 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0005 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0004
  have p0006 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0005
  have p0007 := @g_hwcardstcclndv (.cv p)
  have p0008 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammafixedhwdndv_1
      hyp_wppstopgammafixedhwdndv_2
  have p0009 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv))
      (syn_ctc (.cv p)) p0008
  have p0010 :=
    @g_sylibr (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0007 p0009
  have p0011 :=
    @g_jca (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0006 p0010
  have p0012 := Nominal.gen p0011 p
  have p0013 := (Nominal.biimpRefl syntaxFormula0001)
  have p0014 :=
    @g_mpbir syntaxFormula0001
      (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv))) syntaxFormula0000)) p0012
      p0013
  have p0015 := Nominal.ax1 syntaxFormula0000 (syn_wbr (.cv p) (syn_clec) C)
  have p0016 :=
    @g_a1i (.imp syntaxFormula0000 syntaxFormula0002)
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0015
  have p0017 :=
    @g_ralimia syntaxFormula0000 syntaxFormula0002 p (syn_chwcards (syn_cvv)) p0016
  have p0018 := Nominal.mp p0014 p0017
  have p0020 :=
    @g_a1i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0003 p0000
  have p0021 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0025 :=
    @g_syl syntaxFormula0003 (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) p0021 p0006
  have p0027 :=
    @g_a1i (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))
      syntaxFormula0003 p0001
  have p0028 :=
    @g_n_3jca syntaxFormula0003 (.classMem (syn_cwppstopstep F C) (syn_cfuns))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0020
      p0025 p0027
  have p0029 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0030 :=
    @g_jca syntaxFormula0003 syntaxFormula0004 (.classMem (.cv r) (syn_cnnc)) p0028 p0029
  have p0031 := @g_frecdomfv (syn_cwppstopstep F C) (.cv p) (.cv r)
  have p0032 := @g_syl syntaxFormula0003 syntaxFormula0005 syntaxFormula0006 p0030 p0031
  have p0034 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv))
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0004
  have p0035 := @g_sylib syntaxFormula0003 syntaxFormula0006 syntaxFormula0007 p0032 p0034
  have p0036 := @g_hwcardssnc (syn_cvv)
  have p0037 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs)
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0036
  have p0038 := @g_syl syntaxFormula0003 syntaxFormula0007 syntaxFormula0008 p0035 p0037
  have p0039 :=
    @g_rgen2 syntaxFormula0008 p r (syn_chwcards (syn_cvv)) (syn_cnnc) dv_cache_0001
      dv_cache_0002 p0038
  have p0040 := Nominal.ax1 syntaxFormula0009 (syn_wbr (.cv p) (syn_clec) C)
  have p0041 :=
    @g_a1i syntaxFormula0011 (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0040
  have p0042 :=
    @g_ralimia syntaxFormula0009 syntaxFormula0010 p (syn_chwcards (syn_cvv)) p0041
  have p0043 := Nominal.mp p0039 p0042
  have p0044 :=
    @g_wppgammatchwboundedeqndv x C (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) r p dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0002 dv_cache_0012 dv_cache_0013 p0000 p0001 p0002 p0003
      hyp_wppstopgammafixedhwdndv_6 p0018 p0043 hyp_wppstopgammafixedhwdndv_3
  have p0045 :=
    @g_wppstopgammaprefixeqndv C F p dv_cache_0003 dv_cache_0014
      hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
      hyp_wppstopgammafixedhwdndv_3 hyp_wppstopgammafixedhwdndv_4
      hyp_wppstopgammafixedhwdndv_5
  have p0046 :=
    @g_eqtri (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C))
      (syn_cwppgamma (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C))
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0044 p0045
  have p0048 := @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0049 := Nominal.mp p0000 p0048
  have p0050 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv))
      (.classMem C (syn_chwcards (syn_cvv))) p0049 hyp_wppstopgammafixedhwdndv_3
  have p0051 := @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0052 := Nominal.mp p0050 p0051
  have p0053 := @g_simpr syntaxFormula0012 syntaxFormula0013
  have p0054 := Nominal.mp p0052 p0053
  have p0057 := @g_hwcardstcclndv C
  have p0058 := Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0057
  have p0059 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv))
      (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0049 p0058
  have p0060 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0061 := Nominal.mp p0059 p0060
  have p0062 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0063 := Nominal.mp p0061 p0062
  have p0064 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppstopstep F C)
  have p0065 := @g_mpbi syntaxFormula0014 syntaxFormula0020 p0063 p0064
  have p0066 := @g_simpr syntaxFormula0018 syntaxFormula0019
  have p0067 := Nominal.mp p0065 p0066
  have p0079 := @g_simpl syntaxFormula0018 syntaxFormula0019
  have p0080 := Nominal.mp p0065 p0079
  have p0081 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0082 := Nominal.mp p0080 p0081
  have p0096 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0097 := Nominal.mp p0080 p0096
  have p0098 :=
    @g_pm3_2i syntaxFormula0017 (syn_wbr (syn_ctc C) (syn_clec) C) p0097
      hyp_wppstopgammafixedhwdndv_4
  have p0115 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs)
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0036
  have p0116 := Nominal.mp p0082 p0115
  have p0120 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_ctc C) p0036
  have p0121 := Nominal.mp p0058 p0120
  have p0123 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0036
  have p0124 := Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0123
  have p0125 :=
    @g_n_3pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cncs))
      (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) p0116 p0121 p0124
  have p0126 := @g_lectr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_ctc C) C
  have p0127 := Nominal.mp p0125 p0126
  have p0128 := Nominal.mp p0098 p0127
  have p0129 :=
    @g_pm3_2i syntaxFormula0016
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C) p0082
      p0128
  have p0130 :=
    @g_simpr syntaxFormula0016
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)
  have p0131 :=
    @g_iftrue syntaxFormula0021 (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0132 :=
    @g_breq1d syntaxFormula0021 syntaxClass0022
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C (syn_clec) p0131
  have p0133 :=
    @g_mpbird syntaxFormula0021 syntaxFormula0023
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C) p0130
      p0132
  have p0137 := @g_nclecid C
  have p0138 := Nominal.mp p0124 p0137
  have p0139 := @g_a1i (syn_wbr C (syn_clec) C) syntaxFormula0024 p0138
  have p0140 :=
    @g_iffalse syntaxFormula0021 (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0141 := @g_breq1d syntaxFormula0024 syntaxClass0022 C C (syn_clec) p0140
  have p0142 :=
    @g_mpbird syntaxFormula0024 syntaxFormula0023 (syn_wbr C (syn_clec) C) p0139 p0141
  have p0143 := @g_pm2_61i syntaxFormula0021 syntaxFormula0023 p0133 p0142
  have p0144 := @g_tru
  have p0145 := @g_simpr syn_wtru syntaxFormula0021
  have p0146 :=
    @g_simpl syntaxFormula0016
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)
  have p0147 := @g_syl syntaxFormula0025 syntaxFormula0021 syntaxFormula0016 p0145 p0146
  have p0148 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) syntaxFormula0026
      hyp_wppstopgammafixedhwdndv_3
  have p0149 :=
    @g_ifclda syn_wtru syntaxFormula0021
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C (syn_chwcards (syn_cvv)) p0147
      p0148
  have p0150 := Nominal.mp p0144 p0149
  have p0154 := Nominal.gen p0006 p
  have p0155 :=
    (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv))
        (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))))
  have p0156 :=
    @g_mpbir
      (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))
      (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv)))
          (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))))
      p0154 p0155
  have p0157 :=
    Nominal.ax1 (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (syn_wbr (.cv p) (syn_clec) C)
  have p0158 :=
    @g_a1i (.imp (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) syntaxFormula0027)
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0157
  have p0159 :=
    @g_ralimia (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) syntaxFormula0027 p
      (syn_chwcards (syn_cvv)) p0158
  have p0160 := Nominal.mp p0156 p0159
  have p0161 := @g_pm3_2i syntaxFormula0028 syntaxFormula0029 p0150 p0160
  have p0162 := @g_id syntaxFormula0030
  have p0163 := @g_breq1d syntaxFormula0030 (.cv p) syntaxClass0022 C (syn_clec) p0162
  have p0165 :=
    @g_eleq1d syntaxFormula0030 (.cv p) syntaxClass0022 (syn_cdm (syn_cwppstopstep F C))
      p0162
  have p0166 :=
    @g_imbi12d syntaxFormula0030 (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0023
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) syntaxFormula0031 p0163 p0165
  have p0167 :=
    @g_rspcva syntaxFormula0027 (.imp syntaxFormula0023 syntaxFormula0031) p
      syntaxClass0022 (syn_chwcards (syn_cvv)) dv_cache_0018 dv_cache_0019 dv_cache_0020
      p0166
  have p0168 := Nominal.mp p0161 p0167
  have p0169 := Nominal.mp p0143 p0168
  have p0173 := @g_elex (syn_ctc C) (syn_chwcards (syn_cvv))
  have p0174 := Nominal.mp p0058 p0173
  have p0175 :=
    @g_wppreachfwdrexvndv (syn_ctc C) syntaxClass0022 n (syn_cwppstopstep F C)
      dv_cache_0021 dv_cache_0022 dv_cache_0023 p0000 p0169 p0001 p0174
  have p0176 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0034
  have p0177 := @g_peano2 (.cv n)
  have p0178 :=
    @g_syl syntaxFormula0035 (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0176 p0177
  have p0179 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0034
  have p0180 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0031
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0000
      p0169 p0001
  have p0181 := @g_a1i syntaxFormula0036 syntaxFormula0035 p0180
  have p0183 :=
    @g_jca syntaxFormula0035 syntaxFormula0036 (.classMem (.cv n) (syn_cnnc)) p0181 p0176
  have p0184 := @g_frecdomfv (syn_cwppstopstep F C) syntaxClass0022 (.cv n)
  have p0185 := @g_syl syntaxFormula0035 syntaxFormula0037 syntaxFormula0038 p0183 p0184
  have p0186 := @g_id syntaxFormula0040
  have p0187 := @g_a1d syntaxFormula0040 syntaxFormula0040 syntaxFormula0035 p0186
  have p0188 := @g_pm3_2 syntaxFormula0038 syntaxFormula0040
  have p0189 :=
    @g_syl9 syntaxFormula0040 syntaxFormula0035 syntaxFormula0040 syntaxFormula0038
      syntaxFormula0041 p0187 p0188
  have p0190 :=
    @g_syl5 syntaxFormula0035 syntaxFormula0038 syntaxFormula0040
      (.imp syntaxFormula0035 syntaxFormula0041) p0185 p0189
  have p0191 := @g_pm2_43d syntaxFormula0040 syntaxFormula0035 syntaxFormula0041 p0190
  have p0192 := @g_id syntaxFormula0042
  have p0193 :=
    @g_breq2d syntaxFormula0042 (.cv y) syntaxClass0033 (syn_ctc C) (syn_clec) p0192
  have p0195 :=
    @g_fveq2d syntaxFormula0042 (.cv y) syntaxClass0033 (syn_cwppstopstep F C) p0192
  have p0196 :=
    @g_breq2d syntaxFormula0042 (syn_cfv (syn_cwppstopstep F C) (.cv y)) syntaxClass0043 C
      (syn_clec) p0195
  have p0197 :=
    @g_imbi12d syntaxFormula0042 (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      syntaxFormula0034 (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))
      syntaxFormula0044 p0193 p0196
  have p0198 :=
    @g_rspcva syntaxFormula0039 syntaxFormula0045 y syntaxClass0033
      (syn_cdm (syn_cwppstopstep F C)) dv_cache_0024 dv_cache_0025 dv_cache_0026 p0197
  have p0199 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0035 syntaxFormula0041 syntaxFormula0045 p0191
      p0198
  have p0200 :=
    @g_mpdi syntaxFormula0040 syntaxFormula0035 syntaxFormula0034 syntaxFormula0044 p0179
      p0199
  have p0205 := @g_wpporbitsucndv (syn_cwppstopstep F C) syntaxClass0022 (.cv n)
  have p0206 :=
    @g_syl syntaxFormula0035 syntaxFormula0037 (.classEq syntaxClass0046 syntaxClass0043)
      p0183 p0205
  have p0207 :=
    @g_breq2d syntaxFormula0035 syntaxClass0046 syntaxClass0043 C (syn_clec) p0206
  have p0208 := @g_biimprd syntaxFormula0035 syntaxFormula0047 syntaxFormula0044 p0207
  have p0209 :=
    @g_sylcom syntaxFormula0040 syntaxFormula0035 syntaxFormula0044 syntaxFormula0047
      p0200 p0208
  have p0210 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0047
  have p0211 :=
    @g_syl9 syntaxFormula0040 syntaxFormula0035 syntaxFormula0047
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0048 p0209 p0210
  have p0212 :=
    @g_syl5 syntaxFormula0035 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      syntaxFormula0040 (.imp syntaxFormula0035 syntaxFormula0048) p0178 p0211
  have p0213 := @g_pm2_43d syntaxFormula0040 syntaxFormula0035 syntaxFormula0048 p0212
  have p0214 := @g_id (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
  have p0215 :=
    @g_fveq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.cv m)
      (syn_cplc (.cv n) (syn_c1c)) syntaxClass0032 p0214
  have p0216 :=
    @g_breq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) syntaxClass0049
      syntaxClass0046 C (syn_clec) p0215
  have p0217 :=
    @g_rspcev syntaxFormula0050 syntaxFormula0047 m (syn_cplc (.cv n) (syn_c1c))
      (syn_cnnc) dv_cache_0027 dv_cache_0028 dv_cache_0029 p0216
  have p0218 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0035 syntaxFormula0048 syntaxFormula0051 p0213
      p0217
  have p0219 :=
    @g_exp3a syntaxFormula0040 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0034
      syntaxFormula0051 p0218
  have p0220 :=
    @g_rexlimdv syntaxFormula0040 syntaxFormula0034 syntaxFormula0051 n (syn_cnnc)
      dv_cache_0030 dv_cache_0031 p0219
  have p0221 := @g_id (.classEq (.cv m) (.cv n))
  have p0222 := @g_fveq2d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) syntaxClass0032 p0221
  have p0223 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) syntaxClass0049 syntaxClass0033 C (syn_clec)
      p0222
  have p0224_e00_recanon :
    Nominal.NPrf (.imp (.objEq m n) (syn_wb syntaxFormula0050 syntaxFormula0052)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_wrex, syn_wex, syn_cphi, syn_clec, syn_copab, syn_csn, syn_cin,
          syn_cplc, syn_c1c, syn_cif, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0223
  have p0224 :=
    @g_cbvrexv syntaxFormula0050 syntaxFormula0052 m n (syn_cnnc) dv_cache_0028
      dv_cache_0032 dv_cache_0033 dv_cache_0034 p0224_e00_recanon
  have p0225 := @g_biimpi syntaxFormula0051 syntaxFormula0053 p0224
  have p0226 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0054 syntaxFormula0051 syntaxFormula0053 p0220
      p0225
  have p0227 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0055
      hyp_wppstopgammafixedhwdndv_4
  have p0228 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0052
  have p0229 :=
    @g_jca syntaxFormula0055 (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0052 p0227
      p0228
  have p0235 := @g_a1i (.classMem (syn_ctc C) (syn_cncs)) syntaxFormula0055 p0121
  have p0239 := @g_a1i (.classMem C (syn_cncs)) syntaxFormula0055 p0124
  have p0240 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0052
  have p0241 := @g_id (.classMem (.cv n) (syn_cnnc))
  have p0288 := @g_pm3_2i syntaxFormula0028 syntaxFormula0056 p0150 p0043
  have p0291 := @g_eqidd syntaxFormula0030 (syn_cwppstopstep F C)
  have p0293 :=
    @g_jca syntaxFormula0030 (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C))
      syntaxFormula0030 p0291 p0162
  have p0294 :=
    @g_freceq12 (syn_cwppstopstep F C) (syn_cwppstopstep F C) (.cv p) syntaxClass0022
  have p0295 :=
    @g_syl syntaxFormula0030
      (syn_wa (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) syntaxFormula0030)
      (.classEq (syn_cfrec (syn_cwppstopstep F C) (.cv p)) syntaxClass0032) p0293 p0294
  have p0296 :=
    @g_fveq1d syntaxFormula0030 (.cv r) (syn_cfrec (syn_cwppstopstep F C) (.cv p))
      syntaxClass0032 p0295
  have p0297 :=
    @g_eleq1d syntaxFormula0030
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) syntaxClass0057
      (syn_cncs) p0296
  have p0298 :=
    @g_ralbidv syntaxFormula0030 syntaxFormula0008 syntaxFormula0058 r (syn_cnnc)
      dv_cache_0035 p0297
  have p0299 :=
    @g_imbi12d syntaxFormula0030 (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0023
      syntaxFormula0009 syntaxFormula0059 p0163 p0298
  have p0300 :=
    @g_rspcva syntaxFormula0010 (.imp syntaxFormula0023 syntaxFormula0059) p
      syntaxClass0022 (syn_chwcards (syn_cvv)) dv_cache_0018 dv_cache_0019 dv_cache_0036
      p0299
  have p0301 := Nominal.mp p0288 p0300
  have p0302 := Nominal.mp p0143 p0301
  have p0303 := @g_a1i syntaxFormula0059 (.classMem (.cv n) (syn_cnnc)) p0302
  have p0304 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) syntaxFormula0059
      p0241 p0303
  have p0305 := @g_id (.classEq (.cv r) (.cv n))
  have p0306 := @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) syntaxClass0032 p0305
  have p0307 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) syntaxClass0057 syntaxClass0033 (syn_cncs) p0306
  have p0308 :=
    @g_rspcva syntaxFormula0058 syntaxFormula0060 r (.cv n) (syn_cnnc) dv_cache_0037
      dv_cache_0038 dv_cache_0039 p0307
  have p0309 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0059) syntaxFormula0060 p0304
      p0308
  have p0310 :=
    @g_syl syntaxFormula0055 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0060 p0240 p0309
  have p0311 :=
    @g_n_3jca syntaxFormula0055 (.classMem (syn_ctc C) (syn_cncs))
      (.classMem C (syn_cncs)) syntaxFormula0060 p0235 p0239 p0310
  have p0312 := @g_lectr (syn_ctc C) C syntaxClass0033
  have p0313 :=
    @g_syl syntaxFormula0055
      (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) syntaxFormula0060)
      (.imp syntaxFormula0061 syntaxFormula0034) p0311 p0312
  have p0314 := @g_mpd syntaxFormula0055 syntaxFormula0061 syntaxFormula0034 p0229 p0313
  have p0315 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) syntaxFormula0052 syntaxFormula0034 p0314
  have p0316 := @g_reximia syntaxFormula0052 syntaxFormula0034 n (syn_cnnc) p0315
  have p0317 :=
    @g_impbid1 syntaxFormula0040 syntaxFormula0054 syntaxFormula0053 p0226 p0316
  have p0318 :=
    @g_syl5bb syntaxFormula0062 syntaxFormula0054 syntaxFormula0040 syntaxFormula0053
      p0175 p0317
  have p0319 := @g_elex C (syn_chwcards (syn_cvv))
  have p0320 := Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0319
  have p0321 :=
    @g_wppreachfwdrexvndv C syntaxClass0022 n (syn_cwppstopstep F C) dv_cache_0040
      dv_cache_0022 dv_cache_0023 p0000 p0169 p0001 p0320
  have p0322 := @g_bicomi syntaxFormula0063 syntaxFormula0053 p0321
  have p0323 :=
    @g_syl6bb syntaxFormula0040 syntaxFormula0062 syntaxFormula0053 syntaxFormula0063
      p0318 p0322
  have p0325 :=
    @g_eqcomd syntaxFormula0021 syntaxClass0022
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0131
  have p0326 := @g_id syntaxFormula0064
  have p0327 :=
    @g_eleq1d syntaxFormula0064 (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      syntaxClass0022 (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)) p0326
  have p0329 :=
    @g_eleq1d syntaxFormula0064 (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      syntaxClass0022 (syn_cwppreach (syn_cwppstopstep F C) C) p0326
  have p0330 :=
    @g_bibi12d syntaxFormula0064 syntaxFormula0019 syntaxFormula0062 syntaxFormula0065
      syntaxFormula0063 p0327 p0329
  have p0331 :=
    @g_syl syntaxFormula0021 syntaxFormula0064
      (syn_wb syntaxFormula0066 syntaxFormula0067) p0325 p0330
  have p0332 :=
    @g_syl5ibrcom syntaxFormula0040 syntaxFormula0066 syntaxFormula0021 syntaxFormula0067
      p0323 p0331
  have p0333 := @g_mpi syntaxFormula0040 syntaxFormula0021 syntaxFormula0066 p0129 p0332
  have p0334 := @g_mpbii syntaxFormula0040 syntaxFormula0019 syntaxFormula0065 p0067 p0333
  have p0397 := @g_jctil syntaxFormula0040 syntaxFormula0065 syntaxFormula0021 p0334 p0129
  have p0398 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppstopstep F C)
  have p0399 :=
    @g_sylibr syntaxFormula0040 (syn_wa syntaxFormula0021 syntaxFormula0065)
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
        (syn_cwppcand (syn_cwppstopstep F C) C))
      p0397 p0398
  have p0400 :=
    @g_id (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))
  have p0401 :=
    @g_breq2d (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))
      (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) p0400
  have p0402 :=
    @g_rspcv (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k))
      syntaxFormula0068 k (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppcand (syn_cwppstopstep F C) C) dv_cache_0041 dv_cache_0042 dv_cache_0043
      p0401
  have p0403 :=
    @g_syl syntaxFormula0040
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
        (syn_cwppcand (syn_cwppstopstep F C) C))
      (.imp syntaxFormula0013 syntaxFormula0068) p0399 p0402
  have p0404 := @g_mpi syntaxFormula0040 syntaxFormula0013 syntaxFormula0068 p0054 p0403
  have p0412 := @g_simpr syntaxFormula0014 syntaxFormula0015
  have p0413 := Nominal.mp p0061 p0412
  have p0425 := @g_wppcandselfndv (syn_ctc C) (syn_cwppstopstep F C) p0049
  have p0426 := Nominal.mp p0058 p0425
  have p0427 := @g_elwppcand (syn_ctc C) (syn_ctc C) (syn_cwppstopstep F C)
  have p0428 :=
    @g_mpbi (.classMem (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)))
      (syn_wa (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc C)))
        (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))))
      p0426 p0427
  have p0429 :=
    @g_simpr
      (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc C)))
      (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0430 := Nominal.mp p0428 p0429
  have p0433 :=
    @g_pm3_2i (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc C) (syn_clec) C) p0058 hyp_wppstopgammafixedhwdndv_4
  have p0434 :=
    @g_simpr (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc C) (syn_clec) C)
  have p0435 := @g_iftrue syntaxFormula0069 (syn_ctc C) C
  have p0436 := @g_breq1d syntaxFormula0069 syntaxClass0070 (syn_ctc C) C (syn_clec) p0435
  have p0437 :=
    @g_mpbird syntaxFormula0069 syntaxFormula0071 (syn_wbr (syn_ctc C) (syn_clec) C) p0434
      p0436
  have p0443 := @g_a1i (syn_wbr C (syn_clec) C) syntaxFormula0072 p0138
  have p0444 := @g_iffalse syntaxFormula0069 (syn_ctc C) C
  have p0445 := @g_breq1d syntaxFormula0072 syntaxClass0070 C C (syn_clec) p0444
  have p0446 :=
    @g_mpbird syntaxFormula0072 syntaxFormula0071 (syn_wbr C (syn_clec) C) p0443 p0445
  have p0447 := @g_pm2_61i syntaxFormula0069 syntaxFormula0071 p0437 p0446
  have p0449 := @g_simpr syn_wtru syntaxFormula0069
  have p0450 :=
    @g_simpl (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc C) (syn_clec) C)
  have p0451 :=
    @g_syl (syn_wa syn_wtru syntaxFormula0069) syntaxFormula0069
      (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0449 p0450
  have p0452 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru syntaxFormula0072)
      hyp_wppstopgammafixedhwdndv_3
  have p0453 :=
    @g_ifclda syn_wtru syntaxFormula0069 (syn_ctc C) C (syn_chwcards (syn_cvv)) p0451
      p0452
  have p0454 := Nominal.mp p0144 p0453
  have p0455 :=
    @g_pm3_2i (.classMem syntaxClass0070 (syn_chwcards (syn_cvv))) syntaxFormula0029 p0454
      p0160
  have p0456 := @g_id syntaxFormula0073
  have p0457 := @g_breq1d syntaxFormula0073 (.cv p) syntaxClass0070 C (syn_clec) p0456
  have p0459 :=
    @g_eleq1d syntaxFormula0073 (.cv p) syntaxClass0070 (syn_cdm (syn_cwppstopstep F C))
      p0456
  have p0460 :=
    @g_imbi12d syntaxFormula0073 (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0071
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) syntaxFormula0074 p0457 p0459
  have p0461 :=
    @g_rspcva syntaxFormula0027 (.imp syntaxFormula0071 syntaxFormula0074) p
      syntaxClass0070 (syn_chwcards (syn_cvv)) dv_cache_0044 dv_cache_0019 dv_cache_0045
      p0460
  have p0462 := Nominal.mp p0455 p0461
  have p0463 := Nominal.mp p0447 p0462
  have p0468 :=
    @g_wppreachfwdrexvndv (syn_ctc C) syntaxClass0070 n (syn_cwppstopstep F C)
      dv_cache_0021 dv_cache_0046 dv_cache_0023 p0000 p0463 p0001 p0174
  have p0469 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0077
  have p0471 :=
    @g_syl syntaxFormula0078 (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0469 p0177
  have p0472 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0077
  have p0473 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0074
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0000
      p0463 p0001
  have p0474 := @g_a1i syntaxFormula0079 syntaxFormula0078 p0473
  have p0476 :=
    @g_jca syntaxFormula0078 syntaxFormula0079 (.classMem (.cv n) (syn_cnnc)) p0474 p0469
  have p0477 := @g_frecdomfv (syn_cwppstopstep F C) syntaxClass0070 (.cv n)
  have p0478 := @g_syl syntaxFormula0078 syntaxFormula0080 syntaxFormula0081 p0476 p0477
  have p0479 := @g_a1d syntaxFormula0040 syntaxFormula0040 syntaxFormula0078 p0186
  have p0480 := @g_pm3_2 syntaxFormula0081 syntaxFormula0040
  have p0481 :=
    @g_syl9 syntaxFormula0040 syntaxFormula0078 syntaxFormula0040 syntaxFormula0081
      syntaxFormula0082 p0479 p0480
  have p0482 :=
    @g_syl5 syntaxFormula0078 syntaxFormula0081 syntaxFormula0040
      (.imp syntaxFormula0078 syntaxFormula0082) p0478 p0481
  have p0483 := @g_pm2_43d syntaxFormula0040 syntaxFormula0078 syntaxFormula0082 p0482
  have p0484 := @g_id syntaxFormula0083
  have p0485 :=
    @g_breq2d syntaxFormula0083 (.cv y) syntaxClass0076 (syn_ctc C) (syn_clec) p0484
  have p0487 :=
    @g_fveq2d syntaxFormula0083 (.cv y) syntaxClass0076 (syn_cwppstopstep F C) p0484
  have p0488 :=
    @g_breq2d syntaxFormula0083 (syn_cfv (syn_cwppstopstep F C) (.cv y)) syntaxClass0084 C
      (syn_clec) p0487
  have p0489 :=
    @g_imbi12d syntaxFormula0083 (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      syntaxFormula0077 (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))
      syntaxFormula0085 p0485 p0488
  have p0490 :=
    @g_rspcva syntaxFormula0039 syntaxFormula0086 y syntaxClass0076
      (syn_cdm (syn_cwppstopstep F C)) dv_cache_0047 dv_cache_0025 dv_cache_0048 p0489
  have p0491 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0078 syntaxFormula0082 syntaxFormula0086 p0483
      p0490
  have p0492 :=
    @g_mpdi syntaxFormula0040 syntaxFormula0078 syntaxFormula0077 syntaxFormula0085 p0472
      p0491
  have p0497 := @g_wpporbitsucndv (syn_cwppstopstep F C) syntaxClass0070 (.cv n)
  have p0498 :=
    @g_syl syntaxFormula0078 syntaxFormula0080 (.classEq syntaxClass0087 syntaxClass0084)
      p0476 p0497
  have p0499 :=
    @g_breq2d syntaxFormula0078 syntaxClass0087 syntaxClass0084 C (syn_clec) p0498
  have p0500 := @g_biimprd syntaxFormula0078 syntaxFormula0088 syntaxFormula0085 p0499
  have p0501 :=
    @g_sylcom syntaxFormula0040 syntaxFormula0078 syntaxFormula0085 syntaxFormula0088
      p0492 p0500
  have p0502 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0088
  have p0503 :=
    @g_syl9 syntaxFormula0040 syntaxFormula0078 syntaxFormula0088
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0089 p0501 p0502
  have p0504 :=
    @g_syl5 syntaxFormula0078 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      syntaxFormula0040 (.imp syntaxFormula0078 syntaxFormula0089) p0471 p0503
  have p0505 := @g_pm2_43d syntaxFormula0040 syntaxFormula0078 syntaxFormula0089 p0504
  have p0507 :=
    @g_fveq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.cv m)
      (syn_cplc (.cv n) (syn_c1c)) syntaxClass0075 p0214
  have p0508 :=
    @g_breq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) syntaxClass0090
      syntaxClass0087 C (syn_clec) p0507
  have p0509 :=
    @g_rspcev syntaxFormula0091 syntaxFormula0088 m (syn_cplc (.cv n) (syn_c1c))
      (syn_cnnc) dv_cache_0027 dv_cache_0028 dv_cache_0049 p0508
  have p0510 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0078 syntaxFormula0089 syntaxFormula0092 p0505
      p0509
  have p0511 :=
    @g_exp3a syntaxFormula0040 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0077
      syntaxFormula0092 p0510
  have p0512 :=
    @g_rexlimdv syntaxFormula0040 syntaxFormula0077 syntaxFormula0092 n (syn_cnnc)
      dv_cache_0050 dv_cache_0031 p0511
  have p0513 := @g_id (.classEq (.cv m) (.cv n))
  have p0514 := @g_fveq2d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) syntaxClass0075 p0513
  have p0515 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) syntaxClass0090 syntaxClass0076 C (syn_clec)
      p0514
  have p0516_e00_recanon :
    Nominal.NPrf (.imp (.objEq m n) (syn_wb syntaxFormula0091 syntaxFormula0093)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_wrex, syn_wex, syn_cphi, syn_clec, syn_copab, syn_csn, syn_cin,
          syn_cplc, syn_c1c, syn_cif, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0515
  have p0516 :=
    @g_cbvrexv syntaxFormula0091 syntaxFormula0093 m n (syn_cnnc) dv_cache_0028
      dv_cache_0032 dv_cache_0051 dv_cache_0052 p0516_e00_recanon
  have p0517 := @g_biimpi syntaxFormula0092 syntaxFormula0094 p0516
  have p0518 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0095 syntaxFormula0092 syntaxFormula0094 p0512
      p0517
  have p0519 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0096
      hyp_wppstopgammafixedhwdndv_4
  have p0520 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0093
  have p0521 :=
    @g_jca syntaxFormula0096 (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0093 p0519
      p0520
  have p0527 := @g_a1i (.classMem (syn_ctc C) (syn_cncs)) syntaxFormula0096 p0121
  have p0531 := @g_a1i (.classMem C (syn_cncs)) syntaxFormula0096 p0124
  have p0532 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0093
  have p0555 :=
    @g_pm3_2i (.classMem syntaxClass0070 (syn_chwcards (syn_cvv))) syntaxFormula0056 p0454
      p0043
  have p0558 := @g_eqidd syntaxFormula0073 (syn_cwppstopstep F C)
  have p0560 :=
    @g_jca syntaxFormula0073 (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C))
      syntaxFormula0073 p0558 p0456
  have p0561 :=
    @g_freceq12 (syn_cwppstopstep F C) (syn_cwppstopstep F C) (.cv p) syntaxClass0070
  have p0562 :=
    @g_syl syntaxFormula0073
      (syn_wa (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) syntaxFormula0073)
      (.classEq (syn_cfrec (syn_cwppstopstep F C) (.cv p)) syntaxClass0075) p0560 p0561
  have p0563 :=
    @g_fveq1d syntaxFormula0073 (.cv r) (syn_cfrec (syn_cwppstopstep F C) (.cv p))
      syntaxClass0075 p0562
  have p0564 :=
    @g_eleq1d syntaxFormula0073
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) syntaxClass0097
      (syn_cncs) p0563
  have p0565 :=
    @g_ralbidv syntaxFormula0073 syntaxFormula0008 syntaxFormula0098 r (syn_cnnc)
      dv_cache_0053 p0564
  have p0566 :=
    @g_imbi12d syntaxFormula0073 (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0071
      syntaxFormula0009 syntaxFormula0099 p0457 p0565
  have p0567 :=
    @g_rspcva syntaxFormula0010 (.imp syntaxFormula0071 syntaxFormula0099) p
      syntaxClass0070 (syn_chwcards (syn_cvv)) dv_cache_0044 dv_cache_0019 dv_cache_0054
      p0566
  have p0568 := Nominal.mp p0555 p0567
  have p0569 := Nominal.mp p0447 p0568
  have p0570 := @g_a1i syntaxFormula0099 (.classMem (.cv n) (syn_cnnc)) p0569
  have p0571 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) syntaxFormula0099
      p0241 p0570
  have p0573 := @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) syntaxClass0075 p0305
  have p0574 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) syntaxClass0097 syntaxClass0076 (syn_cncs) p0573
  have p0575 :=
    @g_rspcva syntaxFormula0098 syntaxFormula0100 r (.cv n) (syn_cnnc) dv_cache_0037
      dv_cache_0038 dv_cache_0055 p0574
  have p0576 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0099) syntaxFormula0100 p0571
      p0575
  have p0577 :=
    @g_syl syntaxFormula0096 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0100 p0532 p0576
  have p0578 :=
    @g_n_3jca syntaxFormula0096 (.classMem (syn_ctc C) (syn_cncs))
      (.classMem C (syn_cncs)) syntaxFormula0100 p0527 p0531 p0577
  have p0579 := @g_lectr (syn_ctc C) C syntaxClass0076
  have p0580 :=
    @g_syl syntaxFormula0096
      (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) syntaxFormula0100)
      (.imp syntaxFormula0101 syntaxFormula0077) p0578 p0579
  have p0581 := @g_mpd syntaxFormula0096 syntaxFormula0101 syntaxFormula0077 p0521 p0580
  have p0582 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) syntaxFormula0093 syntaxFormula0077 p0581
  have p0583 := @g_reximia syntaxFormula0093 syntaxFormula0077 n (syn_cnnc) p0582
  have p0584 :=
    @g_impbid1 syntaxFormula0040 syntaxFormula0095 syntaxFormula0094 p0518 p0583
  have p0585 :=
    @g_syl5bb syntaxFormula0102 syntaxFormula0095 syntaxFormula0040 syntaxFormula0094
      p0468 p0584
  have p0588 :=
    @g_wppreachfwdrexvndv C syntaxClass0070 n (syn_cwppstopstep F C) dv_cache_0040
      dv_cache_0046 dv_cache_0023 p0000 p0463 p0001 p0320
  have p0589 := @g_bicomi syntaxFormula0103 syntaxFormula0094 p0588
  have p0590 :=
    @g_syl6bb syntaxFormula0040 syntaxFormula0102 syntaxFormula0094 syntaxFormula0103
      p0585 p0589
  have p0592 := @g_eqcomd syntaxFormula0069 syntaxClass0070 (syn_ctc C) p0435
  have p0593 := @g_id syntaxFormula0104
  have p0594 :=
    @g_eleq1d syntaxFormula0104 (syn_ctc C) syntaxClass0070
      (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)) p0593
  have p0596 :=
    @g_eleq1d syntaxFormula0104 (syn_ctc C) syntaxClass0070
      (syn_cwppreach (syn_cwppstopstep F C) C) p0593
  have p0597 :=
    @g_bibi12d syntaxFormula0104
      (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
      syntaxFormula0102 (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C))
      syntaxFormula0103 p0594 p0596
  have p0598 :=
    @g_syl syntaxFormula0069 syntaxFormula0104
      (syn_wb syntaxFormula0105 syntaxFormula0106) p0592 p0597
  have p0599 :=
    @g_syl5ibrcom syntaxFormula0040 syntaxFormula0105 syntaxFormula0069 syntaxFormula0106
      p0590 p0598
  have p0600 := @g_mpi syntaxFormula0040 syntaxFormula0069 syntaxFormula0105 p0433 p0599
  have p0601 :=
    @g_mpbii syntaxFormula0040
      (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
      (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0430 p0600
  have p0605 :=
    @g_jctil syntaxFormula0040
      (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)) syntaxFormula0069
      p0601 p0433
  have p0606 := @g_elwppcand C (syn_ctc C) (syn_cwppstopstep F C)
  have p0607 :=
    @g_sylibr syntaxFormula0040
      (syn_wa syntaxFormula0069
        (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)))
      (.classMem (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) C)) p0605 p0606
  have p0608 := @g_id (.classEq (.cv k) (syn_ctc C))
  have p0609 :=
    @g_breq2d (.classEq (.cv k) (syn_ctc C)) (.cv k) (syn_ctc C)
      (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) p0608
  have p0610 :=
    @g_rspcv (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)) k
      (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) C) dv_cache_0017 dv_cache_0042
      dv_cache_0056 p0609
  have p0611 :=
    @g_syl syntaxFormula0040
      (.classMem (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) C))
      (.imp syntaxFormula0013
        (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)))
      p0607 p0610
  have p0612 :=
    @g_mpi syntaxFormula0040 syntaxFormula0013
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)) p0054
      p0611
  have p0618 := @g_simpl syntaxFormula0012 syntaxFormula0013
  have p0619 := Nominal.mp p0052 p0618
  have p0620 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0621 := @g_mpbi syntaxFormula0012 syntaxFormula0109 p0619 p0620
  have p0622 := @g_simpl syntaxFormula0107 syntaxFormula0108
  have p0623 := Nominal.mp p0621 p0622
  have p0624 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0625 := Nominal.mp p0623 p0624
  have p0626 :=
    @g_jctil syntaxFormula0040
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C))
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0612
      p0625
  have p0636 := @g_simpr syntaxFormula0107 syntaxFormula0108
  have p0637 := Nominal.mp p0621 p0636
  have p0662 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0663 := Nominal.mp p0623 p0662
  have p0664 :=
    @g_pm3_2i
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C) p0625 p0663
  have p0666 := @g_iftrue syntaxFormula0107 (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0667 :=
    @g_breq1d syntaxFormula0107 syntaxClass0110 (syn_cwppgamma (syn_cwppstopstep F C) C) C
      (syn_clec) p0666
  have p0668 :=
    @g_mpbird syntaxFormula0107 syntaxFormula0111
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C) p0662 p0667
  have p0674 := @g_a1i (syn_wbr C (syn_clec) C) syntaxFormula0112 p0138
  have p0675 := @g_iffalse syntaxFormula0107 (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0676 := @g_breq1d syntaxFormula0112 syntaxClass0110 C C (syn_clec) p0675
  have p0677 :=
    @g_mpbird syntaxFormula0112 syntaxFormula0111 (syn_wbr C (syn_clec) C) p0674 p0676
  have p0678 := @g_pm2_61i syntaxFormula0107 syntaxFormula0111 p0668 p0677
  have p0680 := @g_simpr syn_wtru syntaxFormula0107
  have p0682 :=
    @g_syl syntaxFormula0113 syntaxFormula0107
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0680
      p0624
  have p0683 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) syntaxFormula0114
      hyp_wppstopgammafixedhwdndv_3
  have p0684 :=
    @g_ifclda syn_wtru syntaxFormula0107 (syn_cwppgamma (syn_cwppstopstep F C) C) C
      (syn_chwcards (syn_cvv)) p0682 p0683
  have p0685 := Nominal.mp p0144 p0684
  have p0686 := @g_pm3_2i syntaxFormula0115 syntaxFormula0029 p0685 p0160
  have p0687 := @g_id syntaxFormula0116
  have p0688 := @g_breq1d syntaxFormula0116 (.cv p) syntaxClass0110 C (syn_clec) p0687
  have p0690 :=
    @g_eleq1d syntaxFormula0116 (.cv p) syntaxClass0110 (syn_cdm (syn_cwppstopstep F C))
      p0687
  have p0691 :=
    @g_imbi12d syntaxFormula0116 (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0111
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) syntaxFormula0117 p0688 p0690
  have p0692 :=
    @g_rspcva syntaxFormula0027 (.imp syntaxFormula0111 syntaxFormula0117) p
      syntaxClass0110 (syn_chwcards (syn_cvv)) dv_cache_0057 dv_cache_0019 dv_cache_0058
      p0691
  have p0693 := Nominal.mp p0686 p0692
  have p0694 := Nominal.mp p0678 p0693
  have p0699 :=
    @g_wppreachfwdrexvndv (syn_ctc C) syntaxClass0110 n (syn_cwppstopstep F C)
      dv_cache_0021 dv_cache_0059 dv_cache_0023 p0000 p0694 p0001 p0174
  have p0700 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0120
  have p0702 :=
    @g_syl syntaxFormula0121 (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0700 p0177
  have p0703 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0120
  have p0704 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) syntaxFormula0117
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0000
      p0694 p0001
  have p0705 := @g_a1i syntaxFormula0122 syntaxFormula0121 p0704
  have p0707 :=
    @g_jca syntaxFormula0121 syntaxFormula0122 (.classMem (.cv n) (syn_cnnc)) p0705 p0700
  have p0708 := @g_frecdomfv (syn_cwppstopstep F C) syntaxClass0110 (.cv n)
  have p0709 := @g_syl syntaxFormula0121 syntaxFormula0123 syntaxFormula0124 p0707 p0708
  have p0710 := @g_a1d syntaxFormula0040 syntaxFormula0040 syntaxFormula0121 p0186
  have p0711 := @g_pm3_2 syntaxFormula0124 syntaxFormula0040
  have p0712 :=
    @g_syl9 syntaxFormula0040 syntaxFormula0121 syntaxFormula0040 syntaxFormula0124
      syntaxFormula0125 p0710 p0711
  have p0713 :=
    @g_syl5 syntaxFormula0121 syntaxFormula0124 syntaxFormula0040
      (.imp syntaxFormula0121 syntaxFormula0125) p0709 p0712
  have p0714 := @g_pm2_43d syntaxFormula0040 syntaxFormula0121 syntaxFormula0125 p0713
  have p0715 := @g_id syntaxFormula0126
  have p0716 :=
    @g_breq2d syntaxFormula0126 (.cv y) syntaxClass0119 (syn_ctc C) (syn_clec) p0715
  have p0718 :=
    @g_fveq2d syntaxFormula0126 (.cv y) syntaxClass0119 (syn_cwppstopstep F C) p0715
  have p0719 :=
    @g_breq2d syntaxFormula0126 (syn_cfv (syn_cwppstopstep F C) (.cv y)) syntaxClass0127 C
      (syn_clec) p0718
  have p0720 :=
    @g_imbi12d syntaxFormula0126 (syn_wbr (syn_ctc C) (syn_clec) (.cv y))
      syntaxFormula0120 (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))
      syntaxFormula0128 p0716 p0719
  have p0721 :=
    @g_rspcva syntaxFormula0039 syntaxFormula0129 y syntaxClass0119
      (syn_cdm (syn_cwppstopstep F C)) dv_cache_0060 dv_cache_0025 dv_cache_0061 p0720
  have p0722 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0121 syntaxFormula0125 syntaxFormula0129 p0714
      p0721
  have p0723 :=
    @g_mpdi syntaxFormula0040 syntaxFormula0121 syntaxFormula0120 syntaxFormula0128 p0703
      p0722
  have p0728 := @g_wpporbitsucndv (syn_cwppstopstep F C) syntaxClass0110 (.cv n)
  have p0729 :=
    @g_syl syntaxFormula0121 syntaxFormula0123 (.classEq syntaxClass0130 syntaxClass0127)
      p0707 p0728
  have p0730 :=
    @g_breq2d syntaxFormula0121 syntaxClass0130 syntaxClass0127 C (syn_clec) p0729
  have p0731 := @g_biimprd syntaxFormula0121 syntaxFormula0131 syntaxFormula0128 p0730
  have p0732 :=
    @g_sylcom syntaxFormula0040 syntaxFormula0121 syntaxFormula0128 syntaxFormula0131
      p0723 p0731
  have p0733 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0131
  have p0734 :=
    @g_syl9 syntaxFormula0040 syntaxFormula0121 syntaxFormula0131
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) syntaxFormula0132 p0732 p0733
  have p0735 :=
    @g_syl5 syntaxFormula0121 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      syntaxFormula0040 (.imp syntaxFormula0121 syntaxFormula0132) p0702 p0734
  have p0736 := @g_pm2_43d syntaxFormula0040 syntaxFormula0121 syntaxFormula0132 p0735
  have p0738 :=
    @g_fveq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.cv m)
      (syn_cplc (.cv n) (syn_c1c)) syntaxClass0118 p0214
  have p0739 :=
    @g_breq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) syntaxClass0133
      syntaxClass0130 C (syn_clec) p0738
  have p0740 :=
    @g_rspcev syntaxFormula0134 syntaxFormula0131 m (syn_cplc (.cv n) (syn_c1c))
      (syn_cnnc) dv_cache_0027 dv_cache_0028 dv_cache_0062 p0739
  have p0741 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0121 syntaxFormula0132 syntaxFormula0135 p0736
      p0740
  have p0742 :=
    @g_exp3a syntaxFormula0040 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0120
      syntaxFormula0135 p0741
  have p0743 :=
    @g_rexlimdv syntaxFormula0040 syntaxFormula0120 syntaxFormula0135 n (syn_cnnc)
      dv_cache_0063 dv_cache_0031 p0742
  have p0744 := @g_id (.classEq (.cv m) (.cv n))
  have p0745 := @g_fveq2d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) syntaxClass0118 p0744
  have p0746 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) syntaxClass0133 syntaxClass0119 C (syn_clec)
      p0745
  have p0747_e00_recanon :
    Nominal.NPrf (.imp (.objEq m n) (syn_wb syntaxFormula0134 syntaxFormula0136)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_wrex, syn_wex, syn_cphi, syn_clec, syn_copab, syn_csn, syn_cin,
          syn_cplc, syn_c1c, syn_cif, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0746
  have p0747 :=
    @g_cbvrexv syntaxFormula0134 syntaxFormula0136 m n (syn_cnnc) dv_cache_0028
      dv_cache_0032 dv_cache_0064 dv_cache_0065 p0747_e00_recanon
  have p0748 := @g_biimpi syntaxFormula0135 syntaxFormula0137 p0747
  have p0749 :=
    @g_syl6 syntaxFormula0040 syntaxFormula0138 syntaxFormula0135 syntaxFormula0137 p0743
      p0748
  have p0750 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0139
      hyp_wppstopgammafixedhwdndv_4
  have p0751 := @g_simpr (.classMem (.cv n) (syn_cnnc)) syntaxFormula0136
  have p0752 :=
    @g_jca syntaxFormula0139 (syn_wbr (syn_ctc C) (syn_clec) C) syntaxFormula0136 p0750
      p0751
  have p0758 := @g_a1i (.classMem (syn_ctc C) (syn_cncs)) syntaxFormula0139 p0121
  have p0762 := @g_a1i (.classMem C (syn_cncs)) syntaxFormula0139 p0124
  have p0763 := @g_simpl (.classMem (.cv n) (syn_cnnc)) syntaxFormula0136
  have p0786 := @g_pm3_2i syntaxFormula0115 syntaxFormula0056 p0685 p0043
  have p0789 := @g_eqidd syntaxFormula0116 (syn_cwppstopstep F C)
  have p0791 :=
    @g_jca syntaxFormula0116 (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C))
      syntaxFormula0116 p0789 p0687
  have p0792 :=
    @g_freceq12 (syn_cwppstopstep F C) (syn_cwppstopstep F C) (.cv p) syntaxClass0110
  have p0793 :=
    @g_syl syntaxFormula0116
      (syn_wa (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) syntaxFormula0116)
      (.classEq (syn_cfrec (syn_cwppstopstep F C) (.cv p)) syntaxClass0118) p0791 p0792
  have p0794 :=
    @g_fveq1d syntaxFormula0116 (.cv r) (syn_cfrec (syn_cwppstopstep F C) (.cv p))
      syntaxClass0118 p0793
  have p0795 :=
    @g_eleq1d syntaxFormula0116
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) syntaxClass0140
      (syn_cncs) p0794
  have p0796 :=
    @g_ralbidv syntaxFormula0116 syntaxFormula0008 syntaxFormula0141 r (syn_cnnc)
      dv_cache_0066 p0795
  have p0797 :=
    @g_imbi12d syntaxFormula0116 (syn_wbr (.cv p) (syn_clec) C) syntaxFormula0111
      syntaxFormula0009 syntaxFormula0142 p0688 p0796
  have p0798 :=
    @g_rspcva syntaxFormula0010 (.imp syntaxFormula0111 syntaxFormula0142) p
      syntaxClass0110 (syn_chwcards (syn_cvv)) dv_cache_0057 dv_cache_0019 dv_cache_0067
      p0797
  have p0799 := Nominal.mp p0786 p0798
  have p0800 := Nominal.mp p0678 p0799
  have p0801 := @g_a1i syntaxFormula0142 (.classMem (.cv n) (syn_cnnc)) p0800
  have p0802 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) syntaxFormula0142
      p0241 p0801
  have p0804 := @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) syntaxClass0118 p0305
  have p0805 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) syntaxClass0140 syntaxClass0119 (syn_cncs) p0804
  have p0806 :=
    @g_rspcva syntaxFormula0141 syntaxFormula0143 r (.cv n) (syn_cnnc) dv_cache_0037
      dv_cache_0038 dv_cache_0068 p0805
  have p0807 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) syntaxFormula0142) syntaxFormula0143 p0802
      p0806
  have p0808 :=
    @g_syl syntaxFormula0139 (.classMem (.cv n) (syn_cnnc)) syntaxFormula0143 p0763 p0807
  have p0809 :=
    @g_n_3jca syntaxFormula0139 (.classMem (syn_ctc C) (syn_cncs))
      (.classMem C (syn_cncs)) syntaxFormula0143 p0758 p0762 p0808
  have p0810 := @g_lectr (syn_ctc C) C syntaxClass0119
  have p0811 :=
    @g_syl syntaxFormula0139
      (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) syntaxFormula0143)
      (.imp syntaxFormula0144 syntaxFormula0120) p0809 p0810
  have p0812 := @g_mpd syntaxFormula0139 syntaxFormula0144 syntaxFormula0120 p0752 p0811
  have p0813 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) syntaxFormula0136 syntaxFormula0120 p0812
  have p0814 := @g_reximia syntaxFormula0136 syntaxFormula0120 n (syn_cnnc) p0813
  have p0815 :=
    @g_impbid1 syntaxFormula0040 syntaxFormula0138 syntaxFormula0137 p0749 p0814
  have p0816 :=
    @g_syl5bb syntaxFormula0145 syntaxFormula0138 syntaxFormula0040 syntaxFormula0137
      p0699 p0815
  have p0819 :=
    @g_wppreachfwdrexvndv C syntaxClass0110 n (syn_cwppstopstep F C) dv_cache_0040
      dv_cache_0059 dv_cache_0023 p0000 p0694 p0001 p0320
  have p0820 := @g_bicomi syntaxFormula0146 syntaxFormula0137 p0819
  have p0821 :=
    @g_syl6bb syntaxFormula0040 syntaxFormula0145 syntaxFormula0137 syntaxFormula0146
      p0816 p0820
  have p0823 :=
    @g_eqcomd syntaxFormula0107 syntaxClass0110 (syn_cwppgamma (syn_cwppstopstep F C) C)
      p0666
  have p0824 := @g_id syntaxFormula0147
  have p0825 :=
    @g_eleq1d syntaxFormula0147 (syn_cwppgamma (syn_cwppstopstep F C) C) syntaxClass0110
      (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)) p0824
  have p0827 :=
    @g_eleq1d syntaxFormula0147 (syn_cwppgamma (syn_cwppstopstep F C) C) syntaxClass0110
      (syn_cwppreach (syn_cwppstopstep F C) C) p0824
  have p0828 :=
    @g_bibi12d syntaxFormula0147 syntaxFormula0148 syntaxFormula0145 syntaxFormula0108
      syntaxFormula0146 p0825 p0827
  have p0829 :=
    @g_syl syntaxFormula0107 syntaxFormula0147
      (syn_wb syntaxFormula0149 syntaxFormula0150) p0823 p0828
  have p0830 :=
    @g_syl5ibrcom syntaxFormula0040 syntaxFormula0149 syntaxFormula0107 syntaxFormula0150
      p0821 p0829
  have p0831 := @g_mpi syntaxFormula0040 syntaxFormula0107 syntaxFormula0149 p0664 p0830
  have p0832 :=
    @g_mpbiri syntaxFormula0040 syntaxFormula0148 syntaxFormula0108 p0637 p0831
  have p0833 :=
    @g_jca syntaxFormula0040
      (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)))
      syntaxFormula0148 p0626 p0832
  have p0834 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppstopstep F C)
  have p0835 :=
    @g_sylibr syntaxFormula0040
      (syn_wa (syn_wa
          (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)))
        syntaxFormula0148)
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)))
      p0833 p0834
  have p0836 := @g_id (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) C))
  have p0837 :=
    @g_breq2d (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) C)) (.cv k)
      (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) p0836
  have p0838 :=
    @g_rspcv
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k))
      syntaxFormula0151 k (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) dv_cache_0069 dv_cache_0070
      dv_cache_0071 p0837
  have p0839 :=
    @g_syl syntaxFormula0040
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)))
      (.imp syntaxFormula0015 syntaxFormula0151) p0835 p0838
  have p0840 := @g_mpi syntaxFormula0040 syntaxFormula0015 syntaxFormula0151 p0413 p0839
  have p0841 := @g_jca syntaxFormula0040 syntaxFormula0068 syntaxFormula0151 p0404 p0840
  have p0856 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma (syn_cwppstopstep F C) C)
      p0036
  have p0857 := Nominal.mp p0625 p0856
  have p0876 :=
    @g_pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cncs))
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cncs)) p0857
      p0116
  have p0877 :=
    @g_sbth (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
  have p0878 := Nominal.mp p0876 p0877
  have p0879 :=
    @g_syl syntaxFormula0040 (syn_wa syntaxFormula0068 syntaxFormula0151)
      (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))
      p0841 p0878
  have p0880 :=
    @g_eqcomd syntaxFormula0040 (syn_cwppgamma (syn_cwppstopstep F C) C)
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0879
  have p0881 :=
    @g_syl5eq syntaxFormula0040 (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C))
      (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppgamma (syn_cwppstopstep F C) C) p0046 p0880
  have p0896 :=
    @g_jctil syntaxFormula0040
      (.classEq (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C))
        (syn_cwppgamma (syn_cwppstopstep F C) C))
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0881
      p0625
  exact p0896


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part066`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppstopgammahwndv (C : Class) (F : Class)
    (hyp_wppstopgammahwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopgammahwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammahwndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_k_not_C, fresh_k_not_F, or_false, not_false_eq_true])
  have p0000 := @g_wppstopstepfunsndv C F hyp_wppstopgammahwndv_1 hyp_wppstopgammahwndv_2
  have p0001 := @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv))
      (.classMem C (syn_chwcards (syn_cvv))) p0002 hyp_wppstopgammahwndv_3
  have p0004 := @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0001 dv_cache_0002
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_simpl
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_cwppcand (syn_cwppstopstep F C) C))
      (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C)
        (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0009 :=
    @g_mpbi
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_cwppcand (syn_cwppstopstep F C) C))
      (syn_wa (syn_wa
          (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
        (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
          (syn_cwppreach (syn_cwppstopstep F C) C)))
      p0007 p0008
  have p0010 :=
    @g_simpl
      (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
      (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C)
        (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0013 := Nominal.mp p0011 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end
