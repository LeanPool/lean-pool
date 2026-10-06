/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodemapf12`. -/
@[expose]
noncomputable def gFdcolcodemapf12 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapf12_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodemapf12_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodemapf12_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
  have dv_cache_0004 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0005 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0006 : q ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_B, not_false_eq_true])
  have dv_cache_0007 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0008 : r ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_B, not_false_eq_true])
  have dv_cache_0009 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0010 : Disjoint (A).fv ((synCuni (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (A).fv ((synCuni (synCuni (.cv q)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((A).fv) (((synCuni (.cv q))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint ((A).fv) (((Class.cv q)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ q } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show q ∉ (A).fv from (by exact fresh_q_not_A))))))))))
  have dv_cache_0011 : Disjoint (A).fv ((synCuni (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv ((synCuni (synCuni (.cv r)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((A).fv) (((synCuni (.cv r))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint ((A).fv) (((Class.cv r)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ r } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show r ∉ (A).fv from (by exact fresh_r_not_A))))))))))
  have dv_cache_0012 : Disjoint (B).fv ((synCuni (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (B).fv ((synCuni (synCuni (.cv q)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((B).fv) (((synCuni (.cv q))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint ((B).fv) (((Class.cv q)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ q } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show q ∉ (B).fv from (by exact fresh_q_not_B))))))))))
  have dv_cache_0013 : Disjoint (B).fv ((synCuni (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv ((synCuni (synCuni (.cv r)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((B).fv) (((synCuni (.cv r))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint ((B).fv) (((Class.cv r)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ r } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show r ∉ (B).fv from (by exact fresh_r_not_B))))))))))
  have dv_cache_0014 :
    Disjoint ((synCuni (synCuni (.cv q)))).fv ((synCuni (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint ((synCuni (synCuni (.cv q)))).fv ((synCuni (synCuni (.cv r)))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni ((synCuni (.cv q))),
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni ((synCuni (.cv r)))];
          exact
            (show Disjoint (((synCuni (.cv q))).fv) (((synCuni (.cv r))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv q)).fv) (((synCuni (.cv r))).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ q } : Finset Var)) (((synCuni (.cv r))).fv)
                          from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                            exact
                              (show Disjoint (({ q } : Finset Var)) (((Class.cv r)).fv)
                                from
                                (by
                                  rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                  exact
                                    (show
                                      Disjoint (({ q } : Finset Var))
                                        (({ r } : Finset Var))
                                      from
                                      (Finset.disjoint_singleton_left.mpr
                                        (show q ∉ ({ r } : Finset Var) from
                                          (by
                                            simpa only [Finset.mem_singleton] using
                                              (show q ≠ r from
                                                (by exact fresh_q_ne_r))))))))))))))))
  have dv_cache_0015 : Disjoint ((synCuni (synCuni (.cv q)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint ((synCuni (synCuni (.cv q)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((synCuni (.cv q))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv q)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ q } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show q ∉ (R).fv from (by exact fresh_q_not_R))))))))))
  have dv_cache_0016 : Disjoint ((synCuni (synCuni (.cv r)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint ((synCuni (synCuni (.cv r)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((synCuni (.cv r))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv r)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ r } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show r ∉ (R).fv from (by exact fresh_r_not_R))))))))))
  have dv_cache_0017 : r ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_A,
          not_false_eq_true])
  have dv_cache_0018 :
    q ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    r ∉ ((synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          fresh_r_not_R, fresh_r_not_A, fresh_r_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0021 : q ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0022 : q ∉ ((synCfdcolcodemap R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap,
          Finset.mem_union, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0023 : r ∉ ((synCfdcolcodemap R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap,
          Finset.mem_union, fresh_r_not_A, fresh_r_not_B, fresh_r_not_R, or_false,
          not_false_eq_true])
  have p0000 := @gSimpl (synWbr R (synCwe) A) (synWss A (synCpw B))
  have p0001 :=
    @gFdcolcodemapf A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf12_1
      hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0002 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWbr R (synCwe) A)
      (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B))))
      p0000 p0001
  have p0003 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfv (synCfdcolcodemap R A B) (.cv r)))
  have p0004 :=
    @gSimpl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
        (.classMem (.cv r) (synCpw1 (synCpw1 A))))
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) p0003 p0004
  have p0007 :=
    @gSimpr (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
        (.classMem (.cv r) (synCpw1 (synCpw1 A))))
  have p0008 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (.classMem (.cv r) (synCpw1 (synCpw1 A)))
  have p0009 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
        (.classMem (.cv r) (synCpw1 (synCpw1 A))))
      (.classMem (.cv q) (synCpw1 (synCpw1 A))) p0007 p0008
  have p0010 := @gFdcolcodearg A q dv_cache_0004
  have p0011 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (synWa (.classMem (synCuni (synCuni (.cv q))) A)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      p0009 p0010
  have p0012 :=
    @gSimpl (.classMem (synCuni (synCuni (.cv q))) A)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
  have p0013 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) A)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      (.classMem (synCuni (synCuni (.cv q))) A) p0011 p0012
  have p0014 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classMem (synCuni (synCuni (.cv q))) A) p0003 p0013
  have p0017 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (.classMem (.cv r) (synCpw1 (synCpw1 A)))
  have p0018 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
        (.classMem (.cv r) (synCpw1 (synCpw1 A))))
      (.classMem (.cv r) (synCpw1 (synCpw1 A))) p0007 p0017
  have p0019 := @gFdcolcodearg A r dv_cache_0005
  have p0020 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classMem (.cv r) (synCpw1 (synCpw1 A)))
      (synWa (.classMem (synCuni (synCuni (.cv r))) A)
        (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))))
      p0018 p0019
  have p0021 :=
    @gSimpl (.classMem (synCuni (synCuni (.cv r))) A)
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r))))))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (.classMem (synCuni (synCuni (.cv r))) A)
        (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))))
      (.classMem (synCuni (synCuni (.cv r))) A) p0020 p0021
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classMem (synCuni (synCuni (.cv r))) A) p0003 p0022
  have p0024 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (.classMem (synCuni (synCuni (.cv q))) A)
      (.classMem (synCuni (synCuni (.cv r))) A) p0014 p0023
  have p0025 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem (synCuni (synCuni (.cv q))) A)
        (.classMem (synCuni (synCuni (.cv r))) A))
      p0005 p0024
  have p0026 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfv (synCfdcolcodemap R A B) (.cv r)))
  have p0030 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) (synWbr R (synCwe) A)
      p0004 p0000
  have p0034 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))) p0030 p0009
  have p0035 :=
    @gFdcolcodemapval A B R q dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003
      dv_cache_0006 dv_cache_0007 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2
      hyp_fdcolcodemapf12_3
  have p0036 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      p0034 p0035
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      p0003 p0036
  have p0045 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWbr R (synCwe) A) (.classMem (.cv r) (synCpw1 (synCpw1 A))) p0030 p0018
  have p0046 :=
    @gFdcolcodemapval A B R r dv_cache_0001 dv_cache_0002 dv_cache_0005 dv_cache_0003
      dv_cache_0008 dv_cache_0009 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2
      hyp_fdcolcodemapf12_3
  have p0047 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv r) (synCpw1 (synCpw1 A))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv r))
        (synCfdcode R A B (synCuni (synCuni (.cv r)))))
      p0045 p0046
  have p0048 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv r))
        (synCfdcode R A B (synCuni (synCuni (.cv r)))))
      p0003 p0047
  have p0049 :=
    @gN3eqtr3d
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCfv (synCfdcolcodemap R A B) (.cv r))
      (synCfdcode R A B (synCuni (synCuni (.cv q))))
      (synCfdcode R A B (synCuni (synCuni (.cv r)))) p0026 p0037 p0048
  have p0050 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (synCuni (synCuni (.cv q))) A)
          (.classMem (synCuni (synCuni (.cv r))) A)))
      (.classEq (synCfdcode R A B (synCuni (synCuni (.cv q))))
        (synCfdcode R A B (synCuni (synCuni (.cv r)))))
      p0025 p0049
  have p0051 :=
    @gFdcodeinj2 A B (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r))) R
      dv_cache_0001 dv_cache_0010 dv_cache_0011 dv_cache_0002 dv_cache_0012 dv_cache_0013
      dv_cache_0003 dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_fdcolcodemapf12_1
      hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (synCuni (synCuni (.cv q))) A)
            (.classMem (synCuni (synCuni (.cv r))) A)))
        (.classEq (synCfdcode R A B (synCuni (synCuni (.cv q))))
          (synCfdcode R A B (synCuni (synCuni (.cv r))))))
      (.classEq (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r)))) p0050 p0051
  have p0053 :=
    @gSneqd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r))) p0052
  have p0054 :=
    @gSneqd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCsn (synCuni (synCuni (.cv r))))
      p0053
  have p0061 :=
    @gSimpr (.classMem (synCuni (synCuni (.cv q))) A)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
  have p0062 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) A)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0011 p0061
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0003 p0062
  have p0070 :=
    @gSimpr (.classMem (synCuni (synCuni (.cv r))) A)
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r))))))
  have p0071 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (synWa (.classMem (synCuni (synCuni (.cv r))) A)
        (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))))
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0020 p0070
  have p0072 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0003 p0071
  have p0073 :=
    @gN3eqtr4d
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
            (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))))
      (synCsn (synCsn (synCuni (synCuni (.cv q)))))
      (synCsn (synCsn (synCuni (synCuni (.cv r))))) (.cv q) (.cv r) p0054 p0063 p0072
  have p0074 :=
    @gEx
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 A)))
          (.classMem (.cv r) (synCpw1 (synCpw1 A)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfv (synCfdcolcodemap R A B) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0073
  have p0075 :=
    @gRalrimivva (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (.imp (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfv (synCfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))
      q r (synCpw1 (synCpw1 A)) (synCpw1 (synCpw1 A)) dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 p0074
  have p0076 :=
    @gJca (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B))))
      (synWral q (synCpw1 (synCpw1 A)) (synWral r (synCpw1 (synCpw1 A)) (.imp
            (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
              (synCfv (synCfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))))
      p0002 p0075
  have p0077 :=
    @gDff13 q r (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B)))
      (synCfdcolcodemap R A B) dv_cache_0021 dv_cache_0017 dv_cache_0022 dv_cache_0023
      dv_cache_0020
  have p0078_e00_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B)))) (synWa
          (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
            (synCpw (synCpw (synCfdif R A B)))) (synWral q (synCpw1 (synCpw1 A))
            (synWral r (synCpw1 (synCpw1 A)) (.imp
                (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
                  (synCfv (synCfdcolcodemap R A B) (.cv r)))
                (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synCfdcolcodemap synCres
          synCpw1 synCpw
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif]
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
      p0077
  have p0078 :=
    @gA1i
      (synWb (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B)))) (synWa
          (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
            (synCpw (synCpw (synCfdif R A B)))) (synWral q (synCpw1 (synCpw1 A))
            (synWral r (synCpw1 (synCpw1 A)) (.imp
                (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
                  (synCfv (synCfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))))))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) p0078_e00_recanon
  have p0079 :=
    @gMpbird (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B))))
      (synWa (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B)))) (synWral q (synCpw1 (synCpw1 A))
          (synWral r (synCpw1 (synCpw1 A)) (.imp
              (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
                (synCfv (synCfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r))))))
      p0076 p0078
  exact p0079

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodecardle2`. -/
@[expose]
noncomputable def gFdcolcodecardle2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodecardle2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodecardle2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodecardle2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec)
          (synCnc (synCpw (synCpw (synCfdif R A B)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let f : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
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
  have fresh_f_ne_z : f ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_f : z ≠ f := Ne.symm fresh_f_ne_z
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
  have dv_cache_0004 : f ∉ ((synCfdcolcodemap R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap,
          Finset.mem_union, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    f ∉
      ((synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, or_false, not_false_eq_true])
  have dv_cache_0006 :
    f ∉ ((Wff.classEq (.cv z) (synCpw (synCpw (synCfdif R A B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_z, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_f_not_A,
          not_false_eq_true])
  have dv_cache_0008 : f ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_z, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCpw (synCpw (synCfdif R A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((synWb (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec)
            (synCnc (synCpw (synCpw (synCfdif R A B))))) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCpw1 A))
              (synCpw (synCpw (synCfdif R A B))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, fresh_z_ne_f,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gFdcolcodemapf12 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0001 := @gSimpl (synWbr R (synCwe) A) (synWss A (synCpw B))
  have p0002 :=
    @gFdcolcodemapex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0003 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWbr R (synCwe) A) (.classMem (synCfdcolcodemap R A B) (synCvv)) p0001 p0002
  have p0004 :=
    @gF1eq1 (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B))) (.cv f)
      (synCfdcolcodemap R A B)
  have p0005 :=
    @gSpcegv
      (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B))))
      (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B))))
      f (synCfdcolcodemap R A B) (synCvv) dv_cache_0004 dv_cache_0005 p0004
  have p0006 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (.classMem (synCfdcolcodemap R A B) (synCvv))
      (.imp (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B)))) (synWex f
          (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B))))))
      p0003 p0005
  have p0007 :=
    @gMpd (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWf1 (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B))))
      (synWex f
        (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B)))))
      p0000 p0006
  have p0009 :=
    @gFdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodecardle2_1
      hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0010 := @gPwexg (synCfdif R A B) (synCvv)
  have p0011 :=
    @gSyl (synWbr R (synCwe) A) (.classMem (synCfdif R A B) (synCvv))
      (.classMem (synCpw (synCfdif R A B)) (synCvv)) p0009 p0010
  have p0012 := @gPwexg (synCpw (synCfdif R A B)) (synCvv)
  have p0013 :=
    @gSyl (synWbr R (synCwe) A) (.classMem (synCpw (synCfdif R A B)) (synCvv))
      (.classMem (synCpw (synCpw (synCfdif R A B))) (synCvv)) p0011 p0012
  have p0014 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWbr R (synCwe) A) (.classMem (synCpw (synCpw (synCfdif R A B))) (synCvv))
      p0001 p0013
  have p0015 := @gId (.classEq (.cv z) (synCpw (synCpw (synCfdif R A B))))
  have p0016 :=
    @gNceqd (.classEq (.cv z) (synCpw (synCpw (synCfdif R A B)))) (.cv z)
      (synCpw (synCpw (synCfdif R A B))) p0015
  have p0017 :=
    @gBreq2d (.classEq (.cv z) (synCpw (synCpw (synCfdif R A B)))) (synCnc (.cv z))
      (synCnc (synCpw (synCpw (synCfdif R A B)))) (synCnc (synCpw1 (synCpw1 A)))
      (synClec) p0016
  have p0018 :=
    @gF1eq3 (.cv z) (synCpw (synCpw (synCfdif R A B))) (synCpw1 (synCpw1 A)) (.cv f)
  have p0019 :=
    @gExbidv (.classEq (.cv z) (synCpw (synCpw (synCfdif R A B))))
      (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (.cv z))
      (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B)))) f
      dv_cache_0006 p0018
  have p0020 :=
    @gBibi12d (.classEq (.cv z) (synCpw (synCpw (synCfdif R A B))))
      (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec) (synCnc (.cv z)))
      (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec)
        (synCnc (synCpw (synCpw (synCfdif R A B)))))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (.cv z)))
      (synWex f
        (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B)))))
      p0017 p0019
  have p0021 := @gPw1ex A hyp_fdcolcodecardle2_2
  have p0022 := @gPw1ex (synCpw1 A) p0021
  have p0023 := @gVex z
  have p0024 :=
    @gNclenc (synCpw1 (synCpw1 A)) (.cv z) f dv_cache_0007 dv_cache_0008 p0022 p0023
  have p0025 :=
    @gVtoclg
      (synWb (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec) (synCnc (.cv z)))
        (synWex f (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (.cv z))))
      (synWb (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec)
          (synCnc (synCpw (synCpw (synCfdif R A B))))) (synWex f
          (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B))))))
      z (synCpw (synCpw (synCfdif R A B))) (synCvv) dv_cache_0009 dv_cache_0010 p0020
      p0024
  have p0026 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (.classMem (synCpw (synCpw (synCfdif R A B))) (synCvv))
      (synWb (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec)
          (synCnc (synCpw (synCpw (synCfdif R A B))))) (synWex f
          (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B))))))
      p0014 p0025
  have p0027 :=
    @gMpbird (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWbr (synCnc (synCpw1 (synCpw1 A))) (synClec)
        (synCnc (synCpw (synCpw (synCfdif R A B)))))
      (synWex f
        (synWf1 (.cv f) (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B)))))
      p0007 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodetc2nc`. -/
@[expose]
noncomputable def gFdcolcodetc2nc (A : Class)
    (hyp_fdcolcodetc2nc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synCnc A))) (synCnc (synCpw1 (synCpw1 A)))) :=
  by
  have p0000 := @gTcnc A hyp_fdcolcodetc2nc_1
  have p0001 := @gTceq (synCtc (synCnc A)) (synCnc (synCpw1 A))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gPw1ex A hyp_fdcolcodetc2nc_1
  have p0004 := @gTcnc (synCpw1 A) p0003
  have p0005 :=
    @gEqtri (synCtc (synCtc (synCnc A))) (synCtc (synCnc (synCpw1 A)))
      (synCnc (synCpw1 (synCpw1 A))) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodetc2le2`. -/
@[expose]
noncomputable def gFdcolcodetc2le2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodetc2le2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodetc2le2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodetc2le2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWbr (synCtc (synCtc (synCnc A))) (synClec)
          (synCnc (synCpw (synCpw (synCfdif R A B)))))) :=
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
  have p0000 := @gFdcolcodetc2nc A hyp_fdcolcodetc2le2_2
  have p0001 :=
    @gA1i (.classEq (synCtc (synCtc (synCnc A))) (synCnc (synCpw1 (synCpw1 A))))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) p0000
  have p0002 :=
    @gFdcolcodecardle2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdcolcodetc2le2_1 hyp_fdcolcodetc2le2_2 hyp_fdcolcodetc2le2_3
  have p0003 :=
    @gEqbrtrd (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synCtc (synCtc (synCnc A))) (synCnc (synCpw1 (synCpw1 A)))
      (synCnc (synCpw (synCpw (synCfdif R A B)))) (synClec) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hwcodesex`. -/
@[expose]
noncomputable def gHwcodesex (A : Class)
    (hyp_hwcodesex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synChwcodes A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcodes A))
  have p0001 := @gWeex
  have p0002 := @gVvex
  have p0003 := @gPwex A hyp_hwcodesex_1
  have p0004 := @gXpex (synCvv) (synCpw A) p0002 p0003
  have p0005 := @gInex (synCwe) (synCxp (synCvv) (synCpw A)) p0001 p0004
  have p0006 :=
    @gEqeltri (synChwcodes A) (synCin (synCwe) (synCxp (synCvv) (synCpw A)))
      (synCvv) p0000 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwcodesexg`. -/
@[expose]
noncomputable def gHwcodesexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synChwcodes A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcodes A))
  have p0001 := @gWeex
  have p0002 := @gA1i (.classMem (synCwe) (synCvv)) (.classMem A V) p0001
  have p0003 := @gVvex
  have p0004 := @gA1i (.classMem (synCvv) (synCvv)) (.classMem A V) p0003
  have p0005 := @gPwexg A V
  have p0006 :=
    @gJca (.classMem A V) (.classMem (synCvv) (synCvv))
      (.classMem (synCpw A) (synCvv)) p0004 p0005
  have p0007 := @gXpexg (synCvv) (synCpw A) (synCvv) (synCvv)
  have p0008 :=
    @gSyl (.classMem A V)
      (synWa (.classMem (synCvv) (synCvv)) (.classMem (synCpw A) (synCvv)))
      (.classMem (synCxp (synCvv) (synCpw A)) (synCvv)) p0006 p0007
  have p0009 :=
    @gJca (.classMem A V) (.classMem (synCwe) (synCvv))
      (.classMem (synCxp (synCvv) (synCpw A)) (synCvv)) p0002 p0008
  have p0010 := @gInexg (synCwe) (synCxp (synCvv) (synCpw A)) (synCvv) (synCvv)
  have p0011 :=
    @gSyl (.classMem A V)
      (synWa (.classMem (synCwe) (synCvv))
        (.classMem (synCxp (synCvv) (synCpw A)) (synCvv)))
      (.classMem (synCin (synCwe) (synCxp (synCvv) (synCpw A))) (synCvv)) p0009
      p0010
  have p0012 :=
    @gSyl5eqel (.classMem A V) (synChwcodes A)
      (synCin (synCwe) (synCxp (synCvv) (synCpw A))) (synCvv) p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_elhwcodes`. -/
@[expose]
noncomputable def gElhwcodes (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_elhwcodes_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_elhwcodes_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop R D) (synChwcodes A))
        (synWa (synWbr R (synCwe) D) (synWss D A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcodes A))
  have p0001 :=
    @gEleq2i (synChwcodes A) (synCin (synCwe) (synCxp (synCvv) (synCpw A)))
      (synCop R D) p0000
  have p0002 := @gElin (synCop R D) (synCwe) (synCxp (synCvv) (synCpw A))
  have p0003 := (Nominal.biimpRefl (synWbr R (synCwe) D))
  have p0004 :=
    @gBicomi (synWbr R (synCwe) D) (.classMem (synCop R D) (synCwe)) p0003
  have p0005 := @gOpelxp R D (synCvv) (synCpw A)
  have p0006 :=
    @gMpbiran (.classMem (synCop R D) (synCxp (synCvv) (synCpw A)))
      (.classMem R (synCvv)) (.classMem D (synCpw A)) hyp_elhwcodes_1 p0005
  have p0007 := @gElpw D A hyp_elhwcodes_2
  have p0008 :=
    @gBitri (.classMem (synCop R D) (synCxp (synCvv) (synCpw A)))
      (.classMem D (synCpw A)) (synWss D A) p0006 p0007
  have p0009 :=
    @gAnbi12i (.classMem (synCop R D) (synCwe)) (synWbr R (synCwe) D)
      (.classMem (synCop R D) (synCxp (synCvv) (synCpw A))) (synWss D A) p0004 p0008
  have p0010 :=
    @gBitri (.classMem (synCop R D) (synCin (synCwe) (synCxp (synCvv) (synCpw A))))
      (synWa (.classMem (synCop R D) (synCwe))
        (.classMem (synCop R D) (synCxp (synCvv) (synCpw A))))
      (synWa (synWbr R (synCwe) D) (synWss D A)) p0002 p0009
  have p0011 :=
    @gBitri (.classMem (synCop R D) (synChwcodes A))
      (.classMem (synCop R D) (synCin (synCwe) (synCxp (synCvv) (synCpw A))))
      (synWa (synWbr R (synCwe) D) (synWss D A)) p0001 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_brhwiso`. -/
@[expose]
noncomputable def gBrhwiso (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_h : h ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v)
    (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwiso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
          (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))) :=
  by
  have dv_cache_0001 : h ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
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
  have dv_cache_0004 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact dv_h_u))
  have dv_cache_0005 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact dv_h_v))
  have dv_cache_0006 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have p0000 := (Nominal.biimpRefl (synWbr (.cv u) (synChwiso A) (.cv v)))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfHwiso v u A h
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @gEleq2i (synChwiso A)
      (synCopab u v (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))))
      (synCop (.cv u) (.cv v)) p0001
  have p0003 :=
    @gOpabid
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      u v
  have p0004 :=
    @gBitri (.classMem (synCop (.cv u) (.cv v)) (synChwiso A))
      (.classMem (synCop (.cv u) (.cv v)) (synCopab u v (synWa
            (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
            (synWex h
              (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0002 p0003
  have p0005 :=
    @gBitri (synWbr (.cv u) (synChwiso A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synChwiso A))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_brhwisoany`. -/
@[expose]
noncomputable def gBrhwisoany (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwiso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
          (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ ({ h } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_h : x ≠ h := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_x : h ≠ x := Ne.symm fresh_x_ne_h
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_h : y ≠ h := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : h ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0005 : h ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ y from (by exact fresh_h_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : h ∉ ((Wff.classEq (.cv x) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, dv_h_u, or_false, not_false_eq_true])
  have dv_cache_0008 : h ∉ ((Wff.classEq (.cv y) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_y, dv_h_v, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv v)).fv :=
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
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A,
          fresh_x_ne_v, fresh_x_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_A,
          fresh_y_ne_v, fresh_y_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (synWbr (.cv u) (synChwiso A) (.cv v)))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfHwiso y x A h
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @gEleq2i (synChwiso A)
      (synCopab x y (synWa (synWa (.classMem (.cv x) (synChwcodes A))
            (.classMem (.cv y) (synChwcodes A))) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
              (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y))))))
      (synCop (.cv u) (.cv v)) p0001
  have p0003 := @gVex u
  have p0004 := @gVex v
  have p0005 := @gEleq1 (.cv x) (.cv u) (synChwcodes A)
  have p0006 :=
    @gAnbi1d (.classEq (.cv x) (.cv u)) (.classMem (.cv x) (synChwcodes A))
      (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)) p0005
  have p0007 := @gFveq2 (.cv x) (.cv u) (synC1st)
  have p0008 :=
    @gIsoeq2 (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y))
      (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
      (synCfv (synC1st) (.cv u)) (.cv h)
  have p0009 :=
    @gSyl (.classEq (.cv x) (.cv u))
      (.classEq (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv u)))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y))))
      p0007 p0008
  have p0010 := @gFveq2 (.cv x) (.cv u) (synC2nd)
  have p0011 :=
    @gIsoeq4 (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y))
      (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (.cv y)) (.cv h)
  have p0012 :=
    @gSyl (.classEq (.cv x) (.cv u))
      (.classEq (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv u)))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y))))
      p0010 p0011
  have p0013 :=
    @gBitrd (.classEq (.cv x) (.cv u))
      (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
      p0009 p0012
  have p0014 :=
    @gExbidv (.classEq (.cv x) (.cv u))
      (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
      h dv_cache_0007 p0013
  have p0015 :=
    @gAnbi12d (.classEq (.cv x) (.cv u))
      (synWa (.classMem (.cv x) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y))))
      p0006 p0014
  have p0016 := @gEleq1 (.cv y) (.cv v) (synChwcodes A)
  have p0017 :=
    @gAnbi2d (.classEq (.cv y) (.cv v)) (.classMem (.cv y) (synChwcodes A))
      (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)) p0016
  have p0018 := @gFveq2 (.cv y) (.cv v) (synC1st)
  have p0019 :=
    @gIsoeq3 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
      (synCfv (synC1st) (.cv v)) (.cv h)
  have p0020 :=
    @gSyl (.classEq (.cv y) (.cv v))
      (.classEq (synCfv (synC1st) (.cv y)) (synCfv (synC1st) (.cv v)))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y))))
      p0018 p0019
  have p0021 := @gFveq2 (.cv y) (.cv v) (synC2nd)
  have p0022 :=
    @gIsoeq5 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y))
      (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (.cv v)) (.cv h)
  have p0023 :=
    @gSyl (.classEq (.cv y) (.cv v))
      (.classEq (synCfv (synC2nd) (.cv y)) (synCfv (synC2nd) (.cv v)))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
        (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0021 p0022
  have p0024 :=
    @gBitrd (.classEq (.cv y) (.cv v))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0020 p0023
  have p0025 :=
    @gExbidv (.classEq (.cv y) (.cv v))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      h dv_cache_0008 p0024
  have p0026 :=
    @gAnbi12d (.classEq (.cv y) (.cv v))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0017 p0025
  have p0027 :=
    @gSylan9bb (.classEq (.cv x) (.cv u))
      (synWa (synWa (.classMem (.cv x) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
            (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv y))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv y)))))
      (.classEq (.cv y) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0015 p0026
  have p0028 :=
    @gOpelopaba
      (synWa (synWa (.classMem (.cv x) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
            (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      x y (.cv u) (.cv v) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0006 p0003 p0004 p0027
  have p0029 :=
    @gBitri (.classMem (synCop (.cv u) (.cv v)) (synChwiso A))
      (.classMem (synCop (.cv u) (.cv v)) (synCopab x y (synWa
            (synWa (.classMem (.cv x) (synChwcodes A)) (.classMem (.cv y) (synChwcodes A)))
            (synWex h
              (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
                (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0002 p0028
  have p0030 :=
    @gBitri (synWbr (.cv u) (synChwiso A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synChwiso A))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0000 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_hwisosymi`. -/
@[expose]
noncomputable def gHwisosymi (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWbr (.cv u) (synChwiso A) (.cv v))
        (synWbr (.cv v) (synChwiso A) (.cv u))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let g : Var := freshVar proofSupport 0
  let h : Var := freshVar proofSupport 1
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_v : g ≠ v := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_u : g ≠ u := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_h_ne_v : h ≠ v := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_g_ne_h : g ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have dv_cache_0001 : h ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
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
  have dv_cache_0004 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0005 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0006 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0007 : g ∉ ((synCcnv (.cv h))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_h,
          not_false_eq_true])
  have dv_cache_0008 :
    g ∉
      ((synWiso (synCcnv (.cv h)) (synCfv (synC1st) (.cv v))
          (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv v))
          (synCfv (synC2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_v, fresh_g_ne_u, fresh_g_ne_h,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    h ∉
      ((synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_h_ne_v, fresh_h_ne_u,
          fresh_h_ne_g, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : g ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_A, not_false_eq_true])
  have dv_cache_0011 : g ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0012 : g ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show g ≠ u from (by exact fresh_g_ne_u))
  have dv_cache_0013 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show v ≠ u from (by exact Ne.symm dv_u_v))
  have p0000 :=
    @gBrhwiso v u A h dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gBiimpi (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
  have p0003 :=
    @gAncom (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A))
  have p0004 :=
    @gBiimpi
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
      p0003
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
      p0002 p0004
  have p0006 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
  have p0007 :=
    @gIsocnv (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (.cv h)
  have p0008 := @gVex h
  have p0009 := @gCnvex (.cv h) p0008
  have p0010 :=
    @gIsoeq1 (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u)) (synCcnv (.cv h)) (.cv g)
  have p0011 :=
    @gSpcev
      (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
        (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u)))
      (synWiso (synCcnv (.cv h)) (synCfv (synC1st) (.cv v))
        (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u)))
      g (synCcnv (.cv h)) dv_cache_0007 dv_cache_0008 p0009 p0010
  have p0012 :=
    @gSyl
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (synCcnv (.cv h)) (synCfv (synC1st) (.cv v))
        (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u)))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u))))
      p0007 p0011
  have p0013 :=
    @gExlimiv
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u))))
      h dv_cache_0009 p0012
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u))))
      p0006 p0013
  have p0015 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u))))
      p0005 p0014
  have p0016 :=
    @gSyl (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u)))))
      p0001 p0015
  have p0017 :=
    @gBrhwiso u v A g dv_cache_0010 dv_cache_0003 dv_cache_0002 dv_cache_0011
      dv_cache_0012 dv_cache_0013
  have p0018 :=
    @gBiimpri (synWbr (.cv v) (synChwiso A) (.cv u))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u)))))
      p0017
  have p0019 :=
    @gSyl (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv v) (synChwiso A) (.cv u)) p0016 p0018
  exact p0019


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwisotri`. -/
@[expose]
noncomputable def gHwisotri (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_u_v : u ≠ v) (dv_u_w : u ≠ w)
    (dv_v_w : v ≠ w) :
    Nominal.NPrf
      (.imp (synWa (synWbr (.cv u) (synChwiso A) (.cv v))
          (synWbr (.cv v) (synChwiso A) (.cv w))) (synWbr (.cv u) (synChwiso A) (.cv w))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let h : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  let g : Var := freshVar proofSupport 2
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_w : h ≠ w := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_ne_w : f ≠ w := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_v : f ≠ v := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_g_ne_w : g ≠ w := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_g_ne_v : g ≠ v := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_g_ne_u : g ≠ u := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h_ne_f : h ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_h : f ≠ h := Ne.symm fresh_h_ne_f
  have fresh_h_ne_g : h ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_g_ne_h : g ≠ h := Ne.symm fresh_h_ne_g
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
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
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0006 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0007 : g ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_A, not_false_eq_true])
  have dv_cache_0008 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0009 : g ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0010 : g ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show g ≠ w from (by exact fresh_g_ne_w))
  have dv_cache_0011 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show v ≠ w from (by exact dv_v_w))
  have dv_cache_0012 :
    g ∉
      ((synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_u, fresh_g_ne_v, fresh_g_ne_f,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    f ∉
      ((synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_w, fresh_f_ne_g,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : h ∉ ((synCcom (.cv g) (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_g, fresh_h_ne_f, or_false, not_false_eq_true])
  have dv_cache_0015 :
    h ∉
      ((synWiso (synCcom (.cv g) (.cv f)) (synCfv (synC1st) (.cv u))
          (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv u))
          (synCfv (synC2nd) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, fresh_h_ne_w, fresh_h_ne_g, fresh_h_ne_f,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    f ∉
      ((synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_u, fresh_f_ne_w,
          fresh_f_ne_h, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 :
    g ∉
      ((synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_ne_u, fresh_g_ne_w,
          fresh_g_ne_h, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0019 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0020 : h ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show h ≠ w from (by exact fresh_h_ne_w))
  have dv_cache_0021 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show u ≠ w from (by exact dv_u_w))
  have p0000 :=
    @gBrhwiso v u A f dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gBiimpi (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0000
  have p0002 :=
    @gBrhwiso w v A g dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011
  have p0003 :=
    @gBiimpi (synWbr (.cv v) (synChwiso A) (.cv w))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      p0002
  have p0004 :=
    @gAnim12i (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWbr (.cv v) (synChwiso A) (.cv w))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      p0001 p0003
  have p0005 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
  have p0006 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
  have p0007 :=
    @gSimpl (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (.classMem (.cv u) (synChwcodes A)) p0006 p0007
  have p0009 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (.classMem (.cv u) (synChwcodes A)) p0005 p0008
  have p0010 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
  have p0011 :=
    @gSimpl
      (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))
  have p0012 :=
    @gSimpr (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A))
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
      (.classMem (.cv w) (synChwcodes A)) p0011 p0012
  have p0014 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      (.classMem (.cv w) (synChwcodes A)) p0010 p0013
  have p0015 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)) p0009
      p0014
  have p0017 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0005 p0017
  have p0020 :=
    @gSimpr
      (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))
      p0010 p0020
  have p0022 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))
      p0018 p0021
  have p0023 :=
    @gEeanv
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
        (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))
      f g dv_cache_0012 dv_cache_0013
  have p0024 :=
    @gBiimpri
      (synWex f (synWex g (synWa
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
            (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWex f
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) (synWex g
          (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      p0023
  have p0025 :=
    @gIsotr (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC2nd) (.cv w)) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w)) (.cv g) (.cv f)
  have p0026 := @gVex g
  have p0027 := @gVex f
  have p0028 := @gCoex (.cv g) (.cv f) p0026 p0027
  have p0029 :=
    @gIsoeq1 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w)) (synCcom (.cv g) (.cv f))
      (.cv h)
  have p0030 :=
    @gSpcev
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w)))
      (synWiso (synCcom (.cv g) (.cv f)) (synCfv (synC1st) (.cv u))
        (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w)))
      h (synCcom (.cv g) (.cv f)) dv_cache_0014 dv_cache_0015 p0028 p0029
  have p0031 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))
      (synWiso (synCcom (.cv g) (.cv f)) (synCfv (synC1st) (.cv u))
        (synCfv (synC1st) (.cv w)) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))
      p0025 p0030
  have p0032 :=
    @gExlimivv
      (synWa (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))
      f g dv_cache_0016 dv_cache_0017 p0031
  have p0033 :=
    @gSyl
      (synWa (synWex f
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) (synWex g
          (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      (synWex f (synWex g (synWa
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
            (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))
      p0024 p0032
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWex f
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) (synWex g
          (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))
      p0022 p0033
  have p0035 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w))))
      p0015 p0034
  have p0036 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWa
          (synWa (.classMem (.cv v) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
          (synWex g (synWiso (.cv g) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv w))
              (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv w))))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w)))))
      p0004 p0035
  have p0037 :=
    @gBrhwiso w u A h dv_cache_0018 dv_cache_0002 dv_cache_0008 dv_cache_0019
      dv_cache_0020 dv_cache_0021
  have p0038 :=
    @gBiimpri (synWbr (.cv u) (synChwiso A) (.cv w))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w)))))
      p0037
  have p0039 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv w) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv w))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv w)))))
      (synWbr (.cv u) (synChwiso A) (.cv w)) p0036 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_hwisorefl`. -/
@[expose]
noncomputable def gHwisorefl (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcodes A)) (synWbr (.cv u) (synChwiso A) (.cv u))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_u : h ≠ u := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ ((synCres (synCid) (synCfv (synC2nd) (.cv u)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    h ∉
      ((synWiso (synCres (synCid) (synCfv (synC2nd) (.cv u)))
          (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0004 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have p0000 := @gPm424 (.classMem (.cv u) (synChwcodes A))
  have p0001 :=
    @gBiimpi (.classMem (.cv u) (synChwcodes A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
      p0000
  have p0002 := @gIsoid (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0003 := @gIdex
  have p0004 := @gFvex (.cv u) (synC2nd)
  have p0005 := @gResex (synCid) (synCfv (synC2nd) (.cv u)) p0003 p0004
  have p0006 :=
    @gIsoeq1 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
      (synCres (synCid) (synCfv (synC2nd) (.cv u))) (.cv h)
  have p0007 :=
    @gSpcev
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synWiso (synCres (synCid) (synCfv (synC2nd) (.cv u)))
        (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      h (synCres (synCid) (synCfv (synC2nd) (.cv u))) dv_cache_0001 dv_cache_0002
      p0005 p0006
  have p0008 := Nominal.mp p0002 p0007
  have p0009 :=
    @gA1i
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcodes A)) p0008
  have p0010 :=
    @gJca (.classMem (.cv u) (synChwcodes A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0001 p0009
  have p0011 := @gBrhwisoany u u A h dv_cache_0003 dv_cache_0004 dv_cache_0004
  have p0012 :=
    @gBiimpri (synWbr (.cv u) (synChwiso A) (.cv u))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0011
  have p0013 :=
    @gSyl (.classMem (.cv u) (synChwcodes A))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv u) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwiso A) (.cv u)) p0010 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_hwrelsex`. -/
@[expose]
noncomputable def gHwrelsex : Nominal.NPrf (.classMem (synChwrels) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwrels))
  have p0001 := @gN1stex
  have p0002 := @gCrossex
  have p0003 := @gN2ndex
  have p0005 := @gTxpex (synC2nd) (synC2nd) p0003 p0003
  have p0006 := @gCoex (synCcross) (synCtxp (synC2nd) (synC2nd)) p0002 p0005
  have p0007 :=
    @gTxpex (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) p0001
      p0006
  have p0008 :=
    @gCnvex
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))) p0007
  have p0009 := @gSsetex
  have p0010 :=
    @gImaex
      (synCcnv (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
      (synCsset) p0008 p0009
  have p0011 :=
    @gEqeltri (synChwrels)
      (synCima (synCcnv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
        (synCsset))
      (synCvv) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hwbijex`. -/
@[expose]
noncomputable def gHwbijex : Nominal.NPrf (.classMem (synChwbij) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwbij))
  have p0001 := @gFunsex
  have p0002 := @gSwapex
  have p0003 := @gImageex (synCswap) p0002
  have p0004 := @gCnvex (synCimage (synCswap)) p0003
  have p0006 := @gImaex (synCcnv (synCimage (synCswap))) (synCfuns) p0004 p0001
  have p0007 :=
    @gInex (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)) p0001
      p0006
  have p0008 :=
    @gEqeltri (synChwbij)
      (synCin (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)))
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hwgenex`. -/
@[expose]
noncomputable def gHwgenex : Nominal.NPrf (.classMem (synChwgen) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwgen))
  have p0001 := @gN2ndex
  have p0002 := @gDomfnex
  have p0003 := @gN1stex
  have p0004 := @gCoex (synCdomfn) (synC1st) p0002 p0003
  have p0005 := @gTxpex (synC2nd) (synCcom (synCdomfn) (synC1st)) p0001 p0004
  have p0006 := (Nominal.classEqRefl (synChwtrn))
  have p0007 := @gComposeex
  have p0011 := @gTxpex (synC1st) (synC2nd) p0003 p0001
  have p0012 := @gCoex (synCcompose) (synCtxp (synC1st) (synC2nd)) p0007 p0011
  have p0013 := @gSwapex
  have p0014 := @gImageex (synCswap) p0013
  have p0016 := @gCoex (synCimage (synCswap)) (synC1st) p0014 p0003
  have p0017 :=
    @gTxpex (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
      (synCcom (synCimage (synCswap)) (synC1st)) p0012 p0016
  have p0018 :=
    @gCoex (synCcompose)
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
      p0007 p0017
  have p0019 :=
    @gEqeltri (synChwtrn)
      (synCcom (synCcompose)
        (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))))
      (synCvv) p0006 p0018
  have p0020 := @gRanfnex
  have p0022 := @gCoex (synCranfn) (synC1st) p0020 p0003
  have p0023 := @gTxpex (synChwtrn) (synCcom (synCranfn) (synC1st)) p0019 p0022
  have p0024 :=
    @gTxpex (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) p0005 p0023
  have p0025 :=
    @gEqeltri (synChwgen)
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
      (synCvv) p0000 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_hwcnex`. -/
@[expose]
noncomputable def gHwcnex (A : Class)
    (hyp_hwcnex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synChwcn A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcn A))
  have p0001 := @gHwcodesex A hyp_hwcnex_1
  have p0002 := (Nominal.classEqRefl (synChwrels))
  have p0003 := @gN1stex
  have p0004 := @gCrossex
  have p0005 := @gN2ndex
  have p0007 := @gTxpex (synC2nd) (synC2nd) p0005 p0005
  have p0008 := @gCoex (synCcross) (synCtxp (synC2nd) (synC2nd)) p0004 p0007
  have p0009 :=
    @gTxpex (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) p0003
      p0008
  have p0010 :=
    @gCnvex
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))) p0009
  have p0011 := @gSsetex
  have p0012 :=
    @gImaex
      (synCcnv (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
      (synCsset) p0010 p0011
  have p0013 :=
    @gEqeltri (synChwrels)
      (synCima (synCcnv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
        (synCsset))
      (synCvv) p0002 p0012
  have p0014 := @gInex (synChwcodes A) (synChwrels) p0001 p0013
  have p0015 :=
    @gEqeltri (synChwcn A) (synCin (synChwcodes A) (synChwrels)) (synCvv) p0000
      p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hwnisoex`. -/
@[expose]
noncomputable def gHwnisoex (A : Class)
    (hyp_hwnisoex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synChwniso A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwniso A))
  have p0001 := @gHwgenex
  have p0002 := @gHwbijex
  have p0003 := @gVvex
  have p0004 := @gXpex (synChwbij) (synCvv) p0002 p0003
  have p0005 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0001 p0004
  have p0006 := @gHwcnex A hyp_hwnisoex_1
  have p0008 := @gXpex (synChwcn A) (synChwcn A) p0006 p0006
  have p0009 :=
    @gInex (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCxp (synChwcn A) (synChwcn A)) p0005 p0008
  have p0010 :=
    @gEqeltri (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synCvv) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnordex`. -/
@[expose]
noncomputable def gHnordex (A : Class)
    (hyp_hnordex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synChnord A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnord A))
  have p0001 := @gHwnisoex A hyp_hnordex_1
  have p0002 := @gHwcnex A hyp_hnordex_1
  have p0003 := @gQsex (synChwcn A) (synChwniso A) p0001 p0002
  have p0004 :=
    @gEqeltri (synChnord A) (synCqs (synChwcn A) (synChwniso A)) (synCvv) p0000
      p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elhwrrels`. -/
@[expose]
noncomputable def gElhwrrels (u : Var) :
    Nominal.NPrf
      (synWb (.classMem (.cv u) (synChwrels)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwrels))
  have p0001 :=
    @gEleq2i (synChwrels)
      (synCima (synCcnv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
        (synCsset))
      (.cv u) p0000
  have p0002 := @gN1stfo
  have p0003 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gFncross
  have p0006 := @gN2ndfo
  have p0007 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0008 := Nominal.mp p0006 p0007
  have p0012 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (synWfn (synC2nd) (synCvv)) p0008 p0008
  have p0013 := @gFntxp (synCvv) (synCvv) (synC2nd) (synC2nd)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @gInidm (synCvv)
  have p0016 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC2nd) (synC2nd))
      p0015
  have p0017 :=
    @gMpbi (synWfn (synCtxp (synC2nd) (synC2nd)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synC2nd)) (synCvv)) p0014 p0016
  have p0018 := @gSsv (synCrn (synCtxp (synC2nd) (synC2nd)))
  have p0019 :=
    @gN3pm32i (synWfn (synCcross) (synCvv))
      (synWfn (synCtxp (synC2nd) (synC2nd)) (synCvv))
      (synWss (synCrn (synCtxp (synC2nd) (synC2nd))) (synCvv)) p0005 p0017 p0018
  have p0020 := @gFnco (synCvv) (synCvv) (synCcross) (synCtxp (synC2nd) (synC2nd))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @gPm32i (synWfn (synC1st) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (synCvv)) p0004
      p0021
  have p0023 :=
    @gFntxp (synCvv) (synCvv) (synC1st)
      (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
  have p0024 := Nominal.mp p0022 p0023
  have p0026 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))) p0015
  have p0027 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (synCvv))
      p0024 p0026
  have p0028 :=
    @gElpreima (synCvv) (.cv u) (synCsset)
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @gVex u
  have p0031 :=
    @gBiantrur (.classMem (.cv u) (synCvv))
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      p0030
  have p0032 :=
    @gBicomi
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      (synWa (.classMem (.cv u) (synCvv)) (.classMem (synCfv
            (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
            (.cv u)) (synCsset)))
      p0031
  have p0033 :=
    @gBitri
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (synWa (.classMem (.cv u) (synCvv)) (.classMem (synCfv
            (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
            (.cv u)) (synCsset)))
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      p0029 p0032
  have p0034 := @gEqid (synCfv (synC1st) (.cv u))
  have p0039 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (.classMem (.cv u) (synCvv)) p0004 p0030
  have p0040 := @gFnbrfvb (synCvv) (.cv u) (synCfv (synC1st) (.cv u)) (synC1st)
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @gMpbi (.classEq (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u)))
      (synWbr (.cv u) (synC1st) (synCfv (synC1st) (.cv u))) p0034 p0041
  have p0043 :=
    @gEqid (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
  have p0062 :=
    @gPm32i (synWfn (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (synCvv))
      (.classMem (.cv u) (synCvv)) p0021 p0030
  have p0063 :=
    @gFnbrfvb (synCvv) (.cv u)
      (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
  have p0064 := Nominal.mp p0062 p0063
  have p0065 :=
    @gMpbi
      (.classEq (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      (synWbr (.cv u) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      p0043 p0064
  have p0066 :=
    @gPm32i (synWbr (.cv u) (synC1st) (synCfv (synC1st) (.cv u)))
      (synWbr (.cv u) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      p0042 p0065
  have p0067 :=
    @gTrtxp (.cv u) (synCfv (synC1st) (.cv u))
      (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
  have p0068 :=
    @gMpbir
      (synWbr (.cv u)
        (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (synCop (synCfv (synC1st) (.cv u))
          (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))))
      (synWa (synWbr (.cv u) (synC1st) (synCfv (synC1st) (.cv u)))
        (synWbr (.cv u) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
          (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))))
      p0066 p0067
  have p0095 :=
    @gFnfun (synCvv)
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
  have p0096 := Nominal.mp p0027 p0095
  have p0097 :=
    @gFunbrfv (.cv u)
      (synCop (synCfv (synC1st) (.cv u))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
  have p0098 := Nominal.mp p0096 p0097
  have p0099 := Nominal.mp p0068 p0098
  have p0113 :=
    @gPm32i (synWfn (synCtxp (synC2nd) (synC2nd)) (synCvv))
      (.classMem (.cv u) (synCvv)) p0017 p0030
  have p0114 := @gFvco2 (synCvv) (.cv u) (synCcross) (synCtxp (synC2nd) (synC2nd))
  have p0115 := Nominal.mp p0113 p0114
  have p0116 := @gEqid (synCfv (synC2nd) (.cv u))
  have p0121 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (.cv u) (synCvv)) p0008 p0030
  have p0122 := @gFnbrfvb (synCvv) (.cv u) (synCfv (synC2nd) (.cv u)) (synC2nd)
  have p0123 := Nominal.mp p0121 p0122
  have p0124 :=
    @gMpbi (.classEq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u))) p0116 p0123
  have p0134 :=
    @gPm32i (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u))) p0124 p0124
  have p0135 :=
    @gTrtxp (.cv u) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) (synC2nd)
      (synC2nd)
  have p0136 :=
    @gMpbir
      (synWbr (.cv u) (synCtxp (synC2nd) (synC2nd))
        (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWa (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u))))
      p0134 p0135
  have p0149 := @gFnfun (synCvv) (synCtxp (synC2nd) (synC2nd))
  have p0150 := Nominal.mp p0017 p0149
  have p0151 :=
    @gFunbrfv (.cv u) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCtxp (synC2nd) (synC2nd))
  have p0152 := Nominal.mp p0150 p0151
  have p0153 := Nominal.mp p0136 p0152
  have p0154 :=
    @gFveq2i (synCfv (synCtxp (synC2nd) (synC2nd)) (.cv u))
      (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) (synCcross)
      p0153
  have p0155 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCfv (synCcross) (synCfv (synCtxp (synC2nd) (synC2nd)) (.cv u)))
      (synCfv (synCcross) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0115 p0154
  have p0156 :=
    (Nominal.classEqRefl
      (synCo (synCfv (synC2nd) (.cv u)) (synCcross) (synCfv (synC2nd) (.cv u))))
  have p0157 := @gFvex (.cv u) (synC2nd)
  have p0159 :=
    @gPm32i (.classMem (synCfv (synC2nd) (.cv u)) (synCvv))
      (.classMem (synCfv (synC2nd) (.cv u)) (synCvv)) p0157 p0157
  have p0160 :=
    @gOvcross (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) (synCvv)
      (synCvv)
  have p0161 := Nominal.mp p0159 p0160
  have p0162 :=
    @gEqtr3i
      (synCo (synCfv (synC2nd) (.cv u)) (synCcross) (synCfv (synC2nd) (.cv u)))
      (synCfv (synCcross) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0156 p0161
  have p0163 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCfv (synCcross) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0155 p0162
  have p0164 :=
    @gOpeq2i (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) p0163
  have p0165 :=
    @gEqtri
      (synCfv (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (.cv u))
      (synCop (synCfv (synC1st) (.cv u))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      (synCop (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0099 p0164
  have p0166 :=
    @gEleq1i
      (synCfv (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (.cv u))
      (synCop (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCsset) p0165
  have p0167 :=
    @gBitri
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      (.classMem (synCop (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))) (synCsset))
      p0033 p0166
  have p0168 :=
    (Nominal.biimpRefl (synWbr (synCfv (synC1st) (.cv u)) (synCsset)
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
  have p0169 := @gFvex (.cv u) (synC1st)
  have p0172 :=
    @gXpex (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) p0157 p0157
  have p0173 :=
    @gBrsset (synCfv (synC1st) (.cv u))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0169 p0172
  have p0174 :=
    @gBitr3i
      (.classMem (synCop (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))) (synCsset))
      (synWbr (synCfv (synC1st) (.cv u)) (synCsset)
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0168 p0173
  have p0175 :=
    @gBitri
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (.classMem (synCop (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))) (synCsset))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0167 p0174
  have p0176 :=
    @gBitri (.classMem (.cv u) (synChwrels))
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0001 p0175
  exact p0176

/-- Checked nominal proof certificate identified upstream as `g_elhwcn`. -/
@[expose]
noncomputable def gElhwcn (u : Var) (A : Class) :
    Nominal.NPrf
      (synWb (.classMem (.cv u) (synChwcn A)) (synWa (.classMem (.cv u) (synChwcodes A))
          (synWss (synCfv (synC1st) (.cv u))
            (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcn A))
  have p0001 :=
    @gEleq2i (synChwcn A) (synCin (synChwcodes A) (synChwrels)) (.cv u) p0000
  have p0002 := @gElin (.cv u) (synChwcodes A) (synChwrels)
  have p0003 := (Nominal.classEqRefl (synChwrels))
  have p0004 :=
    @gEleq2i (synChwrels)
      (synCima (synCcnv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))))
        (synCsset))
      (.cv u) p0003
  have p0005 := @gN1stfo
  have p0006 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gFncross
  have p0009 := @gN2ndfo
  have p0010 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0011 := Nominal.mp p0009 p0010
  have p0015 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (synWfn (synC2nd) (synCvv)) p0011 p0011
  have p0016 := @gFntxp (synCvv) (synCvv) (synC2nd) (synC2nd)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @gInidm (synCvv)
  have p0019 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC2nd) (synC2nd))
      p0018
  have p0020 :=
    @gMpbi (synWfn (synCtxp (synC2nd) (synC2nd)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synC2nd)) (synCvv)) p0017 p0019
  have p0021 := @gSsv (synCrn (synCtxp (synC2nd) (synC2nd)))
  have p0022 :=
    @gN3pm32i (synWfn (synCcross) (synCvv))
      (synWfn (synCtxp (synC2nd) (synC2nd)) (synCvv))
      (synWss (synCrn (synCtxp (synC2nd) (synC2nd))) (synCvv)) p0008 p0020 p0021
  have p0023 := @gFnco (synCvv) (synCvv) (synCcross) (synCtxp (synC2nd) (synC2nd))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gPm32i (synWfn (synC1st) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (synCvv)) p0007
      p0024
  have p0026 :=
    @gFntxp (synCvv) (synCvv) (synC1st)
      (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
  have p0027 := Nominal.mp p0025 p0026
  have p0029 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))) p0018
  have p0030 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (synCvv))
      p0027 p0029
  have p0031 :=
    @gElpreima (synCvv) (.cv u) (synCsset)
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := @gVex u
  have p0034 :=
    @gBiantrur (.classMem (.cv u) (synCvv))
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      p0033
  have p0035 :=
    @gBicomi
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      (synWa (.classMem (.cv u) (synCvv)) (.classMem (synCfv
            (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
            (.cv u)) (synCsset)))
      p0034
  have p0036 :=
    @gBitri
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (synWa (.classMem (.cv u) (synCvv)) (.classMem (synCfv
            (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
            (.cv u)) (synCsset)))
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      p0032 p0035
  have p0037 := @gEqid (synCfv (synC1st) (.cv u))
  have p0042 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (.classMem (.cv u) (synCvv)) p0007 p0033
  have p0043 := @gFnbrfvb (synCvv) (.cv u) (synCfv (synC1st) (.cv u)) (synC1st)
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @gMpbi (.classEq (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv u)))
      (synWbr (.cv u) (synC1st) (synCfv (synC1st) (.cv u))) p0037 p0044
  have p0046 :=
    @gEqid (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
  have p0065 :=
    @gPm32i (synWfn (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (synCvv))
      (.classMem (.cv u) (synCvv)) p0024 p0033
  have p0066 :=
    @gFnbrfvb (synCvv) (.cv u)
      (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
  have p0067 := Nominal.mp p0065 p0066
  have p0068 :=
    @gMpbi
      (.classEq (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      (synWbr (.cv u) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      p0046 p0067
  have p0069 :=
    @gPm32i (synWbr (.cv u) (synC1st) (synCfv (synC1st) (.cv u)))
      (synWbr (.cv u) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      p0045 p0068
  have p0070 :=
    @gTrtxp (.cv u) (synCfv (synC1st) (.cv u))
      (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
  have p0071 :=
    @gMpbir
      (synWbr (.cv u)
        (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (synCop (synCfv (synC1st) (.cv u))
          (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))))
      (synWa (synWbr (.cv u) (synC1st) (synCfv (synC1st) (.cv u)))
        (synWbr (.cv u) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd)))
          (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))))
      p0069 p0070
  have p0098 :=
    @gFnfun (synCvv)
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
  have p0099 := Nominal.mp p0030 p0098
  have p0100 :=
    @gFunbrfv (.cv u)
      (synCop (synCfv (synC1st) (.cv u))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
  have p0101 := Nominal.mp p0099 p0100
  have p0102 := Nominal.mp p0071 p0101
  have p0116 :=
    @gPm32i (synWfn (synCtxp (synC2nd) (synC2nd)) (synCvv))
      (.classMem (.cv u) (synCvv)) p0020 p0033
  have p0117 := @gFvco2 (synCvv) (.cv u) (synCcross) (synCtxp (synC2nd) (synC2nd))
  have p0118 := Nominal.mp p0116 p0117
  have p0119 := @gEqid (synCfv (synC2nd) (.cv u))
  have p0124 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (.cv u) (synCvv)) p0011 p0033
  have p0125 := @gFnbrfvb (synCvv) (.cv u) (synCfv (synC2nd) (.cv u)) (synC2nd)
  have p0126 := Nominal.mp p0124 p0125
  have p0127 :=
    @gMpbi (.classEq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u))) p0119 p0126
  have p0137 :=
    @gPm32i (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u))) p0127 p0127
  have p0138 :=
    @gTrtxp (.cv u) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) (synC2nd)
      (synC2nd)
  have p0139 :=
    @gMpbir
      (synWbr (.cv u) (synCtxp (synC2nd) (synC2nd))
        (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWa (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv u) (synC2nd) (synCfv (synC2nd) (.cv u))))
      p0137 p0138
  have p0152 := @gFnfun (synCvv) (synCtxp (synC2nd) (synC2nd))
  have p0153 := Nominal.mp p0020 p0152
  have p0154 :=
    @gFunbrfv (.cv u) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCtxp (synC2nd) (synC2nd))
  have p0155 := Nominal.mp p0153 p0154
  have p0156 := Nominal.mp p0139 p0155
  have p0157 :=
    @gFveq2i (synCfv (synCtxp (synC2nd) (synC2nd)) (.cv u))
      (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) (synCcross)
      p0156
  have p0158 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCfv (synCcross) (synCfv (synCtxp (synC2nd) (synC2nd)) (.cv u)))
      (synCfv (synCcross) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0118 p0157
  have p0159 :=
    (Nominal.classEqRefl
      (synCo (synCfv (synC2nd) (.cv u)) (synCcross) (synCfv (synC2nd) (.cv u))))
  have p0160 := @gFvex (.cv u) (synC2nd)
  have p0162 :=
    @gPm32i (.classMem (synCfv (synC2nd) (.cv u)) (synCvv))
      (.classMem (synCfv (synC2nd) (.cv u)) (synCvv)) p0160 p0160
  have p0163 :=
    @gOvcross (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) (synCvv)
      (synCvv)
  have p0164 := Nominal.mp p0162 p0163
  have p0165 :=
    @gEqtr3i
      (synCo (synCfv (synC2nd) (.cv u)) (synCcross) (synCfv (synC2nd) (.cv u)))
      (synCfv (synCcross) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0159 p0164
  have p0166 :=
    @gEqtri (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCfv (synCcross) (synCop (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0158 p0165
  have p0167 :=
    @gOpeq2i (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) p0166
  have p0168 :=
    @gEqtri
      (synCfv (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (.cv u))
      (synCop (synCfv (synC1st) (.cv u))
        (synCfv (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))) (.cv u)))
      (synCop (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0102 p0167
  have p0169 :=
    @gEleq1i
      (synCfv (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
        (.cv u))
      (synCop (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCsset) p0168
  have p0170 :=
    @gBitri
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (.classMem (synCfv
          (synCtxp (synC1st) (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))
          (.cv u)) (synCsset))
      (.classMem (synCop (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))) (synCsset))
      p0036 p0169
  have p0171 :=
    (Nominal.biimpRefl (synWbr (synCfv (synC1st) (.cv u)) (synCsset)
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
  have p0172 := @gFvex (.cv u) (synC1st)
  have p0175 :=
    @gXpex (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)) p0160 p0160
  have p0176 :=
    @gBrsset (synCfv (synC1st) (.cv u))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0172 p0175
  have p0177 :=
    @gBitr3i
      (.classMem (synCop (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))) (synCsset))
      (synWbr (synCfv (synC1st) (.cv u)) (synCsset)
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0171 p0176
  have p0178 :=
    @gBitri
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (.classMem (synCop (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))) (synCsset))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0170 p0177
  have p0179 :=
    @gBitri (.classMem (.cv u) (synChwrels))
      (.classMem (.cv u) (synCima (synCcnv (synCtxp (synC1st)
              (synCcom (synCcross) (synCtxp (synC2nd) (synC2nd))))) (synCsset)))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0004 p0178
  have p0180 :=
    @gAnbi2i (.classMem (.cv u) (synChwrels))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcodes A)) p0179
  have p0181 :=
    @gBitri (.classMem (.cv u) (synCin (synChwcodes A) (synChwrels)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv u) (synChwrels)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0002 p0180
  have p0182 :=
    @gBitri (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synCin (synChwcodes A) (synChwrels)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0001 p0181
  exact p0182

/-- Checked nominal proof certificate identified upstream as `g_elhwbij`. -/
@[expose]
noncomputable def gElhwbij (f : Var) :
    Nominal.NPrf
      (synWb (.classMem (.cv f) (synChwbij))
        (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))) :=
  by
  let proofSupport : Finset Var := ({ f } : Finset Var)
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_f : g ≠ f := by
    intro h
    exact fresh_g (Finset.mem_singleton.mpr h)
  have dv_cache_0001 : g ∉ ((Class.cv f)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_f, not_false_eq_true])
  have dv_cache_0002 : g ∉ ((synCcnv (synCimage (synCswap)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : g ∉ ((synCfuns)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((synCcnv (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_f,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChwbij))
  have p0001 :=
    @gEleq2i (synChwbij)
      (synCin (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)))
      (.cv f) p0000
  have p0002 :=
    @gElin (.cv f) (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns))
  have p0003 :=
    @gElima g (.cv f) (synCcnv (synCimage (synCswap))) (synCfuns) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0004 := @gBrcnv (.cv g) (.cv f) (synCimage (synCswap))
  have p0005 := @gVex f
  have p0006 := @gVex g
  have p0007 := @gBrimage (.cv f) (.cv g) (synCswap) p0005 p0006
  have p0008 :=
    @gBitri (synWbr (.cv g) (synCcnv (synCimage (synCswap))) (.cv f))
      (synWbr (.cv f) (synCimage (synCswap)) (.cv g))
      (.classEq (.cv g) (synCima (synCswap) (.cv f))) p0004 p0007
  have p0009 := @gDfcnv2 (.cv f)
  have p0010 := @gEqeq2i (synCcnv (.cv f)) (synCima (synCswap) (.cv f)) (.cv g) p0009
  have p0011 :=
    @gBicomi (.classEq (.cv g) (synCcnv (.cv f)))
      (.classEq (.cv g) (synCima (synCswap) (.cv f))) p0010
  have p0012 :=
    @gBitri (synWbr (.cv g) (synCcnv (synCimage (synCswap))) (.cv f))
      (.classEq (.cv g) (synCima (synCswap) (.cv f)))
      (.classEq (.cv g) (synCcnv (.cv f))) p0008 p0011
  have p0013 :=
    @gRexbii (synWbr (.cv g) (synCcnv (synCimage (synCswap))) (.cv f))
      (.classEq (.cv g) (synCcnv (.cv f))) g (synCfuns) p0012
  have p0014 :=
    @gBitri
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)))
      (synWrex g (synCfuns) (synWbr (.cv g) (synCcnv (synCimage (synCswap))) (.cv f)))
      (synWrex g (synCfuns) (.classEq (.cv g) (synCcnv (.cv f)))) p0003 p0013
  have p0015 := @gRisset g (synCcnv (.cv f)) (synCfuns) dv_cache_0004 dv_cache_0003
  have p0016 :=
    @gBicomi (.classMem (synCcnv (.cv f)) (synCfuns))
      (synWrex g (synCfuns) (.classEq (.cv g) (synCcnv (.cv f)))) p0015
  have p0017 :=
    @gBitri
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)))
      (synWrex g (synCfuns) (.classEq (.cv g) (synCcnv (.cv f))))
      (.classMem (synCcnv (.cv f)) (synCfuns)) p0014 p0016
  have p0018 :=
    @gAnbi2i
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synCswap))) (synCfuns)))
      (.classMem (synCcnv (.cv f)) (synCfuns)) (.classMem (.cv f) (synCfuns)) p0017
  have p0019 :=
    @gBitri
      (.classMem (.cv f)
        (synCin (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns))))
      (synWa (.classMem (.cv f) (synCfuns))
        (.classMem (.cv f) (synCima (synCcnv (synCimage (synCswap))) (synCfuns))))
      (synWa (.classMem (.cv f) (synCfuns)) (.classMem (synCcnv (.cv f)) (synCfuns)))
      p0002 p0018
  have p0021 := @gElfuns (.cv f) p0005
  have p0023 := @gCnvex (.cv f) p0005
  have p0024 := @gElfuns (synCcnv (.cv f)) p0023
  have p0025 :=
    @gAnbi12i (.classMem (.cv f) (synCfuns)) (synWfun (.cv f))
      (.classMem (synCcnv (.cv f)) (synCfuns)) (synWfun (synCcnv (.cv f))) p0021 p0024
  have p0026 :=
    @gBitri
      (.classMem (.cv f)
        (synCin (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns))))
      (synWa (.classMem (.cv f) (synCfuns)) (.classMem (synCcnv (.cv f)) (synCfuns)))
      (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))) p0019 p0025
  have p0027 :=
    @gBitri (.classMem (.cv f) (synChwbij))
      (.classMem (.cv f)
        (synCin (synCfuns) (synCima (synCcnv (synCimage (synCswap))) (synCfuns))))
      (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))) p0001 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_elhnord`. -/
@[expose]
noncomputable def gElhnord (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (_dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x)
    (hyp_elhnord_1 : Nominal.NPrf (.classMem (.cv x) (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synChnord A)) (synWrex u (synChwcn A)
          (.classEq (.cv x) (synCec (.cv u) (synChwniso A))))) :=
  by
  have dv_cache_0001 : u ∉ ((synChwcn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_u,
          not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_u_x,
          not_false_eq_true])
  have dv_cache_0003 : u ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_u,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChnord A))
  have p0001 :=
    @gEleq2i (synChnord A) (synCqs (synChwcn A) (synChwniso A)) (.cv x) p0000
  have p0002 :=
    @gElqs u (synChwcn A) (.cv x) (synChwniso A) dv_cache_0001 dv_cache_0002
      dv_cache_0003 hyp_elhnord_1
  have p0003 :=
    @gBitri (.classMem (.cv x) (synChnord A))
      (.classMem (.cv x) (synCqs (synChwcn A) (synChwniso A)))
      (synWrex u (synChwcn A) (.classEq (.cv x) (synCec (.cv u) (synChwniso A))))
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hwnisoclasselhnord`. -/
@[expose]
noncomputable def gHwnisoclasselhnord (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv)
    (hyp_hwnisoclasselhnord_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classMem (synCec (.cv u) (synChwniso A)) (synChnord A))) :=
  by
  have p0000 := @gHwnisoex A hyp_hwnisoclasselhnord_1
  have p0001 := @gEcelqsi (synChwcn A) (.cv u) (synChwniso A) p0000
  have p0002 := (Nominal.classEqRefl (synChnord A))
  have p0003 :=
    @gEleq2i (synChnord A) (synCqs (synChwcn A) (synChwniso A))
      (synCec (.cv u) (synChwniso A)) p0002
  have p0004 :=
    @gSylibr (.classMem (.cv u) (synChwcn A))
      (.classMem (synCec (.cv u) (synChwniso A)) (synCqs (synChwcn A) (synChwniso A)))
      (.classMem (synCec (.cv u) (synChwniso A)) (synChnord A)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_imageswapfn`. -/
@[expose]
noncomputable def gImageswapfn :
    Nominal.NPrf (synWfn (synCimage (synCswap)) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCima (synCswap) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : a ∉ ((synCimage (synCswap))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((synCimage (synCswap))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((synCmpt x (synCvv) (synCima (synCswap) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((synCmpt x (synCvv) (synCima (synCswap) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0008 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 := @gSwapex
  have p0001 := @gVex x
  have p0002 := @gImaex (synCswap) (.cv x) p0000 p0001
  have p0003 := @gEqid (synCmpt x (synCvv) (synCima (synCswap) (.cv x)))
  have p0004 :=
    @gFnmpti x (synCvv) (synCima (synCswap) (.cv x))
      (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) dv_cache_0001 p0002 p0003
  have p0005 := @gVex a
  have p0006 := @gVex b
  have p0007 := @gBrimage (.cv a) (.cv b) (synCswap) p0005 p0006
  have p0014 :=
    @gPm32i (synWfn (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (synCvv))
      (.classMem (.cv a) (synCvv)) p0004 p0005
  have p0015 :=
    @gFnbrfvb (synCvv) (.cv a) (.cv b)
      (synCmpt x (synCvv) (synCima (synCswap) (.cv x)))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gBicomi
      (.classEq (synCfv (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv a)) (.cv b))
      (synWbr (.cv a) (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv b))
      p0016
  have p0019 := @gImaeq2 (.cv x) (.cv a) (synCswap)
  have p0023 := @gImaex (synCswap) (.cv a) p0000 p0005
  have p0024 :=
    @gFvmpt x (.cv a) (synCima (synCswap) (.cv x)) (synCima (synCswap) (.cv a))
      (synCvv) (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) dv_cache_0002
      dv_cache_0003 dv_cache_0001 p0019 p0003 p0023
  have p0025 := Nominal.mp p0005 p0024
  have p0026 :=
    @gEqeq1i (synCfv (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv a))
      (synCima (synCswap) (.cv a)) (.cv b) p0025
  have p0027 :=
    @gBitri
      (synWbr (.cv a) (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv b))
      (.classEq (synCfv (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv a)) (.cv b))
      (.classEq (synCima (synCswap) (.cv a)) (.cv b)) p0017 p0026
  have p0028 := @gEqcom (synCima (synCswap) (.cv a)) (.cv b)
  have p0029 :=
    @gBitri
      (synWbr (.cv a) (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv b))
      (.classEq (synCima (synCswap) (.cv a)) (.cv b))
      (.classEq (.cv b) (synCima (synCswap) (.cv a))) p0027 p0028
  have p0030 :=
    @gBitr4i (synWbr (.cv a) (synCimage (synCswap)) (.cv b))
      (.classEq (.cv b) (synCima (synCswap) (.cv a)))
      (synWbr (.cv a) (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (.cv b))
      p0007 p0029
  have p0031 :=
    @gEqbrriv a b (synCimage (synCswap))
      (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 p0030
  have p0032 :=
    @gFneq1i (synCvv) (synCimage (synCswap))
      (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) p0031
  have p0033 :=
    @gMpbir (synWfn (synCimage (synCswap)) (synCvv))
      (synWfn (synCmpt x (synCvv) (synCima (synCswap) (.cv x))) (synCvv)) p0004
      p0032
  exact p0033

/-- Checked nominal proof certificate identified upstream as `g_imageswapval`. -/
@[expose]
noncomputable def gImageswapval (f : Var) :
    Nominal.NPrf
      (.classEq (synCfv (synCimage (synCswap)) (.cv f)) (synCcnv (.cv f))) :=
  by
  have p0000 := @gEqid (synCima (synCswap) (.cv f))
  have p0001 := @gVex f
  have p0002 := @gSwapex
  have p0004 := @gImaex (synCswap) (.cv f) p0002 p0001
  have p0005 := @gBrimage (.cv f) (synCima (synCswap) (.cv f)) (synCswap) p0001 p0004
  have p0006 :=
    @gMpbir (synWbr (.cv f) (synCimage (synCswap)) (synCima (synCswap) (.cv f)))
      (.classEq (synCima (synCswap) (.cv f)) (synCima (synCswap) (.cv f))) p0000 p0005
  have p0007 := @gImageswapfn
  have p0009 :=
    @gPm32i (synWfn (synCimage (synCswap)) (synCvv)) (.classMem (.cv f) (synCvv))
      p0007 p0001
  have p0010 :=
    @gFnbrfvb (synCvv) (.cv f) (synCima (synCswap) (.cv f)) (synCimage (synCswap))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gMpbir
      (.classEq (synCfv (synCimage (synCswap)) (.cv f)) (synCima (synCswap) (.cv f)))
      (synWbr (.cv f) (synCimage (synCswap)) (synCima (synCswap) (.cv f))) p0006
      p0011
  have p0013 := @gDfcnv2 (.cv f)
  have p0014 :=
    @gEqtr4i (synCfv (synCimage (synCswap)) (.cv f)) (synCima (synCswap) (.cv f))
      (synCcnv (.cv f)) p0012 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part033`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwtrnfn`. -/
@[expose]
noncomputable def gHwtrnfn : Nominal.NPrf (synWfn (synChwtrn) (synCvv)) :=
  by
  have p0000 := @gComposefn
  have p0002 := @gN1stfo
  have p0003 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gN2ndfo
  have p0006 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synC2nd) (synCvv)) p0004 p0007
  have p0009 := @gFntxp (synCvv) (synCvv) (synC1st) (synC2nd)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gInidm (synCvv)
  have p0012 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synC2nd))
      p0011
  have p0013 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synC2nd)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synC2nd)) (synCvv)) p0010 p0012
  have p0014 := @gSsv (synCrn (synCtxp (synC1st) (synC2nd)))
  have p0015 :=
    @gN3pm32i (synWfn (synCcompose) (synCvv))
      (synWfn (synCtxp (synC1st) (synC2nd)) (synCvv))
      (synWss (synCrn (synCtxp (synC1st) (synC2nd))) (synCvv)) p0000 p0013 p0014
  have p0016 :=
    @gFnco (synCvv) (synCvv) (synCcompose) (synCtxp (synC1st) (synC2nd))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @gImageswapfn
  have p0022 := @gSsv (synCrn (synC1st))
  have p0023 :=
    @gN3pm32i (synWfn (synCimage (synCswap)) (synCvv))
      (synWfn (synC1st) (synCvv)) (synWss (synCrn (synC1st)) (synCvv)) p0018 p0004
      p0022
  have p0024 := @gFnco (synCvv) (synCvv) (synCimage (synCswap)) (synC1st)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gPm32i
      (synWfn (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synC1st)) (synCvv)) p0017 p0025
  have p0027 :=
    @gFntxp (synCvv) (synCvv)
      (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
      (synCcom (synCimage (synCswap)) (synC1st))
  have p0028 := Nominal.mp p0026 p0027
  have p0030 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
      p0011
  have p0031 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      p0028 p0030
  have p0032 :=
    @gSsv
      (synCrn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))))
  have p0033 :=
    @gN3pm32i (synWfn (synCcompose) (synCvv))
      (synWfn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      (synWss (synCrn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st)))) (synCvv))
      p0000 p0031 p0032
  have p0034 :=
    @gFnco (synCvv) (synCvv) (synCcompose)
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
  have p0035 := Nominal.mp p0033 p0034
  have p0036 := (Nominal.classEqRefl (synChwtrn))
  have p0037 :=
    @gFneq1i (synCvv) (synChwtrn)
      (synCcom (synCcompose)
        (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))))
      p0036
  have p0038 :=
    @gBicomi (synWfn (synChwtrn) (synCvv))
      (synWfn (synCcom (synCcompose)
          (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st)))) (synCvv))
      p0037
  have p0039 :=
    @gMpbi
      (synWfn (synCcom (synCcompose)
          (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st)))) (synCvv))
      (synWfn (synChwtrn) (synCvv)) p0035 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_hwtrnval`. -/
@[expose]
noncomputable def gHwtrnval (R : Class) (f : Var)
    (hyp_hwtrnval_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChwtrn) (synCop (.cv f) R))
        (synCcom (synCcom (.cv f) R) (synCcnv (.cv f)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwtrn))
  have p0001 :=
    @gFveq1i (synCop (.cv f) R) (synChwtrn)
      (synCcom (synCcompose)
        (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))))
      p0000
  have p0002 := @gComposefn
  have p0003 := @gN1stfo
  have p0004 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gN2ndfo
  have p0007 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synC2nd) (synCvv)) p0005 p0008
  have p0010 := @gFntxp (synCvv) (synCvv) (synC1st) (synC2nd)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @gInidm (synCvv)
  have p0013 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synC2nd))
      p0012
  have p0014 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synC2nd)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synC2nd)) (synCvv)) p0011 p0013
  have p0015 := @gSsv (synCrn (synCtxp (synC1st) (synC2nd)))
  have p0016 :=
    @gN3pm32i (synWfn (synCcompose) (synCvv))
      (synWfn (synCtxp (synC1st) (synC2nd)) (synCvv))
      (synWss (synCrn (synCtxp (synC1st) (synC2nd))) (synCvv)) p0002 p0014 p0015
  have p0017 :=
    @gFnco (synCvv) (synCvv) (synCcompose) (synCtxp (synC1st) (synC2nd))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gImageswapfn
  have p0023 := @gSsv (synCrn (synC1st))
  have p0024 :=
    @gN3pm32i (synWfn (synCimage (synCswap)) (synCvv))
      (synWfn (synC1st) (synCvv)) (synWss (synCrn (synC1st)) (synCvv)) p0019 p0005
      p0023
  have p0025 := @gFnco (synCvv) (synCvv) (synCimage (synCswap)) (synC1st)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gPm32i
      (synWfn (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synC1st)) (synCvv)) p0018 p0026
  have p0028 :=
    @gFntxp (synCvv) (synCvv)
      (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
      (synCcom (synCimage (synCswap)) (synC1st))
  have p0029 := Nominal.mp p0027 p0028
  have p0031 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
      p0012
  have p0032 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      p0029 p0031
  have p0033 := @gVex f
  have p0034 := @gOpex (.cv f) R p0033 hyp_hwtrnval_1
  have p0035 :=
    @gPm32i
      (synWfn (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0032 p0034
  have p0036 :=
    @gFvco2 (synCvv) (synCop (.cv f) R) (synCcompose)
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @gEqid
      (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCop (.cv f) R))
  have p0058 :=
    @gPm32i
      (synWfn (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0018 p0034
  have p0059 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R)
      (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCop (.cv f) R))
      (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
  have p0060 := Nominal.mp p0058 p0059
  have p0061 :=
    @gMpbi
      (.classEq (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCop (.cv f) R))
        (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCop (.cv f) R)))
      p0038 p0060
  have p0062 :=
    @gEqid (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
  have p0073 :=
    @gPm32i (synWfn (synCcom (synCimage (synCswap)) (synC1st)) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0026 p0034
  have p0074 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R)
      (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
      (synCcom (synCimage (synCswap)) (synC1st))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @gMpbi
      (.classEq (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
        (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCimage (synCswap)) (synC1st))
        (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R)))
      p0062 p0075
  have p0077 :=
    @gPm32i
      (synWbr (synCop (.cv f) R) (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCimage (synCswap)) (synC1st))
        (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R)))
      p0061 p0076
  have p0078 :=
    @gTrtxp (synCop (.cv f) R)
      (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCop (.cv f) R))
      (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
      (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
      (synCcom (synCimage (synCswap)) (synC1st))
  have p0079 :=
    @gMpbir
      (synWbr (synCop (.cv f) R)
        (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCop
          (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCop (.cv f) R))
          (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))))
      (synWa (synWbr (synCop (.cv f) R)
          (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCop (.cv f) R)))
        (synWbr (synCop (.cv f) R) (synCcom (synCimage (synCswap)) (synC1st))
          (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))))
      p0077 p0078
  have p0111 :=
    @gFnfun (synCvv)
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
  have p0112 := Nominal.mp p0032 p0111
  have p0113 :=
    @gFunbrfv (synCop (.cv f) R)
      (synCop (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCop (.cv f) R))
        (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R)))
      (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
        (synCcom (synCimage (synCswap)) (synC1st)))
  have p0114 := Nominal.mp p0112 p0113
  have p0115 := Nominal.mp p0079 p0114
  have p0130 :=
    @gPm32i (synWfn (synCtxp (synC1st) (synC2nd)) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0014 p0034
  have p0131 :=
    @gFvco2 (synCvv) (synCop (.cv f) R) (synCcompose) (synCtxp (synC1st) (synC2nd))
  have p0132 := Nominal.mp p0130 p0131
  have p0133 := @gEqid (synCfv (synC1st) (synCop (.cv f) R))
  have p0139 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (.classMem (synCop (.cv f) R) (synCvv))
      p0005 p0034
  have p0140 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R) (synCfv (synC1st) (synCop (.cv f) R))
      (synC1st)
  have p0141 := Nominal.mp p0139 p0140
  have p0142 :=
    @gMpbi
      (.classEq (synCfv (synC1st) (synCop (.cv f) R))
        (synCfv (synC1st) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synC1st) (synCfv (synC1st) (synCop (.cv f) R)))
      p0133 p0141
  have p0143 := @gEqid (synCfv (synC2nd) (synCop (.cv f) R))
  have p0149 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (synCop (.cv f) R) (synCvv))
      p0008 p0034
  have p0150 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R) (synCfv (synC2nd) (synCop (.cv f) R))
      (synC2nd)
  have p0151 := Nominal.mp p0149 p0150
  have p0152 :=
    @gMpbi
      (.classEq (synCfv (synC2nd) (synCop (.cv f) R))
        (synCfv (synC2nd) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synC2nd) (synCfv (synC2nd) (synCop (.cv f) R)))
      p0143 p0151
  have p0153 :=
    @gPm32i
      (synWbr (synCop (.cv f) R) (synC1st) (synCfv (synC1st) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synC2nd) (synCfv (synC2nd) (synCop (.cv f) R)))
      p0142 p0152
  have p0154 :=
    @gTrtxp (synCop (.cv f) R) (synCfv (synC1st) (synCop (.cv f) R))
      (synCfv (synC2nd) (synCop (.cv f) R)) (synC1st) (synC2nd)
  have p0155 :=
    @gMpbir
      (synWbr (synCop (.cv f) R) (synCtxp (synC1st) (synC2nd))
        (synCop (synCfv (synC1st) (synCop (.cv f) R))
          (synCfv (synC2nd) (synCop (.cv f) R))))
      (synWa (synWbr (synCop (.cv f) R) (synC1st) (synCfv (synC1st) (synCop (.cv f) R)))
        (synWbr (synCop (.cv f) R) (synC2nd) (synCfv (synC2nd) (synCop (.cv f) R))))
      p0153 p0154
  have p0168 := @gFnfun (synCvv) (synCtxp (synC1st) (synC2nd))
  have p0169 := Nominal.mp p0014 p0168
  have p0170 :=
    @gFunbrfv (synCop (.cv f) R)
      (synCop (synCfv (synC1st) (synCop (.cv f) R))
        (synCfv (synC2nd) (synCop (.cv f) R)))
      (synCtxp (synC1st) (synC2nd))
  have p0171 := Nominal.mp p0169 p0170
  have p0172 := Nominal.mp p0155 p0171
  have p0174 := @gOpfv1st (.cv f) R p0033 hyp_hwtrnval_1
  have p0176 := @gOpfv2nd (.cv f) R p0033 hyp_hwtrnval_1
  have p0177 :=
    @gOpeq12i (synCfv (synC1st) (synCop (.cv f) R)) (.cv f)
      (synCfv (synC2nd) (synCop (.cv f) R)) R p0174 p0176
  have p0178 :=
    @gEqtri (synCfv (synCtxp (synC1st) (synC2nd)) (synCop (.cv f) R))
      (synCop (synCfv (synC1st) (synCop (.cv f) R))
        (synCfv (synC2nd) (synCop (.cv f) R)))
      (synCop (.cv f) R) p0172 p0177
  have p0179 :=
    @gFveq2i (synCfv (synCtxp (synC1st) (synC2nd)) (synCop (.cv f) R))
      (synCop (.cv f) R) (synCcompose) p0178
  have p0180 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCop (.cv f) R))
      (synCfv (synCcompose) (synCfv (synCtxp (synC1st) (synC2nd)) (synCop (.cv f) R)))
      (synCfv (synCcompose) (synCop (.cv f) R)) p0132 p0179
  have p0181 := (Nominal.classEqRefl (synCo (.cv f) (synCcompose) R))
  have p0183 :=
    @gPm32i (.classMem (.cv f) (synCvv)) (.classMem R (synCvv)) p0033 hyp_hwtrnval_1
  have p0184 := @gComposevalg (.cv f) R (synCvv) (synCvv)
  have p0185 := Nominal.mp p0183 p0184
  have p0186 :=
    @gEqtr3i (synCo (.cv f) (synCcompose) R)
      (synCfv (synCcompose) (synCop (.cv f) R)) (synCcom (.cv f) R) p0181 p0185
  have p0187 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCop (.cv f) R))
      (synCfv (synCcompose) (synCop (.cv f) R)) (synCcom (.cv f) R) p0180 p0186
  have p0194 := @gFvco2 (synCvv) (synCop (.cv f) R) (synCimage (synCswap)) (synC1st)
  have p0195 := Nominal.mp p0139 p0194
  have p0198 :=
    @gFveq2i (synCfv (synC1st) (synCop (.cv f) R)) (.cv f) (synCimage (synCswap))
      p0174
  have p0199 :=
    @gEqtri (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
      (synCfv (synCimage (synCswap)) (synCfv (synC1st) (synCop (.cv f) R)))
      (synCfv (synCimage (synCswap)) (.cv f)) p0195 p0198
  have p0200 := @gImageswapval f
  have p0201 :=
    @gEqtri (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
      (synCfv (synCimage (synCswap)) (.cv f)) (synCcnv (.cv f)) p0199 p0200
  have p0202 :=
    @gOpeq12i
      (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd))) (synCop (.cv f) R))
      (synCcom (.cv f) R)
      (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R))
      (synCcnv (.cv f)) p0187 p0201
  have p0203 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCop (.cv f) R))
      (synCop (synCfv (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCop (.cv f) R))
        (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop (.cv f) R)))
      (synCop (synCcom (.cv f) R) (synCcnv (.cv f))) p0115 p0202
  have p0204 :=
    @gFveq2i
      (synCfv (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
          (synCcom (synCimage (synCswap)) (synC1st))) (synCop (.cv f) R))
      (synCop (synCcom (.cv f) R) (synCcnv (.cv f))) (synCcompose) p0203
  have p0205 :=
    @gEqtri
      (synCfv (synCcom (synCcompose)
          (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st)))) (synCop (.cv f) R))
      (synCfv (synCcompose) (synCfv
          (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st))) (synCop (.cv f) R)))
      (synCfv (synCcompose) (synCop (synCcom (.cv f) R) (synCcnv (.cv f)))) p0037
      p0204
  have p0206 :=
    (Nominal.classEqRefl (synCo (synCcom (.cv f) R) (synCcompose) (synCcnv (.cv f))))
  have p0208 := @gCoex (.cv f) R p0033 hyp_hwtrnval_1
  have p0210 := @gCnvex (.cv f) p0033
  have p0211 :=
    @gPm32i (.classMem (synCcom (.cv f) R) (synCvv))
      (.classMem (synCcnv (.cv f)) (synCvv)) p0208 p0210
  have p0212 := @gComposevalg (synCcom (.cv f) R) (synCcnv (.cv f)) (synCvv) (synCvv)
  have p0213 := Nominal.mp p0211 p0212
  have p0214 :=
    @gEqtr3i (synCo (synCcom (.cv f) R) (synCcompose) (synCcnv (.cv f)))
      (synCfv (synCcompose) (synCop (synCcom (.cv f) R) (synCcnv (.cv f))))
      (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) p0206 p0213
  have p0215 :=
    @gEqtri
      (synCfv (synCcom (synCcompose)
          (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st)))) (synCop (.cv f) R))
      (synCfv (synCcompose) (synCop (synCcom (.cv f) R) (synCcnv (.cv f))))
      (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) p0205 p0214
  have p0216 :=
    @gEqtri (synCfv (synChwtrn) (synCop (.cv f) R))
      (synCfv (synCcom (synCcompose)
          (synCtxp (synCcom (synCcompose) (synCtxp (synC1st) (synC2nd)))
            (synCcom (synCimage (synCswap)) (synC1st)))) (synCop (.cv f) R))
      (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) p0001 p0215
  exact p0216

/-- Checked nominal proof certificate identified upstream as `g_ranfnfn`. -/
@[expose]
noncomputable def gRanfnfn : Nominal.NPrf (synWfn (synCranfn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gVex x
  have p0001 := @gRnex (.cv x) p0000
  have p0002 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRanfn x
  have p0003 :=
    @gFnmpti x (synCvv) (synCrn (.cv x)) (synCranfn) dv_cache_0001 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hwgenfn`. -/
@[expose]
noncomputable def gHwgenfn : Nominal.NPrf (synWfn (synChwgen) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gN2ndfo
  have p0001 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gVex x
  have p0004 := @gDmex (.cv x) p0003
  have p0005 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfDomfn x
  have p0006 :=
    @gFnmpti x (synCvv) (synCdm (.cv x)) (synCdomfn) dv_cache_0001 p0004 p0005
  have p0007 := @gN1stfo
  have p0008 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gSsv (synCrn (synC1st))
  have p0011 :=
    @gN3pm32i (synWfn (synCdomfn) (synCvv)) (synWfn (synC1st) (synCvv))
      (synWss (synCrn (synC1st)) (synCvv)) p0006 p0009 p0010
  have p0012 := @gFnco (synCvv) (synCvv) (synCdomfn) (synC1st)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCcom (synCdomfn) (synC1st)) (synCvv)) p0002 p0013
  have p0015 := @gFntxp (synCvv) (synCvv) (synC2nd) (synCcom (synCdomfn) (synC1st))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gInidm (synCvv)
  have p0018 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) p0017
  have p0019 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCvv)) p0016
      p0018
  have p0020 := @gHwtrnfn
  have p0022 := @gRnex (.cv x) p0003
  have p0023 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRanfn x
  have p0024 :=
    @gFnmpti x (synCvv) (synCrn (.cv x)) (synCranfn) dv_cache_0001 p0022 p0023
  have p0029 :=
    @gN3pm32i (synWfn (synCranfn) (synCvv)) (synWfn (synC1st) (synCvv))
      (synWss (synCrn (synC1st)) (synCvv)) p0024 p0009 p0010
  have p0030 := @gFnco (synCvv) (synCvv) (synCranfn) (synC1st)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @gPm32i (synWfn (synChwtrn) (synCvv))
      (synWfn (synCcom (synCranfn) (synC1st)) (synCvv)) p0020 p0031
  have p0033 :=
    @gFntxp (synCvv) (synCvv) (synChwtrn) (synCcom (synCranfn) (synC1st))
  have p0034 := Nominal.mp p0032 p0033
  have p0036 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) p0017
  have p0037 :=
    @gMpbi
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCvv)) p0034
      p0036
  have p0038 :=
    @gPm32i (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCvv))
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCvv)) p0019
      p0037
  have p0039 :=
    @gFntxp (synCvv) (synCvv) (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
  have p0040 := Nominal.mp p0038 p0039
  have p0042 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
      p0017
  have p0043 :=
    @gMpbi
      (synWfn (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCvv))
      p0040 p0042
  have p0044 := (Nominal.classEqRefl (synChwgen))
  have p0045 :=
    @gFneq1i (synCvv) (synChwgen)
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
      p0044
  have p0046 :=
    @gBicomi (synWfn (synChwgen) (synCvv))
      (synWfn (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCvv))
      p0045
  have p0047 :=
    @gMpbi
      (synWfn (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCvv))
      (synWfn (synChwgen) (synCvv)) p0043 p0046
  exact p0047


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwgenval`. -/
@[expose]
noncomputable def gHwgenval (R : Class) (f : Var)
    (hyp_hwgenval_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChwgen) (synCop (.cv f) R))
        (synCop (synCop R (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) (synCrn (.cv f))))) :=
  by
  let proofSupport : Finset Var := R.fv ∪ ({ f } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChwgen))
  have p0001 :=
    @gFveq1i (synCop (.cv f) R) (synChwgen)
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
      p0000
  have p0002 :=
    @gEqid
      (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R))
  have p0003 := @gN2ndfo
  have p0004 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gVex x
  have p0007 := @gDmex (.cv x) p0006
  have p0008 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfDomfn x
  have p0009 :=
    @gFnmpti x (synCvv) (synCdm (.cv x)) (synCdomfn) dv_cache_0001 p0007 p0008
  have p0010 := @gN1stfo
  have p0011 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gSsv (synCrn (synC1st))
  have p0014 :=
    @gN3pm32i (synWfn (synCdomfn) (synCvv)) (synWfn (synC1st) (synCvv))
      (synWss (synCrn (synC1st)) (synCvv)) p0009 p0012 p0013
  have p0015 := @gFnco (synCvv) (synCvv) (synCdomfn) (synC1st)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCcom (synCdomfn) (synC1st)) (synCvv)) p0005 p0016
  have p0018 := @gFntxp (synCvv) (synCvv) (synC2nd) (synCcom (synCdomfn) (synC1st))
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @gInidm (synCvv)
  have p0021 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) p0020
  have p0022 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCvv)) p0019
      p0021
  have p0023 := @gVex f
  have p0024 := @gOpex (.cv f) R p0023 hyp_hwgenval_1
  have p0025 :=
    @gPm32i (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0022 p0024
  have p0026 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R)
      (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R))
      (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @gMpbi
      (.classEq (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCop (.cv f) R)) (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R)))
      p0002 p0027
  have p0029 :=
    @gEqid
      (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCop (.cv f) R))
  have p0030 := @gHwtrnfn
  have p0032 := @gRnex (.cv x) p0006
  have p0033 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRanfn x
  have p0034 :=
    @gFnmpti x (synCvv) (synCrn (.cv x)) (synCranfn) dv_cache_0001 p0032 p0033
  have p0039 :=
    @gN3pm32i (synWfn (synCranfn) (synCvv)) (synWfn (synC1st) (synCvv))
      (synWss (synCrn (synC1st)) (synCvv)) p0034 p0012 p0013
  have p0040 := @gFnco (synCvv) (synCvv) (synCranfn) (synC1st)
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @gPm32i (synWfn (synChwtrn) (synCvv))
      (synWfn (synCcom (synCranfn) (synC1st)) (synCvv)) p0030 p0041
  have p0043 :=
    @gFntxp (synCvv) (synCvv) (synChwtrn) (synCcom (synCranfn) (synC1st))
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) p0020
  have p0047 :=
    @gMpbi
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCvv)) p0044
      p0046
  have p0050 :=
    @gPm32i
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0047 p0024
  have p0051 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R)
      (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCop (.cv f) R))
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
  have p0052 := Nominal.mp p0050 p0051
  have p0053 :=
    @gMpbi
      (.classEq (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCop (.cv f) R))
        (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
        (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCop (.cv f) R)))
      p0029 p0052
  have p0054 :=
    @gPm32i
      (synWbr (synCop (.cv f) R) (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
        (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCop (.cv f) R)))
      p0028 p0053
  have p0055 :=
    @gTrtxp (synCop (.cv f) R)
      (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R))
      (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCop (.cv f) R))
      (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
  have p0056 :=
    @gMpbir
      (synWbr (synCop (.cv f) R)
        (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCop
          (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R))
          (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
            (synCop (.cv f) R))))
      (synWa (synWbr (synCop (.cv f) R)
          (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
            (synCop (.cv f) R))) (synWbr (synCop (.cv f) R)
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
            (synCop (.cv f) R))))
      p0054 p0055
  have p0095 :=
    @gPm32i (synWfn (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCvv))
      (synWfn (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCvv)) p0022
      p0047
  have p0096 :=
    @gFntxp (synCvv) (synCvv) (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
  have p0097 := Nominal.mp p0095 p0096
  have p0099 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
      p0020
  have p0100 :=
    @gMpbi
      (synWfn (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCvv))
      p0097 p0099
  have p0101 :=
    @gFnfun (synCvv)
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
  have p0102 := Nominal.mp p0100 p0101
  have p0103 :=
    @gFunbrfv (synCop (.cv f) R)
      (synCop (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCop (.cv f) R))
        (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCop (.cv f) R)))
      (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))))
  have p0104 := Nominal.mp p0102 p0103
  have p0105 := Nominal.mp p0056 p0104
  have p0106 := @gEqid (synCfv (synC2nd) (synCop (.cv f) R))
  have p0112 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (synCop (.cv f) R) (synCvv))
      p0005 p0024
  have p0113 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R) (synCfv (synC2nd) (synCop (.cv f) R))
      (synC2nd)
  have p0114 := Nominal.mp p0112 p0113
  have p0115 :=
    @gMpbi
      (.classEq (synCfv (synC2nd) (synCop (.cv f) R))
        (synCfv (synC2nd) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synC2nd) (synCfv (synC2nd) (synCop (.cv f) R)))
      p0106 p0114
  have p0116 := @gEqid (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))
  have p0130 :=
    @gPm32i (synWfn (synCcom (synCdomfn) (synC1st)) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0016 p0024
  have p0131 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R)
      (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))
      (synCcom (synCdomfn) (synC1st))
  have p0132 := Nominal.mp p0130 p0131
  have p0133 :=
    @gMpbi
      (.classEq (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))
        (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCdomfn) (synC1st))
        (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)))
      p0116 p0132
  have p0134 :=
    @gPm32i
      (synWbr (synCop (.cv f) R) (synC2nd) (synCfv (synC2nd) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCdomfn) (synC1st))
        (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)))
      p0115 p0133
  have p0135 :=
    @gTrtxp (synCop (.cv f) R) (synCfv (synC2nd) (synCop (.cv f) R))
      (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)) (synC2nd)
      (synCcom (synCdomfn) (synC1st))
  have p0136 :=
    @gMpbir
      (synWbr (synCop (.cv f) R) (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
        (synCop (synCfv (synC2nd) (synCop (.cv f) R))
          (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))))
      (synWa (synWbr (synCop (.cv f) R) (synC2nd) (synCfv (synC2nd) (synCop (.cv f) R)))
        (synWbr (synCop (.cv f) R) (synCcom (synCdomfn) (synC1st))
          (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))))
      p0134 p0135
  have p0157 :=
    @gFnfun (synCvv) (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
  have p0158 := Nominal.mp p0022 p0157
  have p0159 :=
    @gFunbrfv (synCop (.cv f) R)
      (synCop (synCfv (synC2nd) (synCop (.cv f) R))
        (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)))
      (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
  have p0160 := Nominal.mp p0158 p0159
  have p0161 := Nominal.mp p0136 p0160
  have p0163 := @gOpfv2nd (.cv f) R p0023 hyp_hwgenval_1
  have p0169 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (.classMem (synCop (.cv f) R) (synCvv))
      p0012 p0024
  have p0170 := @gFvco2 (synCvv) (synCop (.cv f) R) (synCdomfn) (synC1st)
  have p0171 := Nominal.mp p0169 p0170
  have p0173 := @gOpfv1st (.cv f) R p0023 hyp_hwgenval_1
  have p0174 :=
    @gFveq2i (synCfv (synC1st) (synCop (.cv f) R)) (.cv f) (synCdomfn) p0173
  have p0175 :=
    @gEqtri (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))
      (synCfv (synCdomfn) (synCfv (synC1st) (synCop (.cv f) R)))
      (synCfv (synCdomfn) (.cv f)) p0171 p0174
  have p0177 := @gFvdomfn (.cv f) (synCvv)
  have p0178 := Nominal.mp p0023 p0177
  have p0179 :=
    @gEqtri (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R))
      (synCfv (synCdomfn) (.cv f)) (synCdm (.cv f)) p0175 p0178
  have p0180 :=
    @gOpeq12i (synCfv (synC2nd) (synCop (.cv f) R)) R
      (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)) (synCdm (.cv f))
      p0163 p0179
  have p0181 :=
    @gEqtri
      (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R))
      (synCop (synCfv (synC2nd) (synCop (.cv f) R))
        (synCfv (synCcom (synCdomfn) (synC1st)) (synCop (.cv f) R)))
      (synCop R (synCdm (.cv f))) p0161 p0180
  have p0182 := @gEqid (synCfv (synChwtrn) (synCop (.cv f) R))
  have p0186 :=
    @gPm32i (synWfn (synChwtrn) (synCvv)) (.classMem (synCop (.cv f) R) (synCvv))
      p0030 p0024
  have p0187 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R) (synCfv (synChwtrn) (synCop (.cv f) R))
      (synChwtrn)
  have p0188 := Nominal.mp p0186 p0187
  have p0189 :=
    @gMpbi
      (.classEq (synCfv (synChwtrn) (synCop (.cv f) R))
        (synCfv (synChwtrn) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synChwtrn) (synCfv (synChwtrn) (synCop (.cv f) R)))
      p0182 p0188
  have p0190 := @gEqid (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))
  have p0204 :=
    @gPm32i (synWfn (synCcom (synCranfn) (synC1st)) (synCvv))
      (.classMem (synCop (.cv f) R) (synCvv)) p0041 p0024
  have p0205 :=
    @gFnbrfvb (synCvv) (synCop (.cv f) R)
      (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))
      (synCcom (synCranfn) (synC1st))
  have p0206 := Nominal.mp p0204 p0205
  have p0207 :=
    @gMpbi
      (.classEq (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))
        (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCranfn) (synC1st))
        (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)))
      p0190 p0206
  have p0208 :=
    @gPm32i
      (synWbr (synCop (.cv f) R) (synChwtrn) (synCfv (synChwtrn) (synCop (.cv f) R)))
      (synWbr (synCop (.cv f) R) (synCcom (synCranfn) (synC1st))
        (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)))
      p0189 p0207
  have p0209 :=
    @gTrtxp (synCop (.cv f) R) (synCfv (synChwtrn) (synCop (.cv f) R))
      (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)) (synChwtrn)
      (synCcom (synCranfn) (synC1st))
  have p0210 :=
    @gMpbir
      (synWbr (synCop (.cv f) R) (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
        (synCop (synCfv (synChwtrn) (synCop (.cv f) R))
          (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))))
      (synWa (synWbr (synCop (.cv f) R) (synChwtrn)
          (synCfv (synChwtrn) (synCop (.cv f) R)))
        (synWbr (synCop (.cv f) R) (synCcom (synCranfn) (synC1st))
          (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))))
      p0208 p0209
  have p0229 :=
    @gFnfun (synCvv) (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
  have p0230 := Nominal.mp p0047 p0229
  have p0231 :=
    @gFunbrfv (synCop (.cv f) R)
      (synCop (synCfv (synChwtrn) (synCop (.cv f) R))
        (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)))
      (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
  have p0232 := Nominal.mp p0230 p0231
  have p0233 := Nominal.mp p0210 p0232
  have p0234 := @gHwtrnval R f hyp_hwgenval_1
  have p0241 := @gFvco2 (synCvv) (synCop (.cv f) R) (synCranfn) (synC1st)
  have p0242 := Nominal.mp p0169 p0241
  have p0245 :=
    @gFveq2i (synCfv (synC1st) (synCop (.cv f) R)) (.cv f) (synCranfn) p0173
  have p0246 :=
    @gEqtri (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))
      (synCfv (synCranfn) (synCfv (synC1st) (synCop (.cv f) R)))
      (synCfv (synCranfn) (.cv f)) p0242 p0245
  have p0248 := @gFvranfn (.cv f) (synCvv)
  have p0249 := Nominal.mp p0023 p0248
  have p0250 :=
    @gEqtri (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R))
      (synCfv (synCranfn) (.cv f)) (synCrn (.cv f)) p0246 p0249
  have p0251 :=
    @gOpeq12i (synCfv (synChwtrn) (synCop (.cv f) R))
      (synCcom (synCcom (.cv f) R) (synCcnv (.cv f)))
      (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)) (synCrn (.cv f))
      p0234 p0250
  have p0252 :=
    @gEqtri
      (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCop (.cv f) R))
      (synCop (synCfv (synChwtrn) (synCop (.cv f) R))
        (synCfv (synCcom (synCranfn) (synC1st)) (synCop (.cv f) R)))
      (synCop (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) (synCrn (.cv f))) p0233
      p0251
  have p0253 :=
    @gOpeq12i
      (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st))) (synCop (.cv f) R))
      (synCop R (synCdm (.cv f)))
      (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st))) (synCop (.cv f) R))
      (synCop (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) (synCrn (.cv f))) p0181
      p0252
  have p0254 :=
    @gEqtri
      (synCfv (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCop (.cv f) R))
      (synCop (synCfv (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCop (.cv f) R))
        (synCfv (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))
          (synCop (.cv f) R)))
      (synCop (synCop R (synCdm (.cv f)))
        (synCop (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) (synCrn (.cv f))))
      p0105 p0253
  have p0255 :=
    @gEqtri (synCfv (synChwgen) (synCop (.cv f) R))
      (synCfv (synCtxp (synCtxp (synC2nd) (synCcom (synCdomfn) (synC1st)))
          (synCtxp (synChwtrn) (synCcom (synCranfn) (synC1st)))) (synCop (.cv f) R))
      (synCop (synCop R (synCdm (.cv f)))
        (synCop (synCcom (synCcom (.cv f) R) (synCcnv (.cv f))) (synCrn (.cv f))))
      p0001 p0254
  exact p0255

/-- Checked nominal proof certificate identified upstream as `g_elhwnisogen`. -/
@[expose]
noncomputable def gElhwnisogen (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (_dv_A_f : f ∉ A.fv) (_dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWrex f (synChwbij) (synWrex r (synCvv)
              (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
                (synCop (.cv u) (.cv v))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ ({ f } : Finset Var) ∪
      ({ r } : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_v : p ≠ v := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_f : p ≠ f := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_p : f ≠ p := Ne.symm fresh_p_ne_f
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p := Ne.symm fresh_p_ne_r
  have dv_cache_0001 : p ∉ ((synCxp (synChwbij) (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((synCop (.cv u) (.cv v))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, fresh_p_ne_v, or_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((synChwgen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((synChwbij)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((synChwbij)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((synChwbij)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : f ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : r ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 :
    f ∉ ((Wff.classEq (synCfv (synChwgen) (.cv p)) (synCop (.cv u) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_p, dv_f_u, dv_f_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    r ∉ ((Wff.classEq (synCfv (synChwgen) (.cv p)) (synCop (.cv u) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_p, dv_r_u, dv_r_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((Wff.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
          (synCop (.cv u) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_f, fresh_p_ne_r, fresh_p_ne_u, fresh_p_ne_v,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : p ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show p ≠ f from (by exact fresh_p_ne_f))
  have dv_cache_0014 : p ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0015 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show f ≠ r from (by exact dv_f_r))
  have p0000 := (Nominal.biimpRefl (synWbr (.cv u) (synChwniso A) (.cv v)))
  have p0001 := (Nominal.classEqRefl (synChwniso A))
  have p0002 :=
    @gEleq2i (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synCop (.cv u) (.cv v)) p0001
  have p0003 :=
    @gElin (synCop (.cv u) (.cv v))
      (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCxp (synChwcn A) (synChwcn A))
  have p0004 := @gHwgenfn
  have p0005 := @gSsv (synCxp (synChwbij) (synCvv))
  have p0006 :=
    @gPm32i (synWfn (synChwgen) (synCvv))
      (synWss (synCxp (synChwbij) (synCvv)) (synCvv)) p0004 p0005
  have p0007 :=
    @gFvelimab p (synCvv) (synCxp (synChwbij) (synCvv)) (synCop (.cv u) (.cv v))
      (synChwgen) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gFveq2 (.cv p) (synCop (.cv f) (.cv r)) (synChwgen)
  have p0010 :=
    @gEqeq1d (.classEq (.cv p) (synCop (.cv f) (.cv r))) (synCfv (synChwgen) (.cv p))
      (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u) (.cv v)) p0009
  have p0011 :=
    @gRexxp (.classEq (synCfv (synChwgen) (.cv p)) (synCop (.cv u) (.cv v)))
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u) (.cv v)))
      p f r (synChwbij) (synCvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 p0010
  have p0012 :=
    @gBitri
      (.classMem (synCop (.cv u) (.cv v))
        (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))
      (synWrex p (synCxp (synChwbij) (synCvv))
        (.classEq (synCfv (synChwgen) (.cv p)) (synCop (.cv u) (.cv v))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (.cv v)))))
      p0008 p0011
  have p0013 := @gOpelxp (.cv u) (.cv v) (synChwcn A) (synChwcn A)
  have p0014 :=
    @gAnbi12i
      (.classMem (synCop (.cv u) (.cv v))
        (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (.cv v)))))
      (.classMem (synCop (.cv u) (.cv v)) (synCxp (synChwcn A) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0012
      p0013
  have p0015 :=
    @gAncom
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0016 :=
    @gBitri
      (synWa (.classMem (synCop (.cv u) (.cv v))
          (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))
        (.classMem (synCop (.cv u) (.cv v)) (synCxp (synChwcn A) (synChwcn A))))
      (synWa (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v)))))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v))))))
      p0014 p0015
  have p0017 :=
    @gBitri
      (.classMem (synCop (.cv u) (.cv v))
        (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn A) (synChwcn A))))
      (synWa (.classMem (synCop (.cv u) (.cv v))
          (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))
        (.classMem (synCop (.cv u) (.cv v)) (synCxp (synChwcn A) (synChwcn A))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v))))))
      p0003 p0016
  have p0018 :=
    @gBitri (.classMem (synCop (.cv u) (.cv v)) (synChwniso A))
      (.classMem (synCop (.cv u) (.cv v))
        (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn A) (synChwcn A))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v))))))
      p0002 p0017
  have p0019 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synChwniso A))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v))))))
      p0000 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_elhwnisogenval`. -/
@[expose]
noncomputable def gElhwnisogenval (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWrex f (synChwbij) (synWrex r (synCvv)
              (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v))))))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0003 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have p0000 :=
    @gElhwnisogen v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @gVex r
  have p0002 := @gHwgenval (.cv r) f p0001
  have p0003 :=
    @gEqeq1i (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
      (synCop (synCop (.cv r) (synCdm (.cv f)))
        (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
      (synCop (.cv u) (.cv v)) p0002
  have p0004 :=
    @gOpth (synCop (.cv r) (synCdm (.cv f)))
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      (.cv u) (.cv v)
  have p0005 :=
    @gBitri
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u) (.cv v)))
      (.classEq (synCop (synCop (.cv r) (synCdm (.cv f)))
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))))
        (synCop (.cv u) (.cv v)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      p0003 p0004
  have p0006 :=
    @gRexbii
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u) (.cv v)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      r (synCvv) p0005
  have p0007 :=
    @gRexbii
      (synWrex r (synCvv) (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
          (synCop (.cv u) (.cv v))))
      (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
          (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (.cv v))))
      f (synChwbij) p0006
  have p0008 :=
    @gAnbi2i
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (.cv v)))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0007
  have p0009 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_elhwnisogenfun`. -/
@[expose]
noncomputable def gElhwnisogenfun (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWex f (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
              (synWrex r (synCvv)
                (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                    (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                      (synCrn (.cv f))) (.cv v)))))))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0003 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have p0000 :=
    @gElhwnisogenval v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    (Nominal.biimpRefl (synWrex f (synChwbij) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v))))))
  have p0002 := @gElhwbij f
  have p0003 :=
    @gAnbi1i (.classMem (.cv f) (synChwbij))
      (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
          (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (.cv v))))
      p0002
  have p0004 :=
    @gExbii
      (synWa (.classMem (.cv f) (synChwbij)) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      f p0003
  have p0005 :=
    @gBitri
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWex f (synWa (.classMem (.cv f) (synChwbij)) (synWrex r (synCvv)
            (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWex f (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
          (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      p0001 p0004
  have p0006 :=
    @gAnbi2i
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWex f (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
          (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0005
  have p0007 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
            (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hwbijf1o`. -/
@[expose]
noncomputable def gHwbijf1o (f : Var) :
    Nominal.NPrf
      (synWb (.classMem (.cv f) (synChwbij))
        (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))) :=
  by
  have p0000 := @gElhwbij f
  have p0001 := @gFunfn (.cv f)
  have p0002 :=
    @gAnbi1i (synWfun (.cv f)) (synWfn (.cv f) (synCdm (.cv f)))
      (synWfun (synCcnv (.cv f))) p0001
  have p0003 := @gF1orn (synCdm (.cv f)) (.cv f)
  have p0004 :=
    @gBicomi (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (synWfn (.cv f) (synCdm (.cv f))) (synWfun (synCcnv (.cv f)))) p0003
  have p0005 :=
    @gBitri (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWa (synWfn (.cv f) (synCdm (.cv f))) (synWfun (synCcnv (.cv f))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) p0002 p0004
  have p0006 :=
    @gBitri (.classMem (.cv f) (synChwbij))
      (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elhwnisogenf1o`. -/
@[expose]
noncomputable def gElhwnisogenf1o (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWex f (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
              (synWrex r (synCvv)
                (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                    (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                      (synCrn (.cv f))) (.cv v)))))))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0003 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have p0000 :=
    @gElhwnisogenfun v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @gFunfn (.cv f)
  have p0002 :=
    @gAnbi1i (synWfun (.cv f)) (synWfn (.cv f) (synCdm (.cv f)))
      (synWfun (synCcnv (.cv f))) p0001
  have p0003 := @gF1orn (synCdm (.cv f)) (.cv f)
  have p0004 :=
    @gBicomi (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (synWfn (.cv f) (synCdm (.cv f))) (synWfun (synCcnv (.cv f)))) p0003
  have p0005 :=
    @gBitri (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWa (synWfn (.cv f) (synCdm (.cv f))) (synWfun (synCcnv (.cv f))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) p0002 p0004
  have p0006 :=
    @gAnbi1i (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
          (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
              (synCrn (.cv f))) (.cv v))))
      p0005
  have p0007 :=
    @gExbii
      (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      f p0006
  have p0008 :=
    @gAnbi2i
      (synWex f (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
          (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWex f (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
          (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0007
  have p0009 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
            (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
            (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      p0000 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end
