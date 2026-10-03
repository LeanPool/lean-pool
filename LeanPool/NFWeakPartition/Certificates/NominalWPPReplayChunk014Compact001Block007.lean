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

@[expose]
noncomputable def g_fdcolcodemapf12 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapf12_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodemapf12_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodemapf12_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B))))) :=
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
  have dv_cache_0010 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((A).fv) (((syn_cuni (.cv q))).fv) from
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
  have dv_cache_0011 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv ((syn_cuni (syn_cuni (.cv r)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((A).fv) (((syn_cuni (.cv r))).fv) from
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
  have dv_cache_0012 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((B).fv) (((syn_cuni (.cv q))).fv) from
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
  have dv_cache_0013 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv ((syn_cuni (syn_cuni (.cv r)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint ((B).fv) (((syn_cuni (.cv r))).fv) from
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
    Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cuni (syn_cuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cuni (syn_cuni (.cv r)))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni ((syn_cuni (.cv q))),
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni ((syn_cuni (.cv r)))];
          exact
            (show Disjoint (((syn_cuni (.cv q))).fv) (((syn_cuni (.cv r))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv q)).fv) (((syn_cuni (.cv r))).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ q } : Finset Var)) (((syn_cuni (.cv r))).fv)
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
  have dv_cache_0015 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((syn_cuni (.cv q))).fv) ((R).fv) from
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
  have dv_cache_0016 : Disjoint ((syn_cuni (syn_cuni (.cv r)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv r)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((syn_cuni (.cv r))).fv) ((R).fv) from
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
  have dv_cache_0017 : r ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
    q ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))).fv :=
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
    r ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))).fv :=
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
  have dv_cache_0021 : q ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
  have dv_cache_0022 : q ∉ ((syn_cfdcolcodemap R A B)).fv :=
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
  have dv_cache_0023 : r ∉ ((syn_cfdcolcodemap R A B)).fv :=
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
  have p0000 := @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0001 :=
    @g_fdcolcodemapf A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf12_1
      hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0002 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wbr R (syn_cwe) A)
      (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0004 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0003 p0004
  have p0007 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
  have p0008 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) p0007 p0008
  have p0010 := @g_fdcolcodearg A q dv_cache_0004
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv q))) A)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0011 p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0003 p0013
  have p0017 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) p0007 p0017
  have p0019 := @g_fdcolcodearg A r dv_cache_0005
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A)
        (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))))
      p0018 p0019
  have p0021 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv r))) A)
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A)
        (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) A) p0020 p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) A) p0003 p0022
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) A)
      (.classMem (syn_cuni (syn_cuni (.cv r))) A) p0014 p0023
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
        (.classMem (syn_cuni (syn_cuni (.cv r))) A))
      p0005 p0024
  have p0026 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A)
      p0004 p0000
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))) p0030 p0009
  have p0035 :=
    @g_fdcolcodemapval A B R q dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003
      dv_cache_0006 dv_cache_0007 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2
      hyp_fdcolcodemapf12_3
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      p0034 p0035
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      p0003 p0036
  have p0045 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr R (syn_cwe) A) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))) p0030 p0018
  have p0046 :=
    @g_fdcolcodemapval A B R r dv_cache_0001 dv_cache_0002 dv_cache_0005 dv_cache_0003
      dv_cache_0008 dv_cache_0009 hyp_fdcolcodemapf12_1 hyp_fdcolcodemapf12_2
      hyp_fdcolcodemapf12_3
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r)))))
      p0045 p0046
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r)))))
      p0003 p0047
  have p0049 :=
    @g_n_3eqtr3d
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))
      (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))
      (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r)))) p0026 p0037 p0048
  have p0050 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
          (.classMem (syn_cuni (syn_cuni (.cv r))) A)))
      (.classEq (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r)))))
      p0025 p0049
  have p0051 :=
    @g_fdcodeinj2 A B (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) R
      dv_cache_0001 dv_cache_0010 dv_cache_0011 dv_cache_0002 dv_cache_0012 dv_cache_0013
      dv_cache_0003 dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_fdcolcodemapf12_1
      hyp_fdcolcodemapf12_2 hyp_fdcolcodemapf12_3
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
            (.classMem (syn_cuni (syn_cuni (.cv r))) A)))
        (.classEq (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))
          (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv r))))))
      (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))) p0050 p0051
  have p0053 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) p0052
  have p0054 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (.cv r))))
      p0053
  have p0061 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) A)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0011 p0061
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0003 p0062
  have p0070 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv r))) A)
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) A)
        (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))))
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0020 p0070
  have p0072 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0003 p0071
  have p0073 :=
    @g_n_3eqtr4d
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))))
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) (.cv q) (.cv r) p0054 p0063 p0072
  have p0074 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 A)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0073
  have p0075 :=
    @g_ralrimivva (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (.imp (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))
      q r (syn_cpw1 (syn_cpw1 A)) (syn_cpw1 (syn_cpw1 A)) dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 p0074
  have p0076 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wral q (syn_cpw1 (syn_cpw1 A)) (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp
            (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
              (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))))
      p0002 p0075
  have p0077 :=
    @g_dff13 q r (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))
      (syn_cfdcolcodemap R A B) dv_cache_0021 dv_cache_0017 dv_cache_0022 dv_cache_0023
      dv_cache_0020
  have p0078_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wa
          (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
            (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A))
            (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp
                (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
                  (syn_cfv (syn_cfdcolcodemap R A B) (.cv r)))
                (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cfdcolcodemap syn_cres
          syn_cpw1 syn_cpw
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
    @g_a1i
      (syn_wb (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wa
          (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
            (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A))
            (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp
                (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
                  (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r)))))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0078_e00_recanon
  have p0079 :=
    @g_mpbird (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wa (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wral q (syn_cpw1 (syn_cpw1 A))
          (syn_wral r (syn_cpw1 (syn_cpw1 A)) (.imp
              (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
                (syn_cfv (syn_cfdcolcodemap R A B) (.cv r))) (.classEq (.cv q) (.cv r))))))
      p0076 p0078
  exact p0079

@[expose]
noncomputable def g_fdcolcodecardle2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodecardle2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodecardle2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodecardle2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec)
          (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))))) :=
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
  have dv_cache_0004 : f ∉ ((syn_cfdcolcodemap R A B)).fv :=
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
      ((syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B))))).fv :=
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
    f ∉ ((Wff.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))))).fv :=
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
  have dv_cache_0007 : f ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
  have dv_cache_0009 : z ∉ ((syn_cpw (syn_cpw (syn_cfdif R A B)))).fv :=
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
      ((syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec)
            (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A))
              (syn_cpw (syn_cpw (syn_cfdif R A B))))))).fv :=
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
    @g_fdcolcodemapf12 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0001 := @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0002 :=
    @g_fdcolcodemapex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdcolcodecardle2_1 hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0003 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcolcodemap R A B) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))) (.cv f)
      (syn_cfdcolcodemap R A B)
  have p0005 :=
    @g_spcegv
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      f (syn_cfdcolcodemap R A B) (syn_cvv) dv_cache_0004 dv_cache_0005 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (.classMem (syn_cfdcolcodemap R A B) (syn_cvv))
      (.imp (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_wex f
          (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))))
      p0003 p0005
  have p0007 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wf1 (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wex f
        (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      p0000 p0006
  have p0009 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodecardle2_1
      hyp_fdcolcodecardle2_2 hyp_fdcolcodecardle2_3
  have p0010 := @g_pwexg (syn_cfdif R A B) (syn_cvv)
  have p0011 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A B) (syn_cvv))
      (.classMem (syn_cpw (syn_cfdif R A B)) (syn_cvv)) p0009 p0010
  have p0012 := @g_pwexg (syn_cpw (syn_cfdif R A B)) (syn_cvv)
  have p0013 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw (syn_cfdif R A B)) (syn_cvv))
      (.classMem (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv))
      p0001 p0013
  have p0015 := @g_id (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))))
  have p0016 :=
    @g_nceqd (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (.cv z)
      (syn_cpw (syn_cpw (syn_cfdif R A B))) p0015
  have p0017 :=
    @g_breq2d (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_cnc (.cv z))
      (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))
      (syn_clec) p0016
  have p0018 :=
    @g_f1eq3 (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cpw1 (syn_cpw1 A)) (.cv f)
  have p0019 :=
    @g_exbidv (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (.cv z))
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))) f
      dv_cache_0006 p0018
  have p0020 :=
    @g_bibi12d (.classEq (.cv z) (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (.cv z)))
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec)
        (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (.cv z)))
      (syn_wex f
        (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      p0017 p0019
  have p0021 := @g_pw1ex A hyp_fdcolcodecardle2_2
  have p0022 := @g_pw1ex (syn_cpw1 A) p0021
  have p0023 := @g_vex z
  have p0024 :=
    @g_nclenc (syn_cpw1 (syn_cpw1 A)) (.cv z) f dv_cache_0007 dv_cache_0008 p0022 p0023
  have p0025 :=
    @g_vtoclg
      (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) (syn_cnc (.cv z)))
        (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (.cv z))))
      (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec)
          (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f
          (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))))
      z (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv) dv_cache_0009 dv_cache_0010 p0020
      p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (.classMem (syn_cpw (syn_cpw (syn_cfdif R A B))) (syn_cvv))
      (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec)
          (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B))))) (syn_wex f
          (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B))))))
      p0014 p0025
  have p0027 :=
    @g_mpbird (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec)
        (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      (syn_wex f
        (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      p0007 p0026
  exact p0027

@[expose]
noncomputable def g_fdcolcodetc2nc (A : Class)
    (hyp_fdcolcodetc2nc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))) :=
  by
  have p0000 := @g_tcnc A hyp_fdcolcodetc2nc_1
  have p0001 := @g_tceq (syn_ctc (syn_cnc A)) (syn_cnc (syn_cpw1 A))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_pw1ex A hyp_fdcolcodetc2nc_1
  have p0004 := @g_tcnc (syn_cpw1 A) p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc A))) (syn_ctc (syn_cnc (syn_cpw1 A)))
      (syn_cnc (syn_cpw1 (syn_cpw1 A))) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_fdcolcodetc2le2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodetc2le2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodetc2le2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodetc2le2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wbr (syn_ctc (syn_ctc (syn_cnc A))) (syn_clec)
          (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))))) :=
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
  have p0000 := @g_fdcolcodetc2nc A hyp_fdcolcodetc2le2_2
  have p0001 :=
    @g_a1i (.classEq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0000
  have p0002 :=
    @g_fdcolcodecardle2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdcolcodetc2le2_1 hyp_fdcolcodetc2le2_2 hyp_fdcolcodetc2le2_3
  have p0003 :=
    @g_eqbrtrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))
      (syn_cnc (syn_cpw (syn_cpw (syn_cfdif R A B)))) (syn_clec) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_hwcodesex (A : Class)
    (hyp_hwcodesex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chwcodes A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0001 := @g_weex
  have p0002 := @g_vvex
  have p0003 := @g_pwex A hyp_hwcodesex_1
  have p0004 := @g_xpex (syn_cvv) (syn_cpw A) p0002 p0003
  have p0005 := @g_inex (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cvv) p0000 p0005
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

@[expose]
noncomputable def g_hwcodesexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_chwcodes A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0001 := @g_weex
  have p0002 := @g_a1i (.classMem (syn_cwe) (syn_cvv)) (.classMem A V) p0001
  have p0003 := @g_vvex
  have p0004 := @g_a1i (.classMem (syn_cvv) (syn_cvv)) (.classMem A V) p0003
  have p0005 := @g_pwexg A V
  have p0006 :=
    @g_jca (.classMem A V) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cpw A) (syn_cvv)) p0004 p0005
  have p0007 := @g_xpexg (syn_cvv) (syn_cpw A) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl (.classMem A V)
      (syn_wa (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cpw A) (syn_cvv)))
      (.classMem (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_jca (.classMem A V) (.classMem (syn_cwe) (syn_cvv))
      (.classMem (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv)) p0002 p0008
  have p0010 := @g_inexg (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_syl (.classMem A V)
      (syn_wa (.classMem (syn_cwe) (syn_cvv))
        (.classMem (syn_cxp (syn_cvv) (syn_cpw A)) (syn_cvv)))
      (.classMem (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cvv)) p0009
      p0010
  have p0012 :=
    @g_syl5eqel (.classMem A V) (syn_chwcodes A)
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_cvv) p0000 p0011
  exact p0012

@[expose]
noncomputable def g_elhwcodes (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_elhwcodes_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_elhwcodes_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop R D) (syn_chwcodes A))
        (syn_wa (syn_wbr R (syn_cwe) D) (syn_wss D A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0001 :=
    @g_eleq2i (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cop R D) p0000
  have p0002 := @g_elin (syn_cop R D) (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))
  have p0003 := (Nominal.biimpRefl (syn_wbr R (syn_cwe) D))
  have p0004 :=
    @g_bicomi (syn_wbr R (syn_cwe) D) (.classMem (syn_cop R D) (syn_cwe)) p0003
  have p0005 := @g_opelxp R D (syn_cvv) (syn_cpw A)
  have p0006 :=
    @g_mpbiran (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A)))
      (.classMem R (syn_cvv)) (.classMem D (syn_cpw A)) hyp_elhwcodes_1 p0005
  have p0007 := @g_elpw D A hyp_elhwcodes_2
  have p0008 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A)))
      (.classMem D (syn_cpw A)) (syn_wss D A) p0006 p0007
  have p0009 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cwe)) (syn_wbr R (syn_cwe) D)
      (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_wss D A) p0004 p0008
  have p0010 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))))
      (syn_wa (.classMem (syn_cop R D) (syn_cwe))
        (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_cpw A))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wss D A)) p0002 p0009
  have p0011 :=
    @g_bitri (.classMem (syn_cop R D) (syn_chwcodes A))
      (.classMem (syn_cop R D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wss D A)) p0001 p0010
  exact p0011

@[expose]
noncomputable def g_brhwiso (v : Var) (u : Var) (A : Class) (h : Var) (dv_A_h : h ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v)
    (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
          (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hwiso v u A h
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_eleq2i (syn_chwiso A)
      (syn_copab u v (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))
      (syn_cop (.cv u) (.cv v)) p0001
  have p0003 :=
    @g_opabid
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      u v
  have p0004 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_copab u v (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
            (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0002 p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0000 p0004
  exact p0005

@[expose]
noncomputable def g_brhwisoany (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
          (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) :=
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
      ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))).fv :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_hwiso y x A h
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_eleq2i (syn_chwiso A)
      (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A))
            (.classMem (.cv y) (syn_chwcodes A))) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
              (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))))))
      (syn_cop (.cv u) (.cv v)) p0001
  have p0003 := @g_vex u
  have p0004 := @g_vex v
  have p0005 := @g_eleq1 (.cv x) (.cv u) (syn_chwcodes A)
  have p0006 :=
    @g_anbi1d (.classEq (.cv x) (.cv u)) (.classMem (.cv x) (syn_chwcodes A))
      (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)) p0005
  have p0007 := @g_fveq2 (.cv x) (.cv u) (syn_c1st)
  have p0008 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))
      (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
      (syn_cfv (syn_c1st) (.cv u)) (.cv h)
  have p0009 :=
    @g_syl (.classEq (.cv x) (.cv u))
      (.classEq (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))))
      p0007 p0008
  have p0010 := @g_fveq2 (.cv x) (.cv u) (syn_c2nd)
  have p0011 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (.cv y)) (.cv h)
  have p0012 :=
    @g_syl (.classEq (.cv x) (.cv u))
      (.classEq (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))))
      p0010 p0011
  have p0013 :=
    @g_bitrd (.classEq (.cv x) (.cv u))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
      p0009 p0012
  have p0014 :=
    @g_exbidv (.classEq (.cv x) (.cv u))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
      h dv_cache_0007 p0013
  have p0015 :=
    @g_anbi12d (.classEq (.cv x) (.cv u))
      (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))))
      p0006 p0014
  have p0016 := @g_eleq1 (.cv y) (.cv v) (syn_chwcodes A)
  have p0017 :=
    @g_anbi2d (.classEq (.cv y) (.cv v)) (.classMem (.cv y) (syn_chwcodes A))
      (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)) p0016
  have p0018 := @g_fveq2 (.cv y) (.cv v) (syn_c1st)
  have p0019 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
      (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0020 :=
    @g_syl (.classEq (.cv y) (.cv v))
      (.classEq (syn_cfv (syn_c1st) (.cv y)) (syn_cfv (syn_c1st) (.cv v)))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))))
      p0018 p0019
  have p0021 := @g_fveq2 (.cv y) (.cv v) (syn_c2nd)
  have p0022 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))
      (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0023 :=
    @g_syl (.classEq (.cv y) (.cv v))
      (.classEq (syn_cfv (syn_c2nd) (.cv y)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0021 p0022
  have p0024 :=
    @g_bitrd (.classEq (.cv y) (.cv v))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0020 p0023
  have p0025 :=
    @g_exbidv (.classEq (.cv y) (.cv v))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      h dv_cache_0008 p0024
  have p0026 :=
    @g_anbi12d (.classEq (.cv y) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0017 p0025
  have p0027 :=
    @g_sylan9bb (.classEq (.cv x) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
            (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv y))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv y)))))
      (.classEq (.cv y) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0015 p0026
  have p0028 :=
    @g_opelopaba
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
            (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      x y (.cv u) (.cv v) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0006 p0003 p0004 p0027
  have p0029 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_copab x y (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chwcodes A)) (.classMem (.cv y) (syn_chwcodes A)))
            (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
                (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0002 p0028
  have p0030 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwiso A))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0000 p0029
  exact p0030

@[expose]
noncomputable def g_hwisosymi (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv u))) :=
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
  have dv_cache_0007 : g ∉ ((syn_ccnv (.cv h))).fv :=
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
      ((syn_wiso (syn_ccnv (.cv h)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)))).fv :=
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
      ((syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
    @g_brhwiso v u A h dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0003 :=
    @g_ancom (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))
  have p0004 :=
    @g_biimpi
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
      p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
      p0002 p0004
  have p0006 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0007 :=
    @g_isocnv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0008 := @g_vex h
  have p0009 := @g_cnvex (.cv h) p0008
  have p0010 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (syn_ccnv (.cv h)) (.cv g)
  have p0011 :=
    @g_spcev
      (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wiso (syn_ccnv (.cv h)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))
      g (syn_ccnv (.cv h)) dv_cache_0007 dv_cache_0008 p0009 p0010
  have p0012 :=
    @g_syl
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (syn_ccnv (.cv h)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))
      p0007 p0011
  have p0013 :=
    @g_exlimiv
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))
      h dv_cache_0009 p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))
      p0006 p0013
  have p0015 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))))
      p0005 p0014
  have p0016 :=
    @g_syl (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0001 p0015
  have p0017 :=
    @g_brhwiso u v A g dv_cache_0010 dv_cache_0003 dv_cache_0002 dv_cache_0011
      dv_cache_0012 dv_cache_0013
  have p0018 :=
    @g_biimpri (syn_wbr (.cv v) (syn_chwiso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0017
  have p0019 :=
    @g_syl (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0016 p0018
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

@[expose]
noncomputable def g_hwisotri (w : Var) (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_u_v : u ≠ v) (dv_u_w : u ≠ w)
    (dv_v_w : v ≠ w) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
          (syn_wbr (.cv v) (syn_chwiso A) (.cv w))) (syn_wbr (.cv u) (syn_chwiso A) (.cv w))) :=
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
      ((syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))).fv :=
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
      ((syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))).fv :=
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
  have dv_cache_0014 : h ∉ ((syn_ccom (.cv g) (.cv f))).fv :=
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
      ((syn_wiso (syn_ccom (.cv g) (.cv f)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cfv (syn_c2nd) (.cv w)))).fv :=
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
      ((syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))).fv :=
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
      ((syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))).fv :=
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
    @g_brhwiso v u A f dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0000
  have p0002 :=
    @g_brhwiso w v A g dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011
  have p0003 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      p0002
  have p0004 :=
    @g_anim12i (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      p0001 p0003
  have p0005 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
  have p0006 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0007 :=
    @g_simpl (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (.classMem (.cv u) (syn_chwcodes A)) p0006 p0007
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (.classMem (.cv u) (syn_chwcodes A)) p0005 p0008
  have p0010 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
  have p0011 :=
    @g_simpl
      (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
  have p0012 :=
    @g_simpr (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
      (.classMem (.cv w) (syn_chwcodes A)) p0011 p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      (.classMem (.cv w) (syn_chwcodes A)) p0010 p0013
  have p0015 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)) p0009
      p0014
  have p0017 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0005 p0017
  have p0020 :=
    @g_simpr
      (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
      p0010 p0020
  have p0022 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
      p0018 p0021
  have p0023 :=
    @g_eeanv
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
        (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))
      f g dv_cache_0012 dv_cache_0013
  have p0024 :=
    @g_biimpri
      (syn_wex f (syn_wex g (syn_wa
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wex f
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g
          (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      p0023
  have p0025 :=
    @g_isotr (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c2nd) (.cv w)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w)) (.cv g) (.cv f)
  have p0026 := @g_vex g
  have p0027 := @g_vex f
  have p0028 := @g_coex (.cv g) (.cv f) p0026 p0027
  have p0029 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w)) (syn_ccom (.cv g) (.cv f))
      (.cv h)
  have p0030 :=
    @g_spcev
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wiso (syn_ccom (.cv g) (.cv f)) (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))
      h (syn_ccom (.cv g) (.cv f)) dv_cache_0014 dv_cache_0015 p0028 p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
      (syn_wiso (syn_ccom (.cv g) (.cv f)) (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_c1st) (.cv w)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))
      p0025 p0030
  have p0032 :=
    @g_exlimivv
      (syn_wa (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))
      f g dv_cache_0016 dv_cache_0017 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wex f
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g
          (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      (syn_wex f (syn_wex g (syn_wa
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))
      p0024 p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wex f
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wex g
          (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))
      p0022 p0033
  have p0035 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w))))
      p0015 p0034
  have p0036 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wa
          (syn_wa (.classMem (.cv v) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
          (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv w))
              (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv w))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))))
      p0004 p0035
  have p0037 :=
    @g_brhwiso w u A h dv_cache_0018 dv_cache_0002 dv_cache_0008 dv_cache_0019
      dv_cache_0020 dv_cache_0021
  have p0038 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwiso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))))
      p0037
  have p0039 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv w) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv w))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv w)))))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0036 p0038
  exact p0039

@[expose]
noncomputable def g_hwisorefl (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcodes A)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))) :=
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
  have dv_cache_0001 : h ∉ ((syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u)))).fv := by
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
      ((syn_wiso (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))).fv :=
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
  have p0000 := @g_pm4_24 (.classMem (.cv u) (syn_chwcodes A))
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcodes A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
      p0000
  have p0002 := @g_isoid (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0003 := @g_idex
  have p0004 := @g_fvex (.cv u) (syn_c2nd)
  have p0005 := @g_resex (syn_cid) (syn_cfv (syn_c2nd) (.cv u)) p0003 p0004
  have p0006 :=
    @g_isoeq1 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u))) (.cv h)
  have p0007 :=
    @g_spcev
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wiso (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      h (syn_cres (syn_cid) (syn_cfv (syn_c2nd) (.cv u))) dv_cache_0001 dv_cache_0002
      p0005 p0006
  have p0008 := Nominal.mp p0002 p0007
  have p0009 :=
    @g_a1i
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcodes A)) p0008
  have p0010 :=
    @g_jca (.classMem (.cv u) (syn_chwcodes A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0001 p0009
  have p0011 := @g_brhwisoany u u A h dv_cache_0003 dv_cache_0004 dv_cache_0004
  have p0012 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwiso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0011
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcodes A))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0010 p0012
  exact p0013

@[expose]
noncomputable def g_hwrelsex : Nominal.NPrf (.classMem (syn_chwrels) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwrels))
  have p0001 := @g_n_1stex
  have p0002 := @g_crossex
  have p0003 := @g_n_2ndex
  have p0005 := @g_txpex (syn_c2nd) (syn_c2nd) p0003 p0003
  have p0006 := @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0002 p0005
  have p0007 :=
    @g_txpex (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) p0001
      p0006
  have p0008 :=
    @g_cnvex
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0007
  have p0009 := @g_ssetex
  have p0010 :=
    @g_imaex
      (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
      (syn_csset) p0008 p0009
  have p0011 :=
    @g_eqeltri (syn_chwrels)
      (syn_cima (syn_ccnv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
        (syn_csset))
      (syn_cvv) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_hwbijex : Nominal.NPrf (.classMem (syn_chwbij) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwbij))
  have p0001 := @g_funsex
  have p0002 := @g_swapex
  have p0003 := @g_imageex (syn_cswap) p0002
  have p0004 := @g_cnvex (syn_cimage (syn_cswap)) p0003
  have p0006 := @g_imaex (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns) p0004 p0001
  have p0007 :=
    @g_inex (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)) p0001
      p0006
  have p0008 :=
    @g_eqeltri (syn_chwbij)
      (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_hwgenex : Nominal.NPrf (.classMem (syn_chwgen) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwgen))
  have p0001 := @g_n_2ndex
  have p0002 := @g_domfnex
  have p0003 := @g_n_1stex
  have p0004 := @g_coex (syn_cdomfn) (syn_c1st) p0002 p0003
  have p0005 := @g_txpex (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)) p0001 p0004
  have p0006 := (Nominal.classEqRefl (syn_chwtrn))
  have p0007 := @g_composeex
  have p0011 := @g_txpex (syn_c1st) (syn_c2nd) p0003 p0001
  have p0012 := @g_coex (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)) p0007 p0011
  have p0013 := @g_swapex
  have p0014 := @g_imageex (syn_cswap) p0013
  have p0016 := @g_coex (syn_cimage (syn_cswap)) (syn_c1st) p0014 p0003
  have p0017 :=
    @g_txpex (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) p0012 p0016
  have p0018 :=
    @g_coex (syn_ccompose)
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
      p0007 p0017
  have p0019 :=
    @g_eqeltri (syn_chwtrn)
      (syn_ccom (syn_ccompose)
        (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
      (syn_cvv) p0006 p0018
  have p0020 := @g_ranfnex
  have p0022 := @g_coex (syn_cranfn) (syn_c1st) p0020 p0003
  have p0023 := @g_txpex (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)) p0019 p0022
  have p0024 :=
    @g_txpex (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0005 p0023
  have p0025 :=
    @g_eqeltri (syn_chwgen)
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
      (syn_cvv) p0000 p0024
  exact p0025

@[expose]
noncomputable def g_hwcnex (A : Class)
    (hyp_hwcnex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chwcn A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcn A))
  have p0001 := @g_hwcodesex A hyp_hwcnex_1
  have p0002 := (Nominal.classEqRefl (syn_chwrels))
  have p0003 := @g_n_1stex
  have p0004 := @g_crossex
  have p0005 := @g_n_2ndex
  have p0007 := @g_txpex (syn_c2nd) (syn_c2nd) p0005 p0005
  have p0008 := @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0004 p0007
  have p0009 :=
    @g_txpex (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) p0003
      p0008
  have p0010 :=
    @g_cnvex
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0009
  have p0011 := @g_ssetex
  have p0012 :=
    @g_imaex
      (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
      (syn_csset) p0010 p0011
  have p0013 :=
    @g_eqeltri (syn_chwrels)
      (syn_cima (syn_ccnv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
        (syn_csset))
      (syn_cvv) p0002 p0012
  have p0014 := @g_inex (syn_chwcodes A) (syn_chwrels) p0001 p0013
  have p0015 :=
    @g_eqeltri (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0000
      p0014
  exact p0015

@[expose]
noncomputable def g_hwnisoex (A : Class)
    (hyp_hwnisoex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chwniso A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwniso A))
  have p0001 := @g_hwgenex
  have p0002 := @g_hwbijex
  have p0003 := @g_vvex
  have p0004 := @g_xpex (syn_chwbij) (syn_cvv) p0002 p0003
  have p0005 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0001 p0004
  have p0006 := @g_hwcnex A hyp_hwnisoex_1
  have p0008 := @g_xpex (syn_chwcn A) (syn_chwcn A) p0006 p0006
  have p0009 :=
    @g_inex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0005 p0008
  have p0010 :=
    @g_eqeltri (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_cvv) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_hnordex (A : Class)
    (hyp_hnordex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_chnord A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnord A))
  have p0001 := @g_hwnisoex A hyp_hnordex_1
  have p0002 := @g_hwcnex A hyp_hnordex_1
  have p0003 := @g_qsex (syn_chwcn A) (syn_chwniso A) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv) p0000
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

@[expose]
noncomputable def g_elhwrrels (u : Var) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv u) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwrels))
  have p0001 :=
    @g_eleq2i (syn_chwrels)
      (syn_cima (syn_ccnv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
        (syn_csset))
      (.cv u) p0000
  have p0002 := @g_n_1stfo
  have p0003 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_fncross
  have p0006 := @g_n_2ndfo
  have p0007 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0008 := Nominal.mp p0006 p0007
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0008 p0008
  have p0013 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @g_inidm (syn_cvv)
  have p0016 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd))
      p0015
  have p0017 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0014 p0016
  have p0018 := @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0019 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv))
      (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0005 p0017 p0018
  have p0020 := @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0004
      p0021
  have p0023 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0024 := Nominal.mp p0022 p0023
  have p0026 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0015
  have p0027 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (syn_cvv))
      p0024 p0026
  have p0028 :=
    @g_elpreima (syn_cvv) (.cv u) (syn_csset)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @g_vex u
  have p0031 :=
    @g_biantrur (.classMem (.cv u) (syn_cvv))
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      p0030
  have p0032 :=
    @g_bicomi
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv
            (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
            (.cv u)) (syn_csset)))
      p0031
  have p0033 :=
    @g_bitri
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv
            (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
            (.cv u)) (syn_csset)))
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      p0029 p0032
  have p0034 := @g_eqid (syn_cfv (syn_c1st) (.cv u))
  have p0039 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0004 p0030
  have p0040 := @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c1st) (.cv u)) (syn_c1st)
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @g_mpbi (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) p0034 p0041
  have p0043 :=
    @g_eqid (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
  have p0062 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0021 p0030
  have p0063 :=
    @g_fnbrfvb (syn_cvv) (.cv u)
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0064 := Nominal.mp p0062 p0063
  have p0065 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      p0043 p0064
  have p0066 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      p0042 p0065
  have p0067 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0068 :=
    @g_mpbir
      (syn_wbr (.cv u)
        (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))))
      (syn_wa (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u)))
        (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
          (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))))
      p0066 p0067
  have p0095 :=
    @g_fnfun (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0096 := Nominal.mp p0027 p0095
  have p0097 :=
    @g_funbrfv (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0098 := Nominal.mp p0096 p0097
  have p0099 := Nominal.mp p0068 p0098
  have p0113 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0017 p0030
  have p0114 := @g_fvco2 (syn_cvv) (.cv u) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0115 := Nominal.mp p0113 p0114
  have p0116 := @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0121 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0008 p0030
  have p0122 := @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
  have p0123 := Nominal.mp p0121 p0122
  have p0124 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0116 p0123
  have p0134 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0124 p0124
  have p0135 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
      (syn_c2nd)
  have p0136 :=
    @g_mpbir
      (syn_wbr (.cv u) (syn_ctxp (syn_c2nd) (syn_c2nd))
        (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))))
      p0134 p0135
  have p0149 := @g_fnfun (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0150 := Nominal.mp p0017 p0149
  have p0151 :=
    @g_funbrfv (.cv u) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0152 := Nominal.mp p0150 p0151
  have p0153 := Nominal.mp p0136 p0152
  have p0154 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u))
      (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_ccross)
      p0153
  have p0155 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u)))
      (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0115 p0154
  have p0156 :=
    (Nominal.classEqRefl
      (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u))))
  have p0157 := @g_fvex (.cv u) (syn_c2nd)
  have p0159 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv))
      (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) p0157 p0157
  have p0160 :=
    @g_ovcross (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)
      (syn_cvv)
  have p0161 := Nominal.mp p0159 p0160
  have p0162 :=
    @g_eqtr3i
      (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0156 p0161
  have p0163 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0155 p0162
  have p0164 :=
    @g_opeq2i (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) p0163
  have p0165 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (.cv u))
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0099 p0164
  have p0166 :=
    @g_eleq1i
      (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (.cv u))
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_csset) p0165
  have p0167 :=
    @g_bitri
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset))
      p0033 p0166
  have p0168 :=
    (Nominal.biimpRefl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset)
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0169 := @g_fvex (.cv u) (syn_c1st)
  have p0172 :=
    @g_xpex (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0157 p0157
  have p0173 :=
    @g_brsset (syn_cfv (syn_c1st) (.cv u))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0169 p0172
  have p0174 :=
    @g_bitr3i
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset)
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0168 p0173
  have p0175 :=
    @g_bitri
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0167 p0174
  have p0176 :=
    @g_bitri (.classMem (.cv u) (syn_chwrels))
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0001 p0175
  exact p0176

@[expose]
noncomputable def g_elhwcn (u : Var) (A : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A))
          (syn_wss (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcn A))
  have p0001 :=
    @g_eleq2i (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (.cv u) p0000
  have p0002 := @g_elin (.cv u) (syn_chwcodes A) (syn_chwrels)
  have p0003 := (Nominal.classEqRefl (syn_chwrels))
  have p0004 :=
    @g_eleq2i (syn_chwrels)
      (syn_cima (syn_ccnv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))))
        (syn_csset))
      (.cv u) p0003
  have p0005 := @g_n_1stfo
  have p0006 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_fncross
  have p0009 := @g_n_2ndfo
  have p0010 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0011 := Nominal.mp p0009 p0010
  have p0015 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0011 p0011
  have p0016 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @g_inidm (syn_cvv)
  have p0019 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd))
      p0018
  have p0020 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0017 p0019
  have p0021 := @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0022 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv))
      (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0008 p0020 p0021
  have p0023 := @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0007
      p0024
  have p0026 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0027 := Nominal.mp p0025 p0026
  have p0029 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0018
  have p0030 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (syn_cvv))
      p0027 p0029
  have p0031 :=
    @g_elpreima (syn_cvv) (.cv u) (syn_csset)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := @g_vex u
  have p0034 :=
    @g_biantrur (.classMem (.cv u) (syn_cvv))
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      p0033
  have p0035 :=
    @g_bicomi
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv
            (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
            (.cv u)) (syn_csset)))
      p0034
  have p0036 :=
    @g_bitri
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv
            (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
            (.cv u)) (syn_csset)))
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      p0032 p0035
  have p0037 := @g_eqid (syn_cfv (syn_c1st) (.cv u))
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0007 p0033
  have p0043 := @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c1st) (.cv u)) (syn_c1st)
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbi (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) p0037 p0044
  have p0046 :=
    @g_eqid (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
  have p0065 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0024 p0033
  have p0066 :=
    @g_fnbrfvb (syn_cvv) (.cv u)
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0067 := Nominal.mp p0065 p0066
  have p0068 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      p0046 p0067
  have p0069 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      p0045 p0068
  have p0070 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0071 :=
    @g_mpbir
      (syn_wbr (.cv u)
        (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))))
      (syn_wa (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u)))
        (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
          (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))))
      p0069 p0070
  have p0098 :=
    @g_fnfun (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0099 := Nominal.mp p0030 p0098
  have p0100 :=
    @g_funbrfv (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0101 := Nominal.mp p0099 p0100
  have p0102 := Nominal.mp p0071 p0101
  have p0116 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv))
      (.classMem (.cv u) (syn_cvv)) p0020 p0033
  have p0117 := @g_fvco2 (syn_cvv) (.cv u) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0118 := Nominal.mp p0116 p0117
  have p0119 := @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0124 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0011 p0033
  have p0125 := @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
  have p0126 := Nominal.mp p0124 p0125
  have p0127 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0119 p0126
  have p0137 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0127 p0127
  have p0138 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
      (syn_c2nd)
  have p0139 :=
    @g_mpbir
      (syn_wbr (.cv u) (syn_ctxp (syn_c2nd) (syn_c2nd))
        (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))))
      p0137 p0138
  have p0152 := @g_fnfun (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0153 := Nominal.mp p0020 p0152
  have p0154 :=
    @g_funbrfv (.cv u) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0155 := Nominal.mp p0153 p0154
  have p0156 := Nominal.mp p0139 p0155
  have p0157 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u))
      (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_ccross)
      p0156
  have p0158 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u)))
      (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0118 p0157
  have p0159 :=
    (Nominal.classEqRefl
      (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u))))
  have p0160 := @g_fvex (.cv u) (syn_c2nd)
  have p0162 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv))
      (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) p0160 p0160
  have p0163 :=
    @g_ovcross (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)
      (syn_cvv)
  have p0164 := Nominal.mp p0162 p0163
  have p0165 :=
    @g_eqtr3i
      (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0159 p0164
  have p0166 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0158 p0165
  have p0167 :=
    @g_opeq2i (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) p0166
  have p0168 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (.cv u))
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0102 p0167
  have p0169 :=
    @g_eleq1i
      (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
        (.cv u))
      (syn_cop (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_csset) p0168
  have p0170 :=
    @g_bitri
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (.classMem (syn_cfv
          (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
          (.cv u)) (syn_csset))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset))
      p0036 p0169
  have p0171 :=
    (Nominal.biimpRefl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset)
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0172 := @g_fvex (.cv u) (syn_c1st)
  have p0175 :=
    @g_xpex (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0160 p0160
  have p0176 :=
    @g_brsset (syn_cfv (syn_c1st) (.cv u))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0172 p0175
  have p0177 :=
    @g_bitr3i
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset)
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0171 p0176
  have p0178 :=
    @g_bitri
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0170 p0177
  have p0179 :=
    @g_bitri (.classMem (.cv u) (syn_chwrels))
      (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0004 p0178
  have p0180 :=
    @g_anbi2i (.classMem (.cv u) (syn_chwrels))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcodes A)) p0179
  have p0181 :=
    @g_bitri (.classMem (.cv u) (syn_cin (syn_chwcodes A) (syn_chwrels)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwrels)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0002 p0180
  have p0182 :=
    @g_bitri (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_cin (syn_chwcodes A) (syn_chwrels)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0001 p0181
  exact p0182

@[expose]
noncomputable def g_elhwbij (f : Var) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv f) (syn_chwbij))
        (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))) :=
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
  have dv_cache_0002 : g ∉ ((syn_ccnv (syn_cimage (syn_cswap)))).fv :=
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
  have dv_cache_0003 : g ∉ ((syn_cfuns)).fv :=
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
  have dv_cache_0004 : g ∉ ((syn_ccnv (.cv f))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_chwbij))
  have p0001 :=
    @g_eleq2i (syn_chwbij)
      (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))
      (.cv f) p0000
  have p0002 :=
    @g_elin (.cv f) (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))
  have p0003 :=
    @g_elima g (.cv f) (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0004 := @g_brcnv (.cv g) (.cv f) (syn_cimage (syn_cswap))
  have p0005 := @g_vex f
  have p0006 := @g_vex g
  have p0007 := @g_brimage (.cv f) (.cv g) (syn_cswap) p0005 p0006
  have p0008 :=
    @g_bitri (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f))
      (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (.cv g))
      (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f))) p0004 p0007
  have p0009 := @g_dfcnv2 (.cv f)
  have p0010 := @g_eqeq2i (syn_ccnv (.cv f)) (syn_cima (syn_cswap) (.cv f)) (.cv g) p0009
  have p0011 :=
    @g_bicomi (.classEq (.cv g) (syn_ccnv (.cv f)))
      (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f))) p0010
  have p0012 :=
    @g_bitri (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f))
      (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f)))
      (.classEq (.cv g) (syn_ccnv (.cv f))) p0008 p0011
  have p0013 :=
    @g_rexbii (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f))
      (.classEq (.cv g) (syn_ccnv (.cv f))) g (syn_cfuns) p0012
  have p0014 :=
    @g_bitri
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))
      (syn_wrex g (syn_cfuns) (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f)))
      (syn_wrex g (syn_cfuns) (.classEq (.cv g) (syn_ccnv (.cv f)))) p0003 p0013
  have p0015 := @g_risset g (syn_ccnv (.cv f)) (syn_cfuns) dv_cache_0004 dv_cache_0003
  have p0016 :=
    @g_bicomi (.classMem (syn_ccnv (.cv f)) (syn_cfuns))
      (syn_wrex g (syn_cfuns) (.classEq (.cv g) (syn_ccnv (.cv f)))) p0015
  have p0017 :=
    @g_bitri
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))
      (syn_wrex g (syn_cfuns) (.classEq (.cv g) (syn_ccnv (.cv f))))
      (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) p0014 p0016
  have p0018 :=
    @g_anbi2i
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))
      (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) (.classMem (.cv f) (syn_cfuns)) p0017
  have p0019 :=
    @g_bitri
      (.classMem (.cv f)
        (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))))
      (syn_wa (.classMem (.cv f) (syn_cfuns))
        (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))))
      (syn_wa (.classMem (.cv f) (syn_cfuns)) (.classMem (syn_ccnv (.cv f)) (syn_cfuns)))
      p0002 p0018
  have p0021 := @g_elfuns (.cv f) p0005
  have p0023 := @g_cnvex (.cv f) p0005
  have p0024 := @g_elfuns (syn_ccnv (.cv f)) p0023
  have p0025 :=
    @g_anbi12i (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f))
      (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) (syn_wfun (syn_ccnv (.cv f))) p0021 p0024
  have p0026 :=
    @g_bitri
      (.classMem (.cv f)
        (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))))
      (syn_wa (.classMem (.cv f) (syn_cfuns)) (.classMem (syn_ccnv (.cv f)) (syn_cfuns)))
      (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) p0019 p0025
  have p0027 :=
    @g_bitri (.classMem (.cv f) (syn_chwbij))
      (.classMem (.cv f)
        (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))))
      (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) p0001 p0026
  exact p0027

@[expose]
noncomputable def g_elhnord (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (_dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x)
    (hyp_elhnord_1 : Nominal.NPrf (.classMem (.cv x) (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_chnord A)) (syn_wrex u (syn_chwcn A)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))) :=
  by
  have dv_cache_0001 : u ∉ ((syn_chwcn A)).fv := by
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
  have dv_cache_0003 : u ∉ ((syn_chwniso A)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_chnord A))
  have p0001 :=
    @g_eleq2i (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (.cv x) p0000
  have p0002 :=
    @g_elqs u (syn_chwcn A) (.cv x) (syn_chwniso A) dv_cache_0001 dv_cache_0002
      dv_cache_0003 hyp_elhnord_1
  have p0003 :=
    @g_bitri (.classMem (.cv x) (syn_chnord A))
      (.classMem (.cv x) (syn_cqs (syn_chwcn A) (syn_chwniso A)))
      (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_hwnisoclasselhnord (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv)
    (hyp_hwnisoclasselhnord_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A))) :=
  by
  have p0000 := @g_hwnisoex A hyp_hwnisoclasselhnord_1
  have p0001 := @g_ecelqsi (syn_chwcn A) (.cv u) (syn_chwniso A) p0000
  have p0002 := (Nominal.classEqRefl (syn_chnord A))
  have p0003 :=
    @g_eleq2i (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A))
      (syn_cec (.cv u) (syn_chwniso A)) p0002
  have p0004 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_cqs (syn_chwcn A) (syn_chwniso A)))
      (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_imageswapfn :
    Nominal.NPrf (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) :=
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
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
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
  have dv_cache_0003 : x ∉ ((syn_cima (syn_cswap) (.cv a))).fv :=
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
  have dv_cache_0004 : a ∉ ((syn_cimage (syn_cswap))).fv :=
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
  have dv_cache_0005 : b ∉ ((syn_cimage (syn_cswap))).fv :=
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
  have dv_cache_0006 : a ∉ ((syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))).fv :=
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
  have dv_cache_0007 : b ∉ ((syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))).fv :=
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
  have p0000 := @g_swapex
  have p0001 := @g_vex x
  have p0002 := @g_imaex (syn_cswap) (.cv x) p0000 p0001
  have p0003 := @g_eqid (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))
  have p0004 :=
    @g_fnmpti x (syn_cvv) (syn_cima (syn_cswap) (.cv x))
      (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0001 p0002 p0003
  have p0005 := @g_vex a
  have p0006 := @g_vex b
  have p0007 := @g_brimage (.cv a) (.cv b) (syn_cswap) p0005 p0006
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (syn_cvv))
      (.classMem (.cv a) (syn_cvv)) p0004 p0005
  have p0015 :=
    @g_fnbrfvb (syn_cvv) (.cv a) (.cv b)
      (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_bicomi
      (.classEq (syn_cfv (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv a)) (.cv b))
      (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b))
      p0016
  have p0019 := @g_imaeq2 (.cv x) (.cv a) (syn_cswap)
  have p0023 := @g_imaex (syn_cswap) (.cv a) p0000 p0005
  have p0024 :=
    @g_fvmpt x (.cv a) (syn_cima (syn_cswap) (.cv x)) (syn_cima (syn_cswap) (.cv a))
      (syn_cvv) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0002
      dv_cache_0003 dv_cache_0001 p0019 p0003 p0023
  have p0025 := Nominal.mp p0005 p0024
  have p0026 :=
    @g_eqeq1i (syn_cfv (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv a))
      (syn_cima (syn_cswap) (.cv a)) (.cv b) p0025
  have p0027 :=
    @g_bitri
      (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b))
      (.classEq (syn_cfv (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv a)) (.cv b))
      (.classEq (syn_cima (syn_cswap) (.cv a)) (.cv b)) p0017 p0026
  have p0028 := @g_eqcom (syn_cima (syn_cswap) (.cv a)) (.cv b)
  have p0029 :=
    @g_bitri
      (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b))
      (.classEq (syn_cima (syn_cswap) (.cv a)) (.cv b))
      (.classEq (.cv b) (syn_cima (syn_cswap) (.cv a))) p0027 p0028
  have p0030 :=
    @g_bitr4i (syn_wbr (.cv a) (syn_cimage (syn_cswap)) (.cv b))
      (.classEq (.cv b) (syn_cima (syn_cswap) (.cv a)))
      (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b))
      p0007 p0029
  have p0031 :=
    @g_eqbrriv a b (syn_cimage (syn_cswap))
      (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 p0030
  have p0032 :=
    @g_fneq1i (syn_cvv) (syn_cimage (syn_cswap))
      (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) p0031
  have p0033 :=
    @g_mpbir (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv))
      (syn_wfn (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (syn_cvv)) p0004
      p0032
  exact p0033

@[expose]
noncomputable def g_imageswapval (f : Var) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_ccnv (.cv f))) :=
  by
  have p0000 := @g_eqid (syn_cima (syn_cswap) (.cv f))
  have p0001 := @g_vex f
  have p0002 := @g_swapex
  have p0004 := @g_imaex (syn_cswap) (.cv f) p0002 p0001
  have p0005 := @g_brimage (.cv f) (syn_cima (syn_cswap) (.cv f)) (syn_cswap) p0001 p0004
  have p0006 :=
    @g_mpbir (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) (.cv f)))
      (.classEq (syn_cima (syn_cswap) (.cv f)) (syn_cima (syn_cswap) (.cv f))) p0000 p0005
  have p0007 := @g_imageswapfn
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (.classMem (.cv f) (syn_cvv))
      p0007 p0001
  have p0010 :=
    @g_fnbrfvb (syn_cvv) (.cv f) (syn_cima (syn_cswap) (.cv f)) (syn_cimage (syn_cswap))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_mpbir
      (.classEq (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_cima (syn_cswap) (.cv f)))
      (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) (.cv f))) p0006
      p0011
  have p0013 := @g_dfcnv2 (.cv f)
  have p0014 :=
    @g_eqtr4i (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_cima (syn_cswap) (.cv f))
      (syn_ccnv (.cv f)) p0012 p0013
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

@[expose]
noncomputable def g_hwtrnfn : Nominal.NPrf (syn_wfn (syn_chwtrn) (syn_cvv)) :=
  by
  have p0000 := @g_composefn
  have p0002 := @g_n_1stfo
  have p0003 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_n_2ndfo
  have p0006 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0004 p0007
  have p0009 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_inidm (syn_cvv)
  have p0012 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd))
      p0011
  have p0013 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0010 p0012
  have p0014 := @g_ssv (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0015 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv))
      (syn_wss (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) p0000 p0013 p0014
  have p0016 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @g_imageswapfn
  have p0022 := @g_ssv (syn_crn (syn_c1st))
  have p0023 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv))
      (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0018 p0004
      p0022
  have p0024 := @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0017 p0025
  have p0027 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0028 := Nominal.mp p0026 p0027
  have p0030 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
      p0011
  have p0031 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      p0028 p0030
  have p0032 :=
    @g_ssv
      (syn_crn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
  have p0033 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      (syn_wss (syn_crn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv))
      p0000 p0031 p0032
  have p0034 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose)
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0035 := Nominal.mp p0033 p0034
  have p0036 := (Nominal.classEqRefl (syn_chwtrn))
  have p0037 :=
    @g_fneq1i (syn_cvv) (syn_chwtrn)
      (syn_ccom (syn_ccompose)
        (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
      p0036
  have p0038 :=
    @g_bicomi (syn_wfn (syn_chwtrn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccompose)
          (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv))
      p0037
  have p0039 :=
    @g_mpbi
      (syn_wfn (syn_ccom (syn_ccompose)
          (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv))
      (syn_wfn (syn_chwtrn) (syn_cvv)) p0035 p0038
  exact p0039

@[expose]
noncomputable def g_hwtrnval (R : Class) (f : Var)
    (hyp_hwtrnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
        (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwtrn))
  have p0001 :=
    @g_fveq1i (syn_cop (.cv f) R) (syn_chwtrn)
      (syn_ccom (syn_ccompose)
        (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
      p0000
  have p0002 := @g_composefn
  have p0003 := @g_n_1stfo
  have p0004 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_n_2ndfo
  have p0007 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0005 p0008
  have p0010 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @g_inidm (syn_cvv)
  have p0013 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd))
      p0012
  have p0014 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0011 p0013
  have p0015 := @g_ssv (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0016 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv))
      (syn_wss (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) p0002 p0014 p0015
  have p0017 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_imageswapfn
  have p0023 := @g_ssv (syn_crn (syn_c1st))
  have p0024 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv))
      (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0019 p0005
      p0023
  have p0025 := @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0018 p0026
  have p0028 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0029 := Nominal.mp p0027 p0028
  have p0031 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
      p0012
  have p0032 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      p0029 p0031
  have p0033 := @g_vex f
  have p0034 := @g_opex (.cv f) R p0033 hyp_hwtrnval_1
  have p0035 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_ccompose)
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @g_eqid
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
  have p0058 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0018 p0034
  have p0059 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R)
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0060 := Nominal.mp p0058 p0059
  have p0061 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cop (.cv f) R)))
      p0038 p0060
  have p0062 :=
    @g_eqid (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
  have p0073 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0026 p0034
  have p0074 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R)
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
        (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))
      p0062 p0075
  have p0077 :=
    @g_pm3_2i
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
        (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))
      p0061 p0076
  have p0078 :=
    @g_trtxp (syn_cop (.cv f) R)
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0079 :=
    @g_mpbir
      (syn_wbr (syn_cop (.cv f) R)
        (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop
          (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_cop (.cv f) R))
          (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))))
      (syn_wa (syn_wbr (syn_cop (.cv f) R)
          (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_cop (.cv f) R)))
        (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
          (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))))
      p0077 p0078
  have p0111 :=
    @g_fnfun (syn_cvv)
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0112 := Nominal.mp p0032 p0111
  have p0113 :=
    @g_funbrfv (syn_cop (.cv f) R)
      (syn_cop (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
        (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0114 := Nominal.mp p0112 p0113
  have p0115 := Nominal.mp p0079 p0114
  have p0130 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0014 p0034
  have p0131 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0132 := Nominal.mp p0130 p0131
  have p0133 := @g_eqid (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
  have p0139 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv))
      p0005 p0034
  have p0140 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
      (syn_c1st)
  have p0141 := Nominal.mp p0139 p0140
  have p0142 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
        (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
      p0133 p0141
  have p0143 := @g_eqid (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
  have p0149 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv))
      p0008 p0034
  have p0150 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
      (syn_c2nd)
  have p0151 := Nominal.mp p0149 p0150
  have p0152 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
        (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      p0143 p0151
  have p0153 :=
    @g_pm3_2i
      (syn_wbr (syn_cop (.cv f) R) (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      p0142 p0152
  have p0154 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
      (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_c1st) (syn_c2nd)
  have p0155 :=
    @g_mpbir
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c1st) (syn_c2nd))
        (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
          (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))))
      (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
        (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))))
      p0153 p0154
  have p0168 := @g_fnfun (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0169 := Nominal.mp p0014 p0168
  have p0170 :=
    @g_funbrfv (syn_cop (.cv f) R)
      (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
        (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0171 := Nominal.mp p0169 p0170
  have p0172 := Nominal.mp p0155 p0171
  have p0174 := @g_opfv1st (.cv f) R p0033 hyp_hwtrnval_1
  have p0176 := @g_opfv2nd (.cv f) R p0033 hyp_hwtrnval_1
  have p0177 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f)
      (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) R p0174 p0176
  have p0178 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (.cv f) R))
      (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
        (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      (syn_cop (.cv f) R) p0172 p0177
  have p0179 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (.cv f) R))
      (syn_cop (.cv f) R) (syn_ccompose) p0178
  have p0180 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (.cv f) R)))
      (syn_cfv (syn_ccompose) (syn_cop (.cv f) R)) p0132 p0179
  have p0181 := (Nominal.classEqRefl (syn_co (.cv f) (syn_ccompose) R))
  have p0183 :=
    @g_pm3_2i (.classMem (.cv f) (syn_cvv)) (.classMem R (syn_cvv)) p0033 hyp_hwtrnval_1
  have p0184 := @g_composevalg (.cv f) R (syn_cvv) (syn_cvv)
  have p0185 := Nominal.mp p0183 p0184
  have p0186 :=
    @g_eqtr3i (syn_co (.cv f) (syn_ccompose) R)
      (syn_cfv (syn_ccompose) (syn_cop (.cv f) R)) (syn_ccom (.cv f) R) p0181 p0185
  have p0187 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccompose) (syn_cop (.cv f) R)) (syn_ccom (.cv f) R) p0180 p0186
  have p0194 := @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0195 := Nominal.mp p0139 p0194
  have p0198 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cimage (syn_cswap))
      p0174
  have p0199 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
      (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) p0195 p0198
  have p0200 := @g_imageswapval f
  have p0201 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_ccnv (.cv f)) p0199 p0200
  have p0202 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
      (syn_ccom (.cv f) R)
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_ccnv (.cv f)) p0187 p0201
  have p0203 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cop (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0115 p0202
  have p0204 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
          (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_ccompose) p0203
  have p0205 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose)
          (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccompose) (syn_cfv
          (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (.cv f) R)))
      (syn_cfv (syn_ccompose) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))) p0037
      p0204
  have p0206 :=
    (Nominal.classEqRefl (syn_co (syn_ccom (.cv f) R) (syn_ccompose) (syn_ccnv (.cv f))))
  have p0208 := @g_coex (.cv f) R p0033 hyp_hwtrnval_1
  have p0210 := @g_cnvex (.cv f) p0033
  have p0211 :=
    @g_pm3_2i (.classMem (syn_ccom (.cv f) R) (syn_cvv))
      (.classMem (syn_ccnv (.cv f)) (syn_cvv)) p0208 p0210
  have p0212 := @g_composevalg (syn_ccom (.cv f) R) (syn_ccnv (.cv f)) (syn_cvv) (syn_cvv)
  have p0213 := Nominal.mp p0211 p0212
  have p0214 :=
    @g_eqtr3i (syn_co (syn_ccom (.cv f) R) (syn_ccompose) (syn_ccnv (.cv f)))
      (syn_cfv (syn_ccompose) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f))))
      (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0206 p0213
  have p0215 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose)
          (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccompose) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f))))
      (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0205 p0214
  have p0216 :=
    @g_eqtri (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccom (syn_ccompose)
          (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
            (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop (.cv f) R))
      (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0001 p0215
  exact p0216

@[expose]
noncomputable def g_ranfnfn : Nominal.NPrf (syn_wfn (syn_cranfn) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_vex x
  have p0001 := @g_rnex (.cv x) p0000
  have p0002 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0003 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_hwgenfn : Nominal.NPrf (syn_wfn (syn_chwgen) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_n_2ndfo
  have p0001 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_vex x
  have p0004 := @g_dmex (.cv x) p0003
  have p0005 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0006 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0004 p0005
  have p0007 := @g_n_1stfo
  have p0008 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_ssv (syn_crn (syn_c1st))
  have p0011 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0006 p0009 p0010
  have p0012 := @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) p0002 p0013
  have p0015 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_inidm (syn_cvv)
  have p0018 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) p0017
  have p0019 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) p0016
      p0018
  have p0020 := @g_hwtrnfn
  have p0022 := @g_rnex (.cv x) p0003
  have p0023 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0024 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0022 p0023
  have p0029 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0024 p0009 p0010
  have p0030 := @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) p0020 p0031
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0034 := Nominal.mp p0032 p0033
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0017
  have p0037 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0034
      p0036
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0019
      p0037
  have p0039 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0040 := Nominal.mp p0038 p0039
  have p0042 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
      p0017
  have p0043 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv))
      p0040 p0042
  have p0044 := (Nominal.classEqRefl (syn_chwgen))
  have p0045 :=
    @g_fneq1i (syn_cvv) (syn_chwgen)
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
      p0044
  have p0046 :=
    @g_bicomi (syn_wfn (syn_chwgen) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv))
      p0045
  have p0047 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv))
      (syn_wfn (syn_chwgen) (syn_cvv)) p0043 p0046
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

@[expose]
noncomputable def g_hwgenval (R : Class) (f : Var)
    (hyp_hwgenval_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) R))
        (syn_cop (syn_cop R (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))))) :=
  by
  let proofSupport : Finset Var := R.fv ∪ ({ f } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_chwgen))
  have p0001 :=
    @g_fveq1i (syn_cop (.cv f) R) (syn_chwgen)
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
      p0000
  have p0002 :=
    @g_eqid
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
  have p0003 := @g_n_2ndfo
  have p0004 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_vex x
  have p0007 := @g_dmex (.cv x) p0006
  have p0008 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0009 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0007 p0008
  have p0010 := @g_n_1stfo
  have p0011 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_ssv (syn_crn (syn_c1st))
  have p0014 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0009 p0012 p0013
  have p0015 := @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) p0005 p0016
  have p0018 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @g_inidm (syn_cvv)
  have p0021 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) p0020
  have p0022 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) p0019
      p0021
  have p0023 := @g_vex f
  have p0024 := @g_opex (.cv f) R p0023 hyp_hwgenval_1
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R)
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)))
      p0002 p0027
  have p0029 :=
    @g_eqid
      (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))
  have p0030 := @g_hwtrnfn
  have p0032 := @g_rnex (.cv x) p0006
  have p0033 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0034 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0032 p0033
  have p0039 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0034 p0012 p0013
  have p0040 := @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) p0030 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0020
  have p0047 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0044
      p0046
  have p0050 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0047 p0024
  have p0051 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R)
      (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0052 := Nominal.mp p0050 p0051
  have p0053 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cop (.cv f) R))
        (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
        (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cop (.cv f) R)))
      p0029 p0052
  have p0054 :=
    @g_pm3_2i
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
        (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cop (.cv f) R)))
      p0028 p0053
  have p0055 :=
    @g_trtxp (syn_cop (.cv f) R)
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0056 :=
    @g_mpbir
      (syn_wbr (syn_cop (.cv f) R)
        (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cop
          (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
          (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
            (syn_cop (.cv f) R))))
      (syn_wa (syn_wbr (syn_cop (.cv f) R)
          (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
            (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R)
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
            (syn_cop (.cv f) R))))
      p0054 p0055
  have p0095 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0022
      p0047
  have p0096 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0097 := Nominal.mp p0095 p0096
  have p0099 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
      p0020
  have p0100 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv))
      p0097 p0099
  have p0101 :=
    @g_fnfun (syn_cvv)
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
  have p0102 := Nominal.mp p0100 p0101
  have p0103 :=
    @g_funbrfv (syn_cop (.cv f) R)
      (syn_cop (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_cop (.cv f) R))
        (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cop (.cv f) R)))
      (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
  have p0104 := Nominal.mp p0102 p0103
  have p0105 := Nominal.mp p0056 p0104
  have p0106 := @g_eqid (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
  have p0112 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv))
      p0005 p0024
  have p0113 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
      (syn_c2nd)
  have p0114 := Nominal.mp p0112 p0113
  have p0115 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
        (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      p0106 p0114
  have p0116 := @g_eqid (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))
  have p0130 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0016 p0024
  have p0131 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R)
      (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0132 := Nominal.mp p0130 p0131
  have p0133 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cdomfn) (syn_c1st))
        (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))
      p0116 p0132
  have p0134 :=
    @g_pm3_2i
      (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cdomfn) (syn_c1st))
        (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))
      p0115 p0133
  have p0135 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_c2nd)
      (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0136 :=
    @g_mpbir
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
        (syn_cop (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
          (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))))
      (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))
        (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cdomfn) (syn_c1st))
          (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))))
      p0134 p0135
  have p0157 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
  have p0158 := Nominal.mp p0022 p0157
  have p0159 :=
    @g_funbrfv (syn_cop (.cv f) R)
      (syn_cop (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
  have p0160 := Nominal.mp p0158 p0159
  have p0161 := Nominal.mp p0136 p0160
  have p0163 := @g_opfv2nd (.cv f) R p0023 hyp_hwgenval_1
  have p0169 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv))
      p0012 p0024
  have p0170 := @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_cdomfn) (syn_c1st)
  have p0171 := Nominal.mp p0169 p0170
  have p0173 := @g_opfv1st (.cv f) R p0023 hyp_hwgenval_1
  have p0174 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cdomfn) p0173
  have p0175 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_cfv (syn_cdomfn) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
      (syn_cfv (syn_cdomfn) (.cv f)) p0171 p0174
  have p0177 := @g_fvdomfn (.cv f) (syn_cvv)
  have p0178 := Nominal.mp p0023 p0177
  have p0179 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_cfv (syn_cdomfn) (.cv f)) (syn_cdm (.cv f)) p0175 p0178
  have p0180 :=
    @g_opeq12i (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) R
      (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cdm (.cv f))
      p0163 p0179
  have p0181 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cop (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_cop R (syn_cdm (.cv f))) p0161 p0180
  have p0182 := @g_eqid (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
  have p0186 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv))
      p0030 p0024
  have p0187 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
      (syn_chwtrn)
  have p0188 := Nominal.mp p0186 p0187
  have p0189 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
        (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_chwtrn) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)))
      p0182 p0188
  have p0190 := @g_eqid (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))
  have p0204 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv))
      (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0041 p0024
  have p0205 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R)
      (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_ccom (syn_cranfn) (syn_c1st))
  have p0206 := Nominal.mp p0204 p0205
  have p0207 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cranfn) (syn_c1st))
        (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))
      p0190 p0206
  have p0208 :=
    @g_pm3_2i
      (syn_wbr (syn_cop (.cv f) R) (syn_chwtrn) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)))
      (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cranfn) (syn_c1st))
        (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))
      p0189 p0207
  have p0209 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
      (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_chwtrn)
      (syn_ccom (syn_cranfn) (syn_c1st))
  have p0210 :=
    @g_mpbir
      (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
        (syn_cop (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
          (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))))
      (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_chwtrn)
          (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)))
        (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cranfn) (syn_c1st))
          (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))))
      p0208 p0209
  have p0229 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0230 := Nominal.mp p0047 p0229
  have p0231 :=
    @g_funbrfv (syn_cop (.cv f) R)
      (syn_cop (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0232 := Nominal.mp p0230 p0231
  have p0233 := Nominal.mp p0210 p0232
  have p0234 := @g_hwtrnval R f hyp_hwgenval_1
  have p0241 := @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_cranfn) (syn_c1st)
  have p0242 := Nominal.mp p0169 p0241
  have p0245 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cranfn) p0173
  have p0246 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_cfv (syn_cranfn) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)))
      (syn_cfv (syn_cranfn) (.cv f)) p0242 p0245
  have p0248 := @g_fvranfn (.cv f) (syn_cvv)
  have p0249 := Nominal.mp p0023 p0248
  have p0250 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))
      (syn_cfv (syn_cranfn) (.cv f)) (syn_crn (.cv f)) p0246 p0249
  have p0251 :=
    @g_opeq12i (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
      (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))
      (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_crn (.cv f))
      p0234 p0250
  have p0252 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cop (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
        (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))
      (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))) p0233
      p0251
  have p0253 :=
    @g_opeq12i
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cop R (syn_cdm (.cv f)))
      (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))
      (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))) p0181
      p0252
  have p0254 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cop (.cv f) R))
      (syn_cop (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_cop (.cv f) R))
        (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
          (syn_cop (.cv f) R)))
      (syn_cop (syn_cop R (syn_cdm (.cv f)))
        (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
      p0105 p0253
  have p0255 :=
    @g_eqtri (syn_cfv (syn_chwgen) (syn_cop (.cv f) R))
      (syn_cfv (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
          (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cop (.cv f) R))
      (syn_cop (syn_cop R (syn_cdm (.cv f)))
        (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
      p0001 p0254
  exact p0255

@[expose]
noncomputable def g_elhwnisogen (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (_dv_A_f : f ∉ A.fv) (_dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
              (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
                (syn_cop (.cv u) (.cv v))))))) :=
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
  have dv_cache_0001 : p ∉ ((syn_cxp (syn_chwbij) (syn_cvv))).fv := by
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
  have dv_cache_0002 : p ∉ ((syn_cop (.cv u) (.cv v))).fv :=
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
  have dv_cache_0003 : p ∉ ((syn_chwgen)).fv :=
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
  have dv_cache_0004 : p ∉ ((syn_chwbij)).fv :=
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
  have dv_cache_0005 : f ∉ ((syn_chwbij)).fv :=
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
  have dv_cache_0006 : r ∉ ((syn_chwbij)).fv :=
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
  have dv_cache_0007 : p ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0008 : f ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0009 : r ∉ ((syn_cvv)).fv :=
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
    f ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v)))).fv :=
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
    r ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v)))).fv :=
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
      ((Wff.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
          (syn_cop (.cv u) (.cv v)))).fv :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
  have p0001 := (Nominal.classEqRefl (syn_chwniso A))
  have p0002 :=
    @g_eleq2i (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_cop (.cv u) (.cv v)) p0001
  have p0003 :=
    @g_elin (syn_cop (.cv u) (.cv v))
      (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cxp (syn_chwcn A) (syn_chwcn A))
  have p0004 := @g_hwgenfn
  have p0005 := @g_ssv (syn_cxp (syn_chwbij) (syn_cvv))
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_chwgen) (syn_cvv))
      (syn_wss (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_fvelimab p (syn_cvv) (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cop (.cv u) (.cv v))
      (syn_chwgen) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_fveq2 (.cv p) (syn_cop (.cv f) (.cv r)) (syn_chwgen)
  have p0010 :=
    @g_eqeq1d (.classEq (.cv p) (syn_cop (.cv f) (.cv r))) (syn_cfv (syn_chwgen) (.cv p))
      (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)) p0009
  have p0011 :=
    @g_rexxp (.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v)))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))
      p f r (syn_chwbij) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 p0010
  have p0012 :=
    @g_bitri
      (.classMem (syn_cop (.cv u) (.cv v))
        (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))
      (syn_wrex p (syn_cxp (syn_chwbij) (syn_cvv))
        (.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (.cv v)))))
      p0008 p0011
  have p0013 := @g_opelxp (.cv u) (.cv v) (syn_chwcn A) (syn_chwcn A)
  have p0014 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv u) (.cv v))
        (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (.cv v)))))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0012
      p0013
  have p0015 :=
    @g_ancom
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0016 :=
    @g_bitri
      (syn_wa (.classMem (syn_cop (.cv u) (.cv v))
          (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))
        (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (syn_wa (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v)))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v))))))
      p0014 p0015
  have p0017 :=
    @g_bitri
      (.classMem (syn_cop (.cv u) (.cv v))
        (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (syn_wa (.classMem (syn_cop (.cv u) (.cv v))
          (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))
        (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v))))))
      p0003 p0016
  have p0018 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A))
      (.classMem (syn_cop (.cv u) (.cv v))
        (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v))))))
      p0002 p0017
  have p0019 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v))))))
      p0000 p0018
  exact p0019

@[expose]
noncomputable def g_elhwnisogenval (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
              (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v))))))) :=
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
    @g_elhwnisogen v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @g_vex r
  have p0002 := @g_hwgenval (.cv r) f p0001
  have p0003 :=
    @g_eqeq1i (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
      (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
        (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
      (syn_cop (.cv u) (.cv v)) p0002
  have p0004 :=
    @g_opth (syn_cop (.cv r) (syn_cdm (.cv f)))
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (.cv u) (.cv v)
  have p0005 :=
    @g_bitri
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))
      (.classEq (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f)))
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))
        (syn_cop (.cv u) (.cv v)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      p0003 p0004
  have p0006 :=
    @g_rexbii
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      r (syn_cvv) p0005
  have p0007 :=
    @g_rexbii
      (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
          (syn_cop (.cv u) (.cv v))))
      (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
          (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (.cv v))))
      f (syn_chwbij) p0006
  have p0008 :=
    @g_anbi2i
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (.cv v)))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      p0000 p0008
  exact p0009

@[expose]
noncomputable def g_elhwnisogenfun (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
              (syn_wrex r (syn_cvv)
                (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                    (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                      (syn_crn (.cv f))) (.cv v)))))))) :=
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
    @g_elhwnisogenval v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v))))))
  have p0002 := @g_elhwbij f
  have p0003 :=
    @g_anbi1i (.classMem (.cv f) (syn_chwbij))
      (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
          (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (.cv v))))
      p0002
  have p0004 :=
    @g_exbii
      (syn_wa (.classMem (.cv f) (syn_chwbij)) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      f p0003
  have p0005 :=
    @g_bitri
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wex f (syn_wa (.classMem (.cv f) (syn_chwbij)) (syn_wrex r (syn_cvv)
            (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
          (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      p0001 p0004
  have p0006 :=
    @g_anbi2i
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
          (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
            (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      p0000 p0006
  exact p0007

@[expose]
noncomputable def g_hwbijf1o (f : Var) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv f) (syn_chwbij))
        (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))) :=
  by
  have p0000 := @g_elhwbij f
  have p0001 := @g_funfn (.cv f)
  have p0002 :=
    @g_anbi1i (syn_wfun (.cv f)) (syn_wfn (.cv f) (syn_cdm (.cv f)))
      (syn_wfun (syn_ccnv (.cv f))) p0001
  have p0003 := @g_f1orn (syn_cdm (.cv f)) (.cv f)
  have p0004 :=
    @g_bicomi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f)))) p0003
  have p0005 :=
    @g_bitri (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002 p0004
  have p0006 :=
    @g_bitri (.classMem (.cv f) (syn_chwbij))
      (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_elhwnisogenf1o (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
              (syn_wrex r (syn_cvv)
                (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                    (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                      (syn_crn (.cv f))) (.cv v)))))))) :=
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
    @g_elhwnisogenfun v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @g_funfn (.cv f)
  have p0002 :=
    @g_anbi1i (syn_wfun (.cv f)) (syn_wfn (.cv f) (syn_cdm (.cv f)))
      (syn_wfun (syn_ccnv (.cv f))) p0001
  have p0003 := @g_f1orn (syn_cdm (.cv f)) (.cv f)
  have p0004 :=
    @g_bicomi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f)))) p0003
  have p0005 :=
    @g_bitri (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002 p0004
  have p0006 :=
    @g_anbi1i (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
          (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
              (syn_crn (.cv f))) (.cv v))))
      p0005
  have p0007 :=
    @g_exbii
      (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      f p0006
  have p0008 :=
    @g_anbi2i
      (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
          (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
          (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
            (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
            (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      p0000 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end
