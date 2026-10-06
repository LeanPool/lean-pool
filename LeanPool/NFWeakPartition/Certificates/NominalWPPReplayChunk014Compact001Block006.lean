/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdcodemap2ex`. -/
@[expose]
noncomputable def gFdcodemap2ex (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdcodemap2ex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcodemap2ex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcodemap2ex_3 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_fdcodemap2ex_4 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (.classMem (synCfdcodemap2 R A B C) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_u_ne_d : u ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_u : d ≠ u := Ne.symm fresh_u_ne_d
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
  have dv_cache_0007 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0010 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0011 : Disjoint (A).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0012 : Disjoint (A).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (A).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0013 : Disjoint (B).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show u ∉ (B).fv from (by exact fresh_u_not_B))))))
  have dv_cache_0014 : Disjoint (B).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint (B).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0015 : Disjoint ((Class.cv u)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint ((Class.cv u)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (u),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)];
          exact
            (show Disjoint (({ u } : Finset Var)) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ ({ d } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show u ≠ d from (by exact fresh_u_ne_d))))))))
  have dv_cache_0016 : Disjoint ((Class.cv u)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint ((Class.cv u)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ u } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ (R).fv from (by exact fresh_u_not_R))))))
  have dv_cache_0017 : Disjoint ((Class.cv d)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint ((Class.cv d)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ d } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0018 : u ∉ ((synCpw1 (synCpw1 C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_u_not_C,
          not_false_eq_true])
  have dv_cache_0019 : u ∉ ((synCfdrowrel R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel,
          Finset.mem_union, fresh_u_not_A, fresh_u_not_B, fresh_u_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0020 : d ∉ ((synCfdrowrel R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0021 : d ∉ ((synCfdrowfib R A B (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_u, fresh_d_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0022 : u ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show u ≠ d from (by exact fresh_u_ne_d))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdcodemap2 u A B C R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @gA1i
      (.classEq (synCfdcodemap2 R A B C)
        (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))))
      (synWbr R (synCwe) A) p0000
  have p0002 := @gVex d
  have p0003 :=
    @gElfdrowfibg A B (.cv u) (.cv d) R dv_cache_0001 dv_cache_0011 dv_cache_0012
      dv_cache_0003 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0016
      dv_cache_0017
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gBicomi (.classMem (.cv d) (synCfdrowfib R A B (.cv u)))
      (.classMem (synCop (synCsn (.cv d)) (.cv u)) (synCfdrowrel R A B)) p0004
  have p0006 :=
    @gReleqmpt u d (synCpw1 (synCpw1 C)) (synCfdrowrel R A B)
      (synCfdrowfib R A B (.cv u)) dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0005
  have p0007 :=
    @gA1i
      (.classEq (synCin (synCxp (synCpw1 (synCpw1 C)) (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
                (synC1c)))))
        (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))))
      (synWbr R (synCwe) A) p0006
  have p0008 := @gPw1ex C hyp_fdcodemap2ex_4
  have p0009 := @gPw1ex (synCpw1 C) p0008
  have p0010 :=
    @gA1i (.classMem (synCpw1 (synCpw1 C)) (synCvv)) (synWbr R (synCwe) A) p0009
  have p0011 := @gVvex
  have p0012 := @gA1i (.classMem (synCvv) (synCvv)) (synWbr R (synCwe) A) p0011
  have p0013 :=
    @gJca (synWbr R (synCwe) A) (.classMem (synCpw1 (synCpw1 C)) (synCvv))
      (.classMem (synCvv) (synCvv)) p0010 p0012
  have p0014 := @gXpexg (synCpw1 (synCpw1 C)) (synCvv) (synCvv) (synCvv)
  have p0015 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCpw1 (synCpw1 C)) (synCvv)) (.classMem (synCvv) (synCvv)))
      (.classMem (synCxp (synCpw1 (synCpw1 C)) (synCvv)) (synCvv)) p0013 p0014
  have p0016 := @gSsetex
  have p0017 := @gIns3ex (synCsset) p0016
  have p0018 :=
    @gA1i (.classMem (synCins3 (synCsset)) (synCvv)) (synWbr R (synCwe) A) p0017
  have p0019 :=
    @gFdrowrelex2 A B R dv_cache_0001 dv_cache_0003 dv_cache_0006 hyp_fdcodemap2ex_1
      hyp_fdcodemap2ex_2 hyp_fdcodemap2ex_3
  have p0020 := @gIns2exg (synCfdrowrel R A B) (synCvv)
  have p0021 :=
    @gSyl (synWbr R (synCwe) A) (.classMem (synCfdrowrel R A B) (synCvv))
      (.classMem (synCins2 (synCfdrowrel R A B)) (synCvv)) p0019 p0020
  have p0022 :=
    @gJca (synWbr R (synCwe) A) (.classMem (synCins3 (synCsset)) (synCvv))
      (.classMem (synCins2 (synCfdrowrel R A B)) (synCvv)) p0018 p0021
  have p0023 :=
    @gSymdifexg (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)) (synCvv)
      (synCvv)
  have p0024 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCins3 (synCsset)) (synCvv))
        (.classMem (synCins2 (synCfdrowrel R A B)) (synCvv)))
      (.classMem (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
        (synCvv))
      p0022 p0023
  have p0025 := @gN1cex
  have p0026 := @gA1i (.classMem (synC1c) (synCvv)) (synWbr R (synCwe) A) p0025
  have p0027 :=
    @gJca (synWbr R (synCwe) A)
      (.classMem (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
        (synCvv))
      (.classMem (synC1c) (synCvv)) p0024 p0026
  have p0028 :=
    @gImaexg (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
      (synC1c) (synCvv) (synCvv)
  have p0029 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synCvv)) (.classMem (synC1c) (synCvv)))
      (.classMem
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synC1c)) (synCvv))
      p0027 p0028
  have p0030 :=
    @gComplexg
      (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
        (synC1c))
      (synCvv)
  have p0031 :=
    @gSyl (synWbr R (synCwe) A)
      (.classMem
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synC1c)) (synCvv))
      (.classMem (synCcompl (synCima
            (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B))) (synC1c)))
        (synCvv))
      p0029 p0030
  have p0032 :=
    @gCnvexg
      (synCcompl
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synC1c)))
      (synCvv)
  have p0033 :=
    @gSyl (synWbr R (synCwe) A)
      (.classMem (synCcompl (synCima
            (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B))) (synC1c)))
        (synCvv))
      (.classMem (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
              (synC1c)))) (synCvv))
      p0031 p0032
  have p0034 :=
    @gJca (synWbr R (synCwe) A)
      (.classMem (synCxp (synCpw1 (synCpw1 C)) (synCvv)) (synCvv))
      (.classMem (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
              (synC1c)))) (synCvv))
      p0015 p0033
  have p0035 :=
    @gInexg (synCxp (synCpw1 (synCpw1 C)) (synCvv))
      (synCcnv (synCcompl (synCima
            (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B))) (synC1c))))
      (synCvv) (synCvv)
  have p0036 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCxp (synCpw1 (synCpw1 C)) (synCvv)) (synCvv)) (.classMem
          (synCcnv (synCcompl (synCima
                (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
                (synC1c)))) (synCvv)))
      (.classMem (synCin (synCxp (synCpw1 (synCpw1 C)) (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
                (synC1c))))) (synCvv))
      p0034 p0035
  have p0037 :=
    @gEqeltrrd (synWbr R (synCwe) A)
      (synCin (synCxp (synCpw1 (synCpw1 C)) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
              (synC1c)))))
      (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))) (synCvv) p0007
      p0036
  have p0038 :=
    @gEqeltrd (synWbr R (synCwe) A) (synCfdcodemap2 R A B C)
      (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))) (synCvv) p0001
      p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_fdcodeeqrnmap2`. -/
@[expose]
noncomputable def gFdcodeeqrnmap2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.classEq (synCfdcode R A B C) (synCrn (synCfdcodemap2 R A B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_q_ne_x : q ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
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
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : q ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_B, not_false_eq_true])
  have dv_cache_0009 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0010 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0011 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0012 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0013 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0014 : x ∉ (R).fv :=
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
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0015 : q ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0016 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0017 : u ∉ (B).fv :=
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
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0018 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0019 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((synCpw1 (synCpw1 C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_C,
          not_false_eq_true])
  have dv_cache_0021 : q ∉ ((synCfdrowfib R A B (.cv u))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, fresh_q_ne_u, fresh_q_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0022 : u ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show u ≠ q from (by exact fresh_u_ne_q))
  have dv_cache_0023 : x ∉ ((Class.cv u)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Wff.classEq (.cv q) (synCfdrowfib R A B (.cv u)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A, fresh_x_not_B, fresh_x_ne_u,
          fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0025 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have dv_cache_0026 : Disjoint (A).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (show Disjoint (A).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0027 : Disjoint (A).fv ((synCsn (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (show Disjoint (A).fv ((synCsn (synCsn (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint ((A).fv) (((synCsn (.cv x))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint ((A).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))))
  have dv_cache_0028 : Disjoint (B).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (show Disjoint (B).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show u ∉ (B).fv from (by exact fresh_u_not_B))))))
  have dv_cache_0029 : Disjoint (B).fv ((synCsn (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (show Disjoint (B).fv ((synCsn (synCsn (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint ((B).fv) (((synCsn (.cv x))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint ((B).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))))
  have dv_cache_0030 : Disjoint ((Class.cv u)).fv ((synCsn (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (show Disjoint ((Class.cv u)).fv ((synCsn (synCsn (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (({ u } : Finset Var)) (((synCsn (.cv x))).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint (({ u } : Finset Var)) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ u } : Finset Var)) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show u ∉ ({ x } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show u ≠ x from (by exact fresh_u_ne_x))))))))))))
  have dv_cache_0031 : Disjoint ((Class.cv u)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (show Disjoint ((Class.cv u)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ u } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ (R).fv from (by exact fresh_u_not_R))))))
  have dv_cache_0032 : Disjoint ((synCsn (synCsn (.cv x)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (show Disjoint ((synCsn (synCsn (.cv x)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (((synCsn (.cv x))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint (((Class.cv x)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ (R).fv from (by exact fresh_x_not_R))))))))))
  have dv_cache_0033 : u ∉ ((synCsn (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_x,
          not_false_eq_true])
  have dv_cache_0034 :
    u ∉ ((Wff.classEq (.cv q) (synCfdrowfib R A B (synCsn (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_not_B, fresh_u_ne_x,
          fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0035 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0036 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0037 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdcode x A B C R q
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdcodemap2 u A B C R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0016 dv_cache_0006 dv_cache_0007
      dv_cache_0017 dv_cache_0010 dv_cache_0018 dv_cache_0019
  have p0002 :=
    @gRnmpt u q (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))
      (synCfdcodemap2 R A B C) dv_cache_0020 dv_cache_0021 dv_cache_0022 p0001
  have p0003 :=
    (Nominal.biimpRefl (synWrex u (synCpw1 (synCpw1 C))
        (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
  have p0004 := @gElpw12 x (.cv u) C dv_cache_0023 dv_cache_0012
  have p0005 :=
    @gAnbi1i (.classMem (.cv u) (synCpw1 (synCpw1 C)))
      (synWrex x C (.classEq (.cv u) (synCsn (synCsn (.cv x)))))
      (.classEq (.cv q) (synCfdrowfib R A B (.cv u))) p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv u) (synCpw1 (synCpw1 C)))
        (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWa (synWrex x C (.classEq (.cv u) (synCsn (synCsn (.cv x)))))
        (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      u p0005
  have p0007 :=
    @gBitri
      (synWrex u (synCpw1 (synCpw1 C)) (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWex u (synWa (.classMem (.cv u) (synCpw1 (synCpw1 C)))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      (synWex u (synWa (synWrex x C (.classEq (.cv u) (synCsn (synCsn (.cv x)))))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      p0003 p0006
  have p0008 :=
    @gR1941v (.classEq (.cv u) (synCsn (synCsn (.cv x))))
      (.classEq (.cv q) (synCfdrowfib R A B (.cv u))) x C dv_cache_0024
  have p0009 :=
    @gBicomi
      (synWrex x C (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      (synWa (synWrex x C (.classEq (.cv u) (synCsn (synCsn (.cv x)))))
        (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      p0008
  have p0010 :=
    @gExbii
      (synWa (synWrex x C (.classEq (.cv u) (synCsn (synCsn (.cv x)))))
        (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWrex x C (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      u p0009
  have p0011 :=
    @gBitri
      (synWrex u (synCpw1 (synCpw1 C)) (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWex u (synWa (synWrex x C (.classEq (.cv u) (synCsn (synCsn (.cv x)))))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      (synWex u (synWrex x C (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
            (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))))
      p0007 p0010
  have p0012 :=
    @gRexcom4
      (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
        (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      x u C dv_cache_0018 dv_cache_0025
  have p0013 :=
    @gBicomi
      (synWrex x C (synWex u (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
            (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))))
      (synWex u (synWrex x C (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
            (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))))
      p0012
  have p0014 :=
    @gBitri
      (synWrex u (synCpw1 (synCpw1 C)) (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWex u (synWrex x C (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
            (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))))
      (synWrex x C (synWex u (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
            (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))))
      p0011 p0013
  have p0015 := @gSnex (synCsn (.cv x))
  have p0016 :=
    @gFdrowfibeq4 A B (.cv u) (synCsn (synCsn (.cv x))) R dv_cache_0001 dv_cache_0026
      dv_cache_0027 dv_cache_0003 dv_cache_0028 dv_cache_0029 dv_cache_0007 dv_cache_0030
      dv_cache_0031 dv_cache_0032
  have p0017 :=
    @gEqeq2d (.classEq (.cv u) (synCsn (synCsn (.cv x)))) (synCfdrowfib R A B (.cv u))
      (synCfdrowfib R A B (synCsn (synCsn (.cv x)))) (.cv q) p0016
  have p0018 :=
    @gCeqsexv (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))
      (.classEq (.cv q) (synCfdrowfib R A B (synCsn (synCsn (.cv x))))) u
      (synCsn (synCsn (.cv x))) dv_cache_0033 dv_cache_0034 p0015 p0017
  have p0019 :=
    @gRexbii
      (synWex u (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      (.classEq (.cv q) (synCfdrowfib R A B (synCsn (synCsn (.cv x))))) x C p0018
  have p0020 :=
    @gBitri
      (synWrex u (synCpw1 (synCpw1 C)) (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWrex x C (synWex u (synWa (.classEq (.cv u) (synCsn (synCsn (.cv x))))
            (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))))
      (synWrex x C (.classEq (.cv q) (synCfdrowfib R A B (synCsn (synCsn (.cv x))))))
      p0014 p0019
  have p0021 := @gVex x
  have p0022 :=
    @gFdrowfibsn2 A B (.cv x) R dv_cache_0001 dv_cache_0035 dv_cache_0003 dv_cache_0036
      dv_cache_0007 dv_cache_0037 p0021
  have p0023 :=
    @gEqeq2i (synCfdrowfib R A B (synCsn (synCsn (.cv x)))) (synCfdrow R A B (.cv x))
      (.cv q) p0022
  have p0024 :=
    @gRexbii (.classEq (.cv q) (synCfdrowfib R A B (synCsn (synCsn (.cv x)))))
      (.classEq (.cv q) (synCfdrow R A B (.cv x))) x C p0023
  have p0025 :=
    @gBitri
      (synWrex u (synCpw1 (synCpw1 C)) (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWrex x C (.classEq (.cv q) (synCfdrowfib R A B (synCsn (synCsn (.cv x))))))
      (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x)))) p0020 p0024
  have p0026 :=
    @gAbbii
      (synWrex u (synCpw1 (synCpw1 C)) (.classEq (.cv q) (synCfdrowfib R A B (.cv u))))
      (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x)))) q p0025
  have p0027 :=
    @gEqtri (synCrn (synCfdcodemap2 R A B C))
      (.cab q (synWrex u (synCpw1 (synCpw1 C))
          (.classEq (.cv q) (synCfdrowfib R A B (.cv u)))))
      (.cab q (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x))))) p0002 p0026
  have p0028 :=
    @gEqtr4i (synCfdcode R A B C)
      (.cab q (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x)))))
      (synCrn (synCfdcodemap2 R A B C)) p0000 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_fdcodeex2`. -/
@[expose]
noncomputable def gFdcodeex2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdcodeex2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcodeex2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcodeex2_3 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_fdcodeex2_4 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (.classMem (synCfdcode R A B C) (synCvv))) :=
  by
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
  have dv_cache_0004 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0005 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @gFdcodeeqrnmap2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gA1i (.classEq (synCfdcode R A B C) (synCrn (synCfdcodemap2 R A B C)))
      (synWbr R (synCwe) A) p0000
  have p0002 :=
    @gFdcodemap2ex A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdcodeex2_1 hyp_fdcodeex2_2 hyp_fdcodeex2_3
      hyp_fdcodeex2_4
  have p0003 := @gRnexg (synCfdcodemap2 R A B C) (synCvv)
  have p0004 :=
    @gSyl (synWbr R (synCwe) A) (.classMem (synCfdcodemap2 R A B C) (synCvv))
      (.classMem (synCrn (synCfdcodemap2 R A B C)) (synCvv)) p0002 p0003
  have p0005 :=
    @gEqeltrd (synWbr R (synCwe) A) (synCfdcode R A B C)
      (synCrn (synCfdcodemap2 R A B C)) (synCvv) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fdcodeelpwpw2`. -/
@[expose]
noncomputable def gFdcodeelpwpw2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdcodeelpwpw2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcodeelpwpw2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcodeelpwpw2_3 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_fdcodeelpwpw2_4 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A)
        (.classMem (synCfdcode R A B C) (synCpw (synCpw (synCfdif R A B))))) :=
  by
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
  have dv_cache_0004 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0005 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @gFdcodesspw2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gA1i (synWss (synCfdcode R A B C) (synCpw (synCfdif R A B)))
      (synWbr R (synCwe) A) p0000
  have p0002 :=
    @gFdcodeex2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdcodeelpwpw2_1 hyp_fdcodeelpwpw2_2
      hyp_fdcodeelpwpw2_3 hyp_fdcodeelpwpw2_4
  have p0003 := @gElpwg (synCfdcode R A B C) (synCpw (synCfdif R A B)) (synCvv)
  have p0004 :=
    @gSyl (synWbr R (synCwe) A) (.classMem (synCfdcode R A B C) (synCvv))
      (synWb (.classMem (synCfdcode R A B C) (synCpw (synCpw (synCfdif R A B))))
        (synWss (synCfdcode R A B C) (synCpw (synCfdif R A B))))
      p0002 p0003
  have p0005 :=
    @gMpbird (synWbr R (synCwe) A)
      (.classMem (synCfdcode R A B C) (synCpw (synCpw (synCfdif R A B))))
      (synWss (synCfdcode R A B C) (synCpw (synCfdif R A B))) p0001 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdroweq4`. -/
@[expose]
noncomputable def gFdroweq4 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq C D) (.classEq (synCfdrow R A B C) (synCfdrow R A B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : d ∉ ((Wff.classEq C D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_d_not_C, fresh_d_not_D, or_false, not_false_eq_true])
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
  have dv_cache_0005 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0009 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0010 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0011 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0012 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0013 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0014 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0015 : d ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have p0000 := @gId (.classEq C D)
  have p0001 := @gEleq1d (.classEq C D) C D (.cv d) p0000
  have p0002 :=
    @gRabbidv (.classEq C D) (.classMem C (.cv d)) (.classMem D (.cv d)) d
      (synCfdif R A B) dv_cache_0001 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdrow A B C R d
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdrow A B D R d
      dv_cache_0002 dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0013 dv_cache_0007
      dv_cache_0008 dv_cache_0014 dv_cache_0015 dv_cache_0011
  have p0005 :=
    @gN3eqtr4g (.classEq C D) (synCrab d (synCfdif R A B) (.classMem C (.cv d)))
      (synCrab d (synCfdif R A B) (.classMem D (.cv d))) (synCfdrow R A B C)
      (synCfdrow R A B D) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elfdcode2g`. -/
@[expose]
noncomputable def gElfdcode2g (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv)
    (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem D (synCvv)) (synWb (.classMem D (synCfdcode R A B C))
          (synWrex x C (.classEq D (synCfdrow R A B (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv q) D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, dv_D_x, or_false, not_false_eq_true])
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
  have dv_cache_0004 : Disjoint (A).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (A).fv from (by exact fresh_q_not_A))))))
  have dv_cache_0005 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
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
  have dv_cache_0007 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0008 : Disjoint (B).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (B).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (B).fv from (by exact fresh_q_not_B))))))
  have dv_cache_0009 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0010 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0011 : Disjoint (C).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (C).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (C).fv from (by exact fresh_q_not_C))))))
  have dv_cache_0012 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0013 : x ∉ (C).fv :=
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
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0014 : Disjoint ((Class.cv q)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint ((Class.cv q)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ q } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show q ∉ (R).fv from (by exact fresh_q_not_R))))))
  have dv_cache_0015 : x ∉ ((Class.cv q)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_q, not_false_eq_true])
  have dv_cache_0016 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0017 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0018 : q ∉ ((Wff.classMem D (synCfdcode R A B C))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode, Finset.mem_union,
          fresh_q_not_D, fresh_q_not_A, fresh_q_not_B, fresh_q_not_C, fresh_q_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((synWrex x C (.classEq D (synCfdrow R A B (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_C, fresh_q_not_D, fresh_q_not_A,
          fresh_q_not_B, fresh_q_ne_x, fresh_q_not_R, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gId (.classEq (.cv q) D)
  have p0001 := @gEleq1d (.classEq (.cv q) D) (.cv q) D (synCfdcode R A B C) p0000
  have p0003 := @gEqeq1d (.classEq (.cv q) D) (.cv q) D (synCfdrow R A B (.cv x)) p0000
  have p0004 :=
    @gRexbidv (.classEq (.cv q) D) (.classEq (.cv q) (synCfdrow R A B (.cv x)))
      (.classEq D (synCfdrow R A B (.cv x))) x C dv_cache_0001 p0003
  have p0005 := @gVex q
  have p0006 :=
    @gElfdcodeg x A B C (.cv q) R dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gVtoclbg (.classMem (.cv q) (synCfdcode R A B C))
      (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x))))
      (.classMem D (synCfdcode R A B C))
      (synWrex x C (.classEq D (synCfdrow R A B (.cv x)))) q D (synCvv) dv_cache_0017
      dv_cache_0018 dv_cache_0019 p0001 p0004 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdcodesub2`. -/
@[expose]
noncomputable def gFdcodesub2 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_fdcodesub2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcodesub2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcodesub2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (synWss C D)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
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
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0003 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : Disjoint (B).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (B).fv from (by exact fresh_y_not_B))))))
  have dv_cache_0006 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint ((Class.cv y)).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((Class.cv y)).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (y),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (x)];
          exact
            (show Disjoint (({ y } : Finset Var)) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ ({ x } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show y ≠ x from (by exact fresh_y_ne_x))))))))
  have dv_cache_0009 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0010 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0011 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0012 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0013 :
    y ∉ ((Wff.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv x)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0014 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0015 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0016 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0017 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0018 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0019 : y ∉ ((synCfdrow R A B (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0021 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0022 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0023 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0024 : y ∉ (D).fv :=
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
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0025 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0026 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0027 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0028 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0029 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0030 : y ∉ ((Wff.classMem (.cv x) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, or_false, not_false_eq_true])
  have dv_cache_0031 :
    y ∉
      ((synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
              (synWa (.classMem C A) (.classMem D A)))
            (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
          (.classMem (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A, fresh_y_not_B,
          fresh_y_not_C, fresh_y_not_D, fresh_y_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0032 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0033 :
    x ∉
      ((synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem (.cv x) C)
  have p0001 := @gEqid (synCfdrow R A B (.cv x))
  have p0002 :=
    @gA1i (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv x)))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      p0001
  have p0003 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv x) C)
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv x))) p0000 p0002
  have p0004 :=
    @gFdroweq4 A B (.cv y) (.cv x) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0005 :=
    @gEqeq2d (.classEq (.cv y) (.cv x)) (synCfdrow R A B (.cv y))
      (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv x)) p0004
  have p0006 :=
    @gRspcev (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv x))) y (.cv x) C
      dv_cache_0011 dv_cache_0012 dv_cache_0013 p0005
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWa (.classMem (.cv x) C)
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv x))))
      (synWrex y C (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      p0003 p0006
  have p0008 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem (.cv x) C)
  have p0009 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (.classEq (synCfdcode R A B C) (synCfdcode R A B D))
  have p0010 :=
    @gSimpl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem C A) (.classMem D A))
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) p0009 p0010
  have p0012 := @gSimpl (synWbr R (synCwe) A) (synWss A (synCpw B))
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) (synWbr R (synCwe) A)
      p0011 p0012
  have p0014 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWbr R (synCwe) A) p0008 p0013
  have p0015 :=
    @gFdrowex2 A B (.cv x) R dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0006
      dv_cache_0007 dv_cache_0010 hyp_fdcodesub2_1 hyp_fdcodesub2_2 hyp_fdcodesub2_3
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWbr R (synCwe) A) (.classMem (synCfdrow R A B (.cv x)) (synCvv)) p0014 p0015
  have p0017 :=
    @gElfdcode2g y A B C (synCfdrow R A B (.cv x)) R dv_cache_0001 dv_cache_0014
      dv_cache_0004 dv_cache_0015 dv_cache_0016 dv_cache_0007 dv_cache_0017 dv_cache_0018
      dv_cache_0012 dv_cache_0019 dv_cache_0020
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (synCfdrow R A B (.cv x)) (synCvv))
      (synWb (.classMem (synCfdrow R A B (.cv x)) (synCfdcode R A B C))
        (synWrex y C (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))))
      p0016 p0017
  have p0019 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (synCfdrow R A B (.cv x)) (synCfdcode R A B C))
      (synWrex y C (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      p0007 p0018
  have p0021 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (.classEq (synCfdcode R A B C) (synCfdcode R A B D))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classEq (synCfdcode R A B C) (synCfdcode R A B D)) p0008 p0021
  have p0023 :=
    @gEleq2d
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synCfdcode R A B C) (synCfdcode R A B D) (synCfdrow R A B (.cv x)) p0022
  have p0024 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (synCfdrow R A B (.cv x)) (synCfdcode R A B C))
      (.classMem (synCfdrow R A B (.cv x)) (synCfdcode R A B D)) p0019 p0023
  have p0034 :=
    @gElfdcode2g y A B D (synCfdrow R A B (.cv x)) R dv_cache_0001 dv_cache_0021
      dv_cache_0004 dv_cache_0015 dv_cache_0022 dv_cache_0007 dv_cache_0017 dv_cache_0023
      dv_cache_0024 dv_cache_0019 dv_cache_0020
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (synCfdrow R A B (.cv x)) (synCvv))
      (synWb (.classMem (synCfdrow R A B (.cv x)) (synCfdcode R A B D))
        (synWrex y D (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))))
      p0016 p0034
  have p0036 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (synCfdrow R A B (.cv x)) (synCfdcode R A B D))
      (synWrex y D (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      p0024 p0035
  have p0037 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
              (synWa (.classMem C A) (.classMem D A)))
            (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))
  have p0038 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv y) D)
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
              (synWa (.classMem C A) (.classMem D A)))
            (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classMem (.cv y) D) p0037 p0038
  have p0041 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv y) D)
  have p0042 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
              (synWa (.classMem C A) (.classMem D A)))
            (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      p0037 p0041
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWbr R (synCwe) A) p0042 p0014
  have p0057 :=
    @gSimpr (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem C A) (.classMem D A))
  have p0058 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (synWa (.classMem C A) (.classMem D A)) p0009 p0057
  have p0059 := @gSimpl (.classMem C A) (.classMem D A)
  have p0060 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (.classMem C A) (.classMem D A)) (.classMem C A) p0058 p0059
  have p0064 := @gSimpr (synWbr R (synCwe) A) (synWss A (synCpw B))
  have p0065 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) (synWss A (synCpw B))
      p0011 p0064
  have p0066 :=
    @gSseld
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      A (synCpw B) C p0065
  have p0067 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem C A) (.classMem C (synCpw B)) p0060 p0066
  have p0073 := @gElex C A
  have p0074 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem C A) (.classMem C (synCvv)) p0060 p0073
  have p0075 := @gElpwg C B (synCvv)
  have p0076 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem C (synCvv)) (synWb (.classMem C (synCpw B)) (synWss C B)) p0074 p0075
  have p0077 :=
    @gMpbid
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem C (synCpw B)) (synWss C B) p0067 p0076
  have p0078 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWss C B) p0008 p0077
  have p0079 :=
    @gSseld
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      C B (.cv x) p0078
  have p0080 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv x) C) (.classMem (.cv x) B) p0000 p0079
  have p0081 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv x) B) p0042 p0080
  have p0092 := @gSimpr (.classMem C A) (.classMem D A)
  have p0093 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (.classMem C A) (.classMem D A)) (.classMem D A) p0058 p0092
  have p0099 :=
    @gSseld
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      A (synCpw B) D p0065
  have p0100 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem D A) (.classMem D (synCpw B)) p0093 p0099
  have p0106 := @gElex D A
  have p0107 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem D A) (.classMem D (synCvv)) p0093 p0106
  have p0108 := @gElpwg D B (synCvv)
  have p0109 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem D (synCvv)) (synWb (.classMem D (synCpw B)) (synWss D B)) p0107 p0108
  have p0110 :=
    @gMpbid
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem D (synCpw B)) (synWss D B) p0100 p0109
  have p0111 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWss D B) p0008 p0110
  have p0112 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWss D B) p0042 p0111
  have p0113 :=
    @gSseld
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      D B (.cv y) p0112
  have p0114 :=
    @gMpd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (.classMem (.cv y) D) (.classMem (.cv y) B) p0039 p0113
  have p0115 :=
    @gN3jca
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWbr R (synCwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B) p0050 p0081
      p0114
  have p0116 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
              (synWa (.classMem C A) (.classMem D A)))
            (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))
  have p0117 :=
    @gJca
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synW3a (synWbr R (synCwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))) p0115 p0116
  have p0122 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      p0042 p0008
  have p0128 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem D A) p0122 p0093
  have p0129 :=
    @gJca
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synW3a (synWbr R (synCwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (.classMem D A) p0117 p0128
  have p0130 :=
    @gFdroweqmem x y A B D R dv_cache_0001 dv_cache_0021 dv_cache_0004 dv_cache_0025
      dv_cache_0015 dv_cache_0022 dv_cache_0007 dv_cache_0026 dv_cache_0017 dv_cache_0023
      dv_cache_0027 dv_cache_0024 dv_cache_0028 dv_cache_0020 dv_cache_0029
  have p0131 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (synWa (synWa
          (synW3a (synWbr R (synCwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))) (.classMem D A))
      (synWb (.classMem (.cv x) D) (.classMem (.cv y) D)) p0129 p0130
  have p0132 :=
    @gMpbird
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
                (synWa (.classMem C A) (.classMem D A)))
              (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (.classMem (.cv x) D) (.classMem (.cv y) D) p0039 p0131
  have p0133 :=
    @gEx
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
              (synWa (.classMem C A) (.classMem D A)))
            (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))
      (.classMem (.cv x) D) p0132
  have p0134 :=
    @gRexlimdva
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y)))
      (.classMem (.cv x) D) y D dv_cache_0030 dv_cache_0031 p0133
  have p0135 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classMem (.cv x) C))
      (synWrex y D (.classEq (synCfdrow R A B (.cv x)) (synCfdrow R A B (.cv y))))
      (.classMem (.cv x) D) p0036 p0134
  have p0136 :=
    @gEx
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem (.cv x) C) (.classMem (.cv x) D) p0135
  have p0137 :=
    @gSsrdv
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      x C D dv_cache_0032 dv_cache_0027 dv_cache_0033 p0136
  exact p0137


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdcodeinj2`. -/
@[expose]
noncomputable def gFdcodeinj2 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_fdcodeinj2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcodeinj2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcodeinj2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
            (synWa (.classMem C A) (.classMem D A)))
          (.classEq (synCfdcode R A B C) (synCfdcode R A B D))) (.classEq C D)) :=
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
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
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
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0010 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0011 : Disjoint (D).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (D).fv (C).fv from
        (show Disjoint (D).fv (C).fv from (by exact dv_C_D.symm)))
  have p0000 :=
    @gFdcodesub2 A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      hyp_fdcodeinj2_1 hyp_fdcodeinj2_2 hyp_fdcodeinj2_3
  have p0001 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (.classEq (synCfdcode R A B C) (synCfdcode R A B D))
  have p0002 :=
    @gSimpl (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem C A) (.classMem D A))
  have p0003 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B))) p0001 p0002
  have p0005 :=
    @gSimpr (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem C A) (.classMem D A))
  have p0006 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (synWa (.classMem C A) (.classMem D A)) p0001 p0005
  have p0007 := @gSimpr (.classMem C A) (.classMem D A)
  have p0008 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (.classMem C A) (.classMem D A)) (.classMem D A) p0006 p0007
  have p0012 := @gSimpl (.classMem C A) (.classMem D A)
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (.classMem C A) (.classMem D A)) (.classMem C A) p0006 p0012
  have p0014 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (.classMem D A) (.classMem C A) p0008 p0013
  have p0015 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
      (synWa (.classMem D A) (.classMem C A)) p0003 p0014
  have p0016 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem C A) (.classMem D A)))
      (.classEq (synCfdcode R A B C) (synCfdcode R A B D))
  have p0017 :=
    @gEqcomd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synCfdcode R A B C) (synCfdcode R A B D) p0016
  have p0018 :=
    @gJca
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
        (synWa (.classMem D A) (.classMem C A)))
      (.classEq (synCfdcode R A B D) (synCfdcode R A B C)) p0015 p0017
  have p0019 :=
    @gFdcodesub2 A B D C R dv_cache_0001 dv_cache_0003 dv_cache_0002 dv_cache_0004
      dv_cache_0006 dv_cache_0005 dv_cache_0007 dv_cache_0011 dv_cache_0010 dv_cache_0009
      hyp_fdcodeinj2_1 hyp_fdcodeinj2_2 hyp_fdcodeinj2_3
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem D A) (.classMem C A)))
        (.classEq (synCfdcode R A B D) (synCfdcode R A B C)))
      (synWss D C) p0018 p0019
  have p0021 :=
    @gEqssd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (synWss A (synCpw B)))
          (synWa (.classMem C A) (.classMem D A)))
        (.classEq (synCfdcode R A B C) (synCfdcode R A B D)))
      C D p0000 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_wppimagefn`. -/
@[expose]
noncomputable def gWppimagefn (R : Class)
    (hyp_wppimagefn_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (synWfn (synCimage R) (synCvv)) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((synCima R (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCimage R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCimage R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gVex x
  have p0001 := @gImaex R (.cv x) hyp_wppimagefn_1 p0000
  have p0002 := @gEueq y (synCima R (.cv x)) dv_cache_0001
  have p0003 :=
    @gMpbi (.classMem (synCima R (.cv x)) (synCvv))
      (synWeu y (.classEq (.cv y) (synCima R (.cv x)))) p0001 p0002
  have p0005 := @gVex y
  have p0006 := @gBrimage (.cv x) (.cv y) R p0000 p0005
  have p0007 :=
    @gEubii (synWbr (.cv x) (synCimage R) (.cv y))
      (.classEq (.cv y) (synCima R (.cv x))) y p0006
  have p0008 :=
    @gMpbir (synWeu y (synWbr (.cv x) (synCimage R) (.cv y)))
      (synWeu y (.classEq (.cv y) (synCima R (.cv x)))) p0003 p0007
  have p0009 :=
    @gRgenw (synWeu y (synWbr (.cv x) (synCimage R) (.cv y))) x (synCvv) p0008
  have p0010 :=
    @gFnres x y (synCvv) (synCimage R) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0011 :=
    @gMpbir (synWfn (synCres (synCimage R) (synCvv)) (synCvv))
      (synWral x (synCvv) (synWeu y (synWbr (.cv x) (synCimage R) (.cv y)))) p0009
      p0010
  have p0012 := @gResid (synCimage R)
  have p0013 :=
    @gFneq1i (synCvv) (synCres (synCimage R) (synCvv)) (synCimage R) p0012
  have p0014 :=
    @gMpbi (synWfn (synCres (synCimage R) (synCvv)) (synCvv))
      (synWfn (synCimage R) (synCvv)) p0011 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_wppfvimage`. -/
@[expose]
noncomputable def gWppfvimage (A : Class) (R : Class) (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_wppfvimage_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_wppfvimage_2 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCimage R) A) (synCima R A)) :=
  by
  have p0000 := @gEqid (synCima R A)
  have p0001 := @gImaex R A hyp_wppfvimage_1 hyp_wppfvimage_2
  have p0002 := @gBrimage A (synCima R A) R hyp_wppfvimage_2 p0001
  have p0003 :=
    @gMpbir (synWbr A (synCimage R) (synCima R A))
      (.classEq (synCima R A) (synCima R A)) p0000 p0002
  have p0004 := @gTru
  have p0005 := @gWppimagefn R hyp_wppfvimage_1
  have p0006 := @gA1i (synWfn (synCimage R) (synCvv)) synWtru p0005
  have p0007 := @gA1i (.classMem A (synCvv)) synWtru hyp_wppfvimage_2
  have p0008 :=
    @gJca synWtru (synWfn (synCimage R) (synCvv)) (.classMem A (synCvv)) p0006 p0007
  have p0009 := Nominal.mp p0004 p0008
  have p0010 := @gFnbrfvb (synCvv) A (synCima R A) (synCimage R)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gMpbir (.classEq (synCfv (synCimage R) A) (synCima R A))
      (synWbr A (synCimage R) (synCima R A)) p0003 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_fdpointrelex`. -/
@[expose]
noncomputable def gFdpointrelex (A : Class)
    (hyp_fdpointrelex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCfdpointrel A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdpointrel A))
  have p0001 := @gFdmemex
  have p0002 := @gKqrelex (synCfdmem) p0001
  have p0003 := @gVvex
  have p0004 := @gUniex A hyp_fdpointrelex_1
  have p0005 := @gPw1ex (synCuni A) p0004
  have p0006 := @gPw1ex (synCpw1 (synCuni A)) p0005
  have p0007 := @gXpex (synCvv) (synCpw1 (synCpw1 (synCuni A))) p0003 p0006
  have p0008 :=
    @gInex (synCkqrel (synCfdmem))
      (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A)))) p0002 p0007
  have p0009 :=
    @gEqeltri (synCfdpointrel A)
      (synCin (synCkqrel (synCfdmem)) (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A)))))
      (synCvv) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_fdglobalrowex`. -/
@[expose]
noncomputable def gFdglobalrowex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdglobalrowex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdglobalrowex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdglobalrowex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdglobalrowmap R A B) (synCvv)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
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
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_u_ne_d : u ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_u : d ≠ u := Ne.symm fresh_u_ne_d
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
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
  have dv_cache_0004 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint (A).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (A).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show u ∉ (A).fv from (by exact fresh_u_not_A))))))
  have dv_cache_0008 : Disjoint (A).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (A).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0009 : Disjoint (B).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (B).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show u ∉ (B).fv from (by exact fresh_u_not_B))))))
  have dv_cache_0010 : Disjoint (B).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (B).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0011 : Disjoint ((Class.cv u)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint ((Class.cv u)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (u),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)];
          exact
            (show Disjoint (({ u } : Finset Var)) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ ({ d } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show u ≠ d from (by exact fresh_u_ne_d))))))))
  have dv_cache_0012 : Disjoint ((Class.cv u)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint ((Class.cv u)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ u } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show u ∉ (R).fv from (by exact fresh_u_not_R))))))
  have dv_cache_0013 : Disjoint ((Class.cv d)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint ((Class.cv d)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ d } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0014 : u ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0015 : u ∉ ((synCfdrowrel R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel,
          Finset.mem_union, fresh_u_not_A, fresh_u_not_B, fresh_u_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0016 : d ∉ ((synCfdrowrel R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0017 : d ∉ ((synCfdrowfib R A B (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_u, fresh_d_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0018 : u ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show u ≠ d from (by exact fresh_u_ne_d))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdglobalrowmap u A B
      R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @gIftrue (synWbr R (synCwe) A)
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synC0)
  have p0002 := @gVex d
  have p0003 :=
    @gElfdrowfibg A B (.cv u) (.cv d) R dv_cache_0001 dv_cache_0007 dv_cache_0008
      dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0004 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gBicomi (.classMem (.cv d) (synCfdrowfib R A B (.cv u)))
      (.classMem (synCop (synCsn (.cv d)) (.cv u)) (synCfdrowrel R A B)) p0004
  have p0006 :=
    @gReleqmpt u d (synCpw1 (synCpw1 (synCuni A))) (synCfdrowrel R A B)
      (synCfdrowfib R A B (.cv u)) dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 p0005
  have p0007 :=
    @gA1i
      (.classEq (synCin (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv)) (synCcnv
            (synCcompl (synCima
                (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
                (synC1c)))))
        (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))))
      (synWbr R (synCwe) A) p0006
  have p0008 := @gUniex A hyp_fdglobalrowex_2
  have p0009 := @gPw1ex (synCuni A) p0008
  have p0010 := @gPw1ex (synCpw1 (synCuni A)) p0009
  have p0011 :=
    @gA1i (.classMem (synCpw1 (synCpw1 (synCuni A))) (synCvv))
      (synWbr R (synCwe) A) p0010
  have p0012 := @gVvex
  have p0013 := @gA1i (.classMem (synCvv) (synCvv)) (synWbr R (synCwe) A) p0012
  have p0014 :=
    @gJca (synWbr R (synCwe) A)
      (.classMem (synCpw1 (synCpw1 (synCuni A))) (synCvv))
      (.classMem (synCvv) (synCvv)) p0011 p0013
  have p0015 := @gXpexg (synCpw1 (synCpw1 (synCuni A))) (synCvv) (synCvv) (synCvv)
  have p0016 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCpw1 (synCpw1 (synCuni A))) (synCvv))
        (.classMem (synCvv) (synCvv)))
      (.classMem (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv)) (synCvv)) p0014
      p0015
  have p0017 := @gSsetex
  have p0018 := @gIns3ex (synCsset) p0017
  have p0019 :=
    @gA1i (.classMem (synCins3 (synCsset)) (synCvv)) (synWbr R (synCwe) A) p0018
  have p0020 :=
    @gFdrowrelex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0004 hyp_fdglobalrowex_1
      hyp_fdglobalrowex_2 hyp_fdglobalrowex_3
  have p0021 := @gIns2exg (synCfdrowrel R A B) (synCvv)
  have p0022 :=
    @gSyl (synWbr R (synCwe) A) (.classMem (synCfdrowrel R A B) (synCvv))
      (.classMem (synCins2 (synCfdrowrel R A B)) (synCvv)) p0020 p0021
  have p0023 :=
    @gJca (synWbr R (synCwe) A) (.classMem (synCins3 (synCsset)) (synCvv))
      (.classMem (synCins2 (synCfdrowrel R A B)) (synCvv)) p0019 p0022
  have p0024 :=
    @gSymdifexg (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)) (synCvv)
      (synCvv)
  have p0025 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCins3 (synCsset)) (synCvv))
        (.classMem (synCins2 (synCfdrowrel R A B)) (synCvv)))
      (.classMem (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
        (synCvv))
      p0023 p0024
  have p0026 := @gN1cex
  have p0027 := @gA1i (.classMem (synC1c) (synCvv)) (synWbr R (synCwe) A) p0026
  have p0028 :=
    @gJca (synWbr R (synCwe) A)
      (.classMem (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
        (synCvv))
      (.classMem (synC1c) (synCvv)) p0025 p0027
  have p0029 :=
    @gImaexg (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
      (synC1c) (synCvv) (synCvv)
  have p0030 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synCvv)) (.classMem (synC1c) (synCvv)))
      (.classMem
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synC1c)) (synCvv))
      p0028 p0029
  have p0031 :=
    @gComplexg
      (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
        (synC1c))
      (synCvv)
  have p0032 :=
    @gSyl (synWbr R (synCwe) A)
      (.classMem
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synC1c)) (synCvv))
      (.classMem (synCcompl (synCima
            (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B))) (synC1c)))
        (synCvv))
      p0030 p0031
  have p0033 :=
    @gCnvexg
      (synCcompl
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
          (synC1c)))
      (synCvv)
  have p0034 :=
    @gSyl (synWbr R (synCwe) A)
      (.classMem (synCcompl (synCima
            (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B))) (synC1c)))
        (synCvv))
      (.classMem (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
              (synC1c)))) (synCvv))
      p0032 p0033
  have p0035 :=
    @gJca (synWbr R (synCwe) A)
      (.classMem (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv)) (synCvv))
      (.classMem (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
              (synC1c)))) (synCvv))
      p0016 p0034
  have p0036 :=
    @gInexg (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv))
      (synCcnv (synCcompl (synCima
            (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B))) (synC1c))))
      (synCvv) (synCvv)
  have p0037 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv)) (synCvv))
        (.classMem (synCcnv (synCcompl (synCima
                (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
                (synC1c)))) (synCvv)))
      (.classMem (synCin (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv)) (synCcnv
            (synCcompl (synCima
                (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
                (synC1c))))) (synCvv))
      p0035 p0036
  have p0038 :=
    @gEqeltrrd (synWbr R (synCwe) A)
      (synCin (synCxp (synCpw1 (synCpw1 (synCuni A))) (synCvv)) (synCcnv (synCcompl
            (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdrowrel R A B)))
              (synC1c)))))
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synCvv) p0007 p0037
  have p0039 :=
    @gEqeltrd (synWbr R (synCwe) A)
      (synCif (synWbr R (synCwe) A)
        (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))) (synC0))
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synCvv) p0001 p0038
  have p0040 :=
    @gIffalse (synWbr R (synCwe) A)
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synC0)
  have p0041 := @gN0ex
  have p0042 := @gA1i (.classMem (synC0) (synCvv)) (.neg (synWbr R (synCwe) A)) p0041
  have p0043 :=
    @gEqeltrd (.neg (synWbr R (synCwe) A))
      (synCif (synWbr R (synCwe) A)
        (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))) (synC0))
      (synC0) (synCvv) p0040 p0042
  have p0044 :=
    @gPm261i (synWbr R (synCwe) A)
      (.classMem (synCif (synWbr R (synCwe) A)
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synC0)) (synCvv))
      p0039 p0043
  have p0045 :=
    @gEqeltri (synCfdglobalrowmap R A B)
      (synCif (synWbr R (synCwe) A)
        (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))) (synC0))
      (synCvv) p0000 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_fdglobalrowval`. -/
@[expose]
noncomputable def gFdglobalrowval (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_u : u ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (.classEq (synCfdglobalrowmap R A B)
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_u, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_u, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdglobalrowmap u A B
      R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @gA1i
      (.classEq (synCfdglobalrowmap R A B) (synCif (synWbr R (synCwe) A)
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synC0)))
      (synWbr R (synCwe) A) p0000
  have p0002 :=
    @gIftrue (synWbr R (synCwe) A)
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synC0)
  have p0003 :=
    @gEqtrd (synWbr R (synCwe) A) (synCfdglobalrowmap R A B)
      (synCif (synWbr R (synCwe) A)
        (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))) (synC0))
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))) p0001
      p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdpointimage`. -/
@[expose]
noncomputable def gFdpointimage (A : Class) (c : Var) (_dv_A_c : c ∉ A.fv)
    (_hyp_fdpointimage_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv c) A)
        (.classEq (synCima (synCfdpointrel A) (synCsn (synCsn (.cv c))))
          (synCpw1 (synCpw1 (.cv c))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ c } : Finset Var)
  let d : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_ne_c : d ≠ c := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_c : y ≠ c := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_c : x ≠ c := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : Disjoint ((synCfdmem)).fv ((synCsn (.cv c))).fv := by
    exact
      (show Disjoint ((synCfdmem)).fv ((synCsn (.cv c))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact (show Disjoint ((∅ : Finset Var)) (((Class.cv c)).fv) from (by simp))))
  have dv_cache_0002 : Disjoint ((synCfdmem)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((synCfdmem)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact (show Disjoint ((∅ : Finset Var)) (({ d } : Finset Var)) from (by simp))))
  have dv_cache_0003 : Disjoint ((synCsn (.cv c))).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((synCsn (.cv c))).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((Class.cv c)).fv) (({ d } : Finset Var)) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ c } : Finset Var)) (({ d } : Finset Var)) from
                    (Finset.disjoint_singleton_left.mpr
                      (show c ∉ ({ d } : Finset Var) from
                        (by
                          simpa only [Finset.mem_singleton] using
                            (show c ≠ d from (by exact fresh_c_ne_d))))))))))
  have dv_cache_0004 : x ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_d, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0006 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_c, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq (.cv d) (synCsn (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_d, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉ ((synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_d,
          fresh_x_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    x ∉ ((Wff.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_d, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Wff.classEq (.cv d) (synCsn (synCsn (.cv y))))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_d, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0015 :
    y ∉
      ((synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
          (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_ne_c, fresh_y_ne_d, fresh_y_not_A, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Wff.classMem (.cv c) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_c, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_d, not_false_eq_true])
  have dv_cache_0018 :
    d ∉ ((synCima (synCfdpointrel A) (synCsn (synCsn (.cv c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_not_A, fresh_d_ne_c, or_false, not_false_eq_true])
  have dv_cache_0019 : d ∉ ((synCpw1 (synCpw1 (.cv c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_d_ne_c,
          not_false_eq_true])
  have dv_cache_0020 : d ∉ ((Wff.classMem (.cv c) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_c, fresh_d_not_A, or_false, not_false_eq_true])
  have p0000 := @gElimasn (synCfdpointrel A) (synCsn (.cv c)) (.cv d)
  have p0001 := (Nominal.classEqRefl (synCfdpointrel A))
  have p0002 :=
    @gEleq2i (synCfdpointrel A)
      (synCin (synCkqrel (synCfdmem)) (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A)))))
      (synCop (synCsn (.cv c)) (.cv d)) p0001
  have p0003 :=
    @gBitri
      (.classMem (.cv d) (synCima (synCfdpointrel A) (synCsn (synCsn (.cv c)))))
      (.classMem (synCop (synCsn (.cv c)) (.cv d)) (synCfdpointrel A))
      (.classMem (synCop (synCsn (.cv c)) (.cv d)) (synCin (synCkqrel (synCfdmem))
          (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A))))))
      p0000 p0002
  have p0004 :=
    @gElin (synCop (synCsn (.cv c)) (.cv d)) (synCkqrel (synCfdmem))
      (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A))))
  have p0005 := @gSnex (.cv c)
  have p0006 := @gVex d
  have p0007 :=
    @gKqrelbr (synCfdmem) (synCsn (.cv c)) (.cv d) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0005 p0006
  have p0009 :=
    @gOpelxp (synCsn (.cv c)) (.cv d) (synCvv) (synCpw1 (synCpw1 (synCuni A)))
  have p0010 :=
    @gMpbiran
      (.classMem (synCop (synCsn (.cv c)) (.cv d))
        (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A)))))
      (.classMem (synCsn (.cv c)) (synCvv))
      (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))) p0005 p0009
  have p0011 :=
    @gAnbi12i (.classMem (synCop (synCsn (.cv c)) (.cv d)) (synCkqrel (synCfdmem)))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classMem (synCop (synCsn (.cv c)) (.cv d))
        (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A)))))
      (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))) p0007 p0010
  have p0012 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv c)) (.cv d)) (synCin (synCkqrel (synCfdmem))
          (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A))))))
      (synWa (.classMem (synCop (synCsn (.cv c)) (.cv d)) (synCkqrel (synCfdmem)))
        (.classMem (synCop (synCsn (.cv c)) (.cv d))
          (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A))))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))))
      p0004 p0011
  have p0013 :=
    @gBitri
      (.classMem (.cv d) (synCima (synCfdpointrel A) (synCsn (synCsn (.cv c)))))
      (.classMem (synCop (synCsn (.cv c)) (.cv d)) (synCin (synCkqrel (synCfdmem))
          (synCxp (synCvv) (synCpw1 (synCpw1 (synCuni A))))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))))
      p0003 p0012
  have p0014 :=
    @gA1i
      (synWb (.classMem (.cv d) (synCima (synCfdpointrel A) (synCsn (synCsn (.cv c)))))
        (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
          (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A))))))
      (.classMem (.cv c) A) p0013
  have p0015 := @gElpw12 x (.cv d) (synCuni A) dv_cache_0004 dv_cache_0005
  have p0016 :=
    @gA1i
      (synWb (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A))))
        (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
      (.classMem (.cv c) A) p0015
  have p0017 :=
    @gAnbi2d (.classMem (.cv c) A) (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A))))
      (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem)) p0016
  have p0018 :=
    @gSimpl (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classEq (.cv d) (synCsn (synCsn (.cv x))))
  have p0019 :=
    @gSimpr (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classEq (.cv d) (synCsn (synCsn (.cv x))))
  have p0020 := @gId (.classEq (.cv d) (synCsn (synCsn (.cv x))))
  have p0021 :=
    @gOpkeq2d (.classEq (.cv d) (synCsn (synCsn (.cv x)))) (.cv d)
      (synCsn (synCsn (.cv x))) (synCsn (.cv c)) p0020
  have p0022 :=
    @gEleq1d (.classEq (.cv d) (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (.cv c)) (.cv d))
      (synCopk (synCsn (.cv c)) (synCsn (synCsn (.cv x)))) (synCfdmem) p0021
  have p0023 := @gVex x
  have p0024 := @gFdmemval (.cv x) c dv_cache_0006 p0023
  have p0025 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv c)) (synCsn (synCsn (.cv x)))) (synCfdmem))
        (.classMem (.cv x) (.cv c)))
      (.classEq (.cv d) (synCsn (synCsn (.cv x)))) p0024
  have p0026 :=
    @gBitrd (.classEq (.cv d) (synCsn (synCsn (.cv x))))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv c)) (synCsn (synCsn (.cv x)))) (synCfdmem))
      (.classMem (.cv x) (.cv c)) p0022 p0025
  have p0027 :=
    @gSyl
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (.classEq (.cv d) (synCsn (synCsn (.cv x))))
      (synWb (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classMem (.cv x) (.cv c)))
      p0019 p0026
  have p0028 :=
    @gMpbid
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classMem (.cv x) (.cv c)) p0018 p0027
  have p0030 :=
    @gJca
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (.classMem (.cv x) (.cv c)) (.classEq (.cv d) (synCsn (synCsn (.cv x)))) p0028
      p0019
  have p0031 := @gId (.classEq (.cv y) (.cv x))
  have p0032 := @gSneqd (.classEq (.cv y) (.cv x)) (.cv y) (.cv x) p0031
  have p0033 :=
    @gSneqd (.classEq (.cv y) (.cv x)) (synCsn (.cv y)) (synCsn (.cv x)) p0032
  have p0034 :=
    @gEqeq2d (.classEq (.cv y) (.cv x)) (synCsn (synCsn (.cv y)))
      (synCsn (synCsn (.cv x))) (.cv d) p0033
  have p0035 :=
    @gRspcev (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (.classEq (.cv d) (synCsn (synCsn (.cv x)))) y (.cv x) (.cv c) dv_cache_0007
      dv_cache_0008 dv_cache_0009 p0034
  have p0036 :=
    @gSyl
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (synWa (.classMem (.cv x) (.cv c)) (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) p0030 p0035
  have p0037 :=
    @gEx (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classEq (.cv d) (synCsn (synCsn (.cv x))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) p0036
  have p0038 :=
    @gA1d (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.imp (.classEq (.cv d) (synCsn (synCsn (.cv x))))
        (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classMem (.cv x) (synCuni A)) p0037
  have p0039 :=
    @gRexlimdv (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classEq (.cv d) (synCsn (synCsn (.cv x))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) x (synCuni A)
      dv_cache_0010 dv_cache_0011 p0038
  have p0040 :=
    @gImp (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x)))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) p0039
  have p0041 :=
    @gA1i
      (.imp (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
          (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
        (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classMem (.cv c) A) p0040
  have p0042 :=
    @gSimprl (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))
      (.classEq (.cv d) (synCsn (synCsn (.cv y))))
  have p0043 :=
    @gSimprr (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))
      (.classEq (.cv d) (synCsn (synCsn (.cv y))))
  have p0044 := @gId (.classEq (.cv d) (synCsn (synCsn (.cv y))))
  have p0045 :=
    @gOpkeq2d (.classEq (.cv d) (synCsn (synCsn (.cv y)))) (.cv d)
      (synCsn (synCsn (.cv y))) (synCsn (.cv c)) p0044
  have p0046 :=
    @gEleq1d (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (synCopk (synCsn (.cv c)) (.cv d))
      (synCopk (synCsn (.cv c)) (synCsn (synCsn (.cv y)))) (synCfdmem) p0045
  have p0047 := @gVex y
  have p0048 := @gFdmemval (.cv y) c dv_cache_0012 p0047
  have p0049 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv c)) (synCsn (synCsn (.cv y)))) (synCfdmem))
        (.classMem (.cv y) (.cv c)))
      (.classEq (.cv d) (synCsn (synCsn (.cv y)))) p0048
  have p0050 :=
    @gBitrd (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv c)) (synCsn (synCsn (.cv y)))) (synCfdmem))
      (.classMem (.cv y) (.cv c)) p0046 p0049
  have p0051 :=
    @gBiimprd (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (.classMem (.cv y) (.cv c)) p0050
  have p0052 :=
    @gSyl
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (.imp (.classMem (.cv y) (.cv c))
        (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem)))
      p0043 p0051
  have p0053 :=
    @gMpd
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classMem (.cv y) (.cv c))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem)) p0042 p0052
  have p0054 :=
    @gSimpl (.classMem (.cv c) A)
      (synWa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (synCsn (synCsn (.cv y)))))
  have p0056 :=
    @gJca
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) p0054 p0042
  have p0057 := @gElssuni (.cv c) A
  have p0058 := @gSselda (.classMem (.cv c) A) (.cv c) (synCuni A) (.cv y) p0057
  have p0059 :=
    @gSyl
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (synWa (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)))
      (.classMem (.cv y) (synCuni A)) p0056 p0058
  have p0061 :=
    @gJca
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classMem (.cv y) (synCuni A)) (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      p0059 p0043
  have p0062 := @gId (.classEq (.cv x) (.cv y))
  have p0063 := @gSneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0062
  have p0064 :=
    @gSneqd (.classEq (.cv x) (.cv y)) (synCsn (.cv x)) (synCsn (.cv y)) p0063
  have p0065 :=
    @gEqeq2d (.classEq (.cv x) (.cv y)) (synCsn (synCsn (.cv x)))
      (synCsn (synCsn (.cv y))) (.cv d) p0064
  have p0066 :=
    @gRspcev (.classEq (.cv d) (synCsn (synCsn (.cv x))))
      (.classEq (.cv d) (synCsn (synCsn (.cv y)))) x (.cv y) (synCuni A) dv_cache_0013
      dv_cache_0005 dv_cache_0014 p0065
  have p0067 :=
    @gSyl
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (synWa (.classMem (.cv y) (synCuni A)) (.classEq (.cv d) (synCsn (synCsn (.cv y)))))
      (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))) p0061 p0066
  have p0068 :=
    @gJca
      (synWa (.classMem (.cv c) A) (synWa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (synCsn (synCsn (.cv y))))))
      (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
      (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))) p0053 p0067
  have p0069 :=
    @gEx (.classMem (.cv c) A)
      (synWa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (synCsn (synCsn (.cv y)))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
      p0068
  have p0070 :=
    @gExp3a (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))
      (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
      p0069
  have p0071 :=
    @gRexlimdv (.classMem (.cv c) A) (.classEq (.cv d) (synCsn (synCsn (.cv y))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
      y (.cv c) dv_cache_0015 dv_cache_0016 p0070
  have p0072 :=
    @gImpbid (.classMem (.cv c) A)
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) p0041 p0071
  have p0073 :=
    @gBitrd (.classMem (.cv c) A)
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (synWrex x (synCuni A) (.classEq (.cv d) (synCsn (synCsn (.cv x))))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) p0017 p0072
  have p0074 := @gElpw12 y (.cv d) (.cv c) dv_cache_0017 dv_cache_0008
  have p0075 :=
    @gBicomi (.classMem (.cv d) (synCpw1 (synCpw1 (.cv c))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y))))) p0074
  have p0076 :=
    @gA1i
      (synWb (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y)))))
        (.classMem (.cv d) (synCpw1 (synCpw1 (.cv c)))))
      (.classMem (.cv c) A) p0075
  have p0077 :=
    @gBitrd (.classMem (.cv c) A)
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))))
      (synWrex y (.cv c) (.classEq (.cv d) (synCsn (synCsn (.cv y)))))
      (.classMem (.cv d) (synCpw1 (synCpw1 (.cv c)))) p0073 p0076
  have p0078 :=
    @gBitrd (.classMem (.cv c) A)
      (.classMem (.cv d) (synCima (synCfdpointrel A) (synCsn (synCsn (.cv c)))))
      (synWa (.classMem (synCopk (synCsn (.cv c)) (.cv d)) (synCfdmem))
        (.classMem (.cv d) (synCpw1 (synCpw1 (synCuni A)))))
      (.classMem (.cv d) (synCpw1 (synCpw1 (.cv c)))) p0014 p0077
  have p0079 :=
    @gEqrdv (.classMem (.cv c) A) d
      (synCima (synCfdpointrel A) (synCsn (synCsn (.cv c))))
      (synCpw1 (synCpw1 (.cv c))) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0078
  exact p0079

/-- Checked nominal proof certificate identified upstream as `g_fdglobalrowima`. -/
@[expose]
noncomputable def gFdglobalrowima (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (.classMem C A))
        (.classEq (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 C)))
          (synCfdcode R A B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
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
  have dv_cache_0004 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((synCpw1 (synCpw1 (synCuni A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0008 : u ∉ ((synCpw1 (synCpw1 C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_u_not_C,
          not_false_eq_true])
  have dv_cache_0009 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0010 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0011 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0012 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have p0000 := @gSimpl (synWbr R (synCwe) A) (.classMem C A)
  have p0001 :=
    @gFdglobalrowval u A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0002 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem C A)) (synWbr R (synCwe) A)
      (.classEq (synCfdglobalrowmap R A B)
        (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u))))
      p0000 p0001
  have p0003 :=
    @gImaeq1d (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synCfdglobalrowmap R A B)
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synCpw1 (synCpw1 C)) p0002
  have p0004 :=
    @gDfima3
      (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
      (synCpw1 (synCpw1 C))
  have p0005 :=
    @gA1i
      (.classEq (synCima
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synCpw1 (synCpw1 C))) (synCrn (synCres
            (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
            (synCpw1 (synCpw1 C)))))
      (synWa (synWbr R (synCwe) A) (.classMem C A)) p0004
  have p0006 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 C)))
      (synCima (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
        (synCpw1 (synCpw1 C)))
      (synCrn (synCres
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synCpw1 (synCpw1 C))))
      p0003 p0005
  have p0007 := @gSimpr (synWbr R (synCwe) A) (.classMem C A)
  have p0008 := @gElssuni C A
  have p0009 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem C A)) (.classMem C A)
      (synWss C (synCuni A)) p0007 p0008
  have p0010 := @gPw1ss C (synCuni A)
  have p0011 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem C A)) (synWss C (synCuni A))
      (synWss (synCpw1 C) (synCpw1 (synCuni A))) p0009 p0010
  have p0012 := @gPw1ss (synCpw1 C) (synCpw1 (synCuni A))
  have p0013 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synWss (synCpw1 C) (synCpw1 (synCuni A)))
      (synWss (synCpw1 (synCpw1 C)) (synCpw1 (synCpw1 (synCuni A)))) p0011 p0012
  have p0014 :=
    @gResmpt u (synCpw1 (synCpw1 (synCuni A))) (synCpw1 (synCpw1 C))
      (synCfdrowfib R A B (.cv u)) dv_cache_0007 dv_cache_0008
  have p0015 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synWss (synCpw1 (synCpw1 C)) (synCpw1 (synCpw1 (synCuni A))))
      (.classEq (synCres
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synCpw1 (synCpw1 C)))
        (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))))
      p0013 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdcodemap2 u A B C R
      dv_cache_0001 dv_cache_0009 dv_cache_0002 dv_cache_0003 dv_cache_0010 dv_cache_0004
      dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0006
  have p0017 :=
    @gEqcomi (synCfdcodemap2 R A B C)
      (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u))) p0016
  have p0018 :=
    @gA1i
      (.classEq (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u)))
        (synCfdcodemap2 R A B C))
      (synWa (synWbr R (synCwe) A) (.classMem C A)) p0017
  have p0019 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synCres (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
        (synCpw1 (synCpw1 C)))
      (synCmpt u (synCpw1 (synCpw1 C)) (synCfdrowfib R A B (.cv u)))
      (synCfdcodemap2 R A B C) p0015 p0018
  have p0020 :=
    @gRneqd (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synCres (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
        (synCpw1 (synCpw1 C)))
      (synCfdcodemap2 R A B C) p0019
  have p0021 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 C)))
      (synCrn (synCres
          (synCmpt u (synCpw1 (synCpw1 (synCuni A))) (synCfdrowfib R A B (.cv u)))
          (synCpw1 (synCpw1 C))))
      (synCrn (synCfdcodemap2 R A B C)) p0006 p0020
  have p0022 :=
    @gFdcodeeqrnmap2 A B C R dv_cache_0001 dv_cache_0009 dv_cache_0002 dv_cache_0010
      dv_cache_0004 dv_cache_0011
  have p0023 := @gEqcomi (synCfdcode R A B C) (synCrn (synCfdcodemap2 R A B C)) p0022
  have p0024 :=
    @gA1i (.classEq (synCrn (synCfdcodemap2 R A B C)) (synCfdcode R A B C))
      (synWa (synWbr R (synCwe) A) (.classMem C A)) p0023
  have p0025 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (.classMem C A))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 C)))
      (synCrn (synCfdcodemap2 R A B C)) (synCfdcode R A B C) p0021 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodemapex`. -/
@[expose]
noncomputable def gFdcolcodemapex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodemapex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodemapex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (.classMem (synCfdcolcodemap R A B) (synCvv))) :=
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
  have p0000 := (Nominal.classEqRefl (synCfdcolcodemap R A B))
  have p0001 :=
    @gFdglobalrowex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapex_1
      hyp_fdcolcodemapex_2 hyp_fdcolcodemapex_3
  have p0002 := @gImageex (synCfdglobalrowmap R A B) p0001
  have p0003 := @gFdpointrelex A hyp_fdcolcodemapex_2
  have p0004 := @gImageex (synCfdpointrel A) p0003
  have p0005 :=
    @gCoex (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A))
      p0002 p0004
  have p0006 := @gPw1ex A hyp_fdcolcodemapex_2
  have p0007 := @gPw1ex (synCpw1 A) p0006
  have p0008 :=
    @gResex
      (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
      (synCpw1 (synCpw1 A)) p0005 p0007
  have p0009 :=
    @gEqeltri (synCfdcolcodemap R A B)
      (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
      (synCvv) p0000 p0008
  have p0010 :=
    @gA1i (.classMem (synCfdcolcodemap R A B) (synCvv)) (synWbr R (synCwe) A) p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodemapfn`. -/
@[expose]
noncomputable def gFdcolcodemapfn (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapfn_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodemapfn_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodemapfn_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A)
        (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
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
  have dv_cache_0004 : x ∉ ((synCrn (synCimage (synCfdpointrel A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have p0000 :=
    @gFdglobalrowex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapfn_1
      hyp_fdcolcodemapfn_2 hyp_fdcolcodemapfn_3
  have p0001 := @gWppimagefn (synCfdglobalrowmap R A B) p0000
  have p0002 := @gFdpointrelex A hyp_fdcolcodemapfn_2
  have p0003 := @gWppimagefn (synCfdpointrel A) p0002
  have p0004 := @gElex (.cv x) (synCrn (synCimage (synCfdpointrel A)))
  have p0005 :=
    @gSsriv x (synCrn (synCimage (synCfdpointrel A))) (synCvv) dv_cache_0004
      dv_cache_0005 p0004
  have p0006 :=
    @gFnco (synCvv) (synCvv) (synCimage (synCfdglobalrowmap R A B))
      (synCimage (synCfdpointrel A))
  have p0007 :=
    @gMp3an (synWfn (synCimage (synCfdglobalrowmap R A B)) (synCvv))
      (synWfn (synCimage (synCfdpointrel A)) (synCvv))
      (synWss (synCrn (synCimage (synCfdpointrel A))) (synCvv))
      (synWfn (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCvv))
      p0001 p0003 p0005 p0006
  have p0008 :=
    @gFnresin1 (synCvv) (synCpw1 (synCpw1 A))
      (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gElex (.cv x) (synCpw1 (synCpw1 A))
  have p0011 :=
    @gSsriv x (synCpw1 (synCpw1 A)) (synCvv) dv_cache_0006 dv_cache_0005 p0010
  have p0012 := @gSseqin2 (synCpw1 (synCpw1 A)) (synCvv)
  have p0013 :=
    @gMpbi (synWss (synCpw1 (synCpw1 A)) (synCvv))
      (.classEq (synCin (synCvv) (synCpw1 (synCpw1 A))) (synCpw1 (synCpw1 A))) p0011
      p0012
  have p0014 :=
    @gReseq2i (synCin (synCvv) (synCpw1 (synCpw1 A))) (synCpw1 (synCpw1 A))
      (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
      p0013
  have p0015 :=
    @gFneq1i (synCin (synCvv) (synCpw1 (synCpw1 A)))
      (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCin (synCvv) (synCpw1 (synCpw1 A))))
      (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
      p0014
  have p0016 :=
    @gMpbi
      (synWfn (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (synCin (synCvv) (synCpw1 (synCpw1 A))))
        (synCin (synCvv) (synCpw1 (synCpw1 A))))
      (synWfn (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
        (synCin (synCvv) (synCpw1 (synCpw1 A))))
      p0009 p0015
  have p0021 :=
    @gFneq2i (synCin (synCvv) (synCpw1 (synCpw1 A))) (synCpw1 (synCpw1 A))
      (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
      p0013
  have p0022 :=
    @gMpbi
      (synWfn (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
        (synCin (synCvv) (synCpw1 (synCpw1 A))))
      (synWfn (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A))) (synCpw1 (synCpw1 A)))
      p0016 p0021
  have p0023 := (Nominal.classEqRefl (synCfdcolcodemap R A B))
  have p0024 :=
    @gFneq1i (synCpw1 (synCpw1 A)) (synCfdcolcodemap R A B)
      (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
      p0023
  have p0025 :=
    @gMpbir (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))
      (synWfn (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A))) (synCpw1 (synCpw1 A)))
      p0022 p0024
  have p0026 :=
    @gA1i (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))
      (synWbr R (synCwe) A) p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodemapval`. -/
@[expose]
noncomputable def gFdcolcodemapval (A : Class) (B : Class) (R : Class) (q : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_q : q ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_q : q ∉ B.fv) (dv_R_q : q ∉ R.fv)
    (hyp_fdcolcodemapval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodemapval_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodemapval_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfdcode R A B (synCuni (synCuni (.cv q)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ ({ q } : Finset Var)
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : x ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_q, not_false_eq_true])
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
  have dv_cache_0003 : Disjoint ((Class.cv q)).fv ((synCfdpointrel A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((Class.cv q)).fv ((synCfdpointrel A)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel];
          exact
            (show Disjoint (({ q } : Finset Var)) ((A).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show q ∉ (A).fv from (by exact dv_A_q))))))
  have dv_cache_0004 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0005 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 :
    Disjoint ((synCpw1 (synCpw1 (.cv x)))).fv ((synCfdglobalrowmap R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((synCpw1 (synCpw1 (.cv x)))).fv ((synCfdglobalrowmap R A B)).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdglobalrowmap];
          exact
            (show Disjoint (((synCpw1 (.cv x))).fv) (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(Finset.disjoint_union_right.mpr
                    ⟨(show Disjoint (((synCpw1 (.cv x))).fv) ((A).fv) from
                        (by
                          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                          exact
                            (show Disjoint (((Class.cv x)).fv) ((A).fv) from
                              (by
                                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                exact
                                  (show Disjoint (({ x } : Finset Var)) ((A).fv) from
                                    (Finset.disjoint_singleton_left.mpr
                                      (show x ∉ (A).fv from
                                        (by exact fresh_x_not_A)))))))),
                      (show Disjoint (((synCpw1 (.cv x))).fv) ((B).fv) from
                        (by
                          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                          exact
                            (show Disjoint (((Class.cv x)).fv) ((B).fv) from
                              (by
                                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                exact
                                  (show Disjoint (({ x } : Finset Var)) ((B).fv) from
                                    (Finset.disjoint_singleton_left.mpr
                                      (show x ∉ (B).fv from
                                        (by exact fresh_x_not_B))))))))⟩),
                  (show Disjoint (((synCpw1 (.cv x))).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                      exact
                        (show Disjoint (((Class.cv x)).fv) ((R).fv) from
                          (by
                            rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                            exact
                              (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                                (Finset.disjoint_singleton_left.mpr
                                  (show x ∉ (R).fv from
                                    (by exact fresh_x_not_R))))))))⟩))))
  have dv_cache_0008 : Disjoint (A).fv ((synCuni (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
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
                            (show q ∉ (A).fv from (by exact dv_A_q))))))))))
  have dv_cache_0009 : Disjoint (B).fv ((synCuni (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
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
                            (show q ∉ (B).fv from (by exact dv_B_q))))))))))
  have dv_cache_0010 : Disjoint ((synCuni (synCuni (.cv q)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
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
                            (show q ∉ (R).fv from (by exact dv_R_q))))))))))
  have dv_cache_0011 :
    x ∉
      ((Wff.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCfdcode R A B (synCuni (synCuni (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A, fresh_x_not_B, fresh_x_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, fresh_x_ne_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))
  have p0001 := @gElpw12 x (.cv q) A dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gA1i
      (synWb (.classMem (.cv q) (synCpw1 (synCpw1 A)))
        (synWrex x A (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))) p0001
  have p0003 :=
    @gMpbid (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (synWrex x A (.classEq (.cv q) (synCsn (synCsn (.cv x))))) p0000 p0002
  have p0004 :=
    @gSimpl (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
  have p0005 := (Nominal.classEqRefl (synCfdcolcodemap R A B))
  have p0006 :=
    @gFveq1i (.cv q) (synCfdcolcodemap R A B)
      (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A)))
      p0005
  have p0007 :=
    @gA1i
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q)) (synCfv (synCres
            (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
            (synCpw1 (synCpw1 A))) (.cv q)))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))) p0006
  have p0009 :=
    @gFvres (.cv q) (synCpw1 (synCpw1 A))
      (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
  have p0010 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (.classEq (synCfv (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
              (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A))) (.cv q)) (synCfv
          (synCcom (synCimage (synCfdglobalrowmap R A B)) (synCimage (synCfdpointrel A)))
          (.cv q)))
      p0000 p0009
  have p0011 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCfv (synCres (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (synCpw1 (synCpw1 A))) (.cv q))
      (synCfv (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (.cv q))
      p0007 p0010
  have p0012 := @gVex q
  have p0013 := @gFdpointrelex A hyp_fdcolcodemapval_2
  have p0014 := @gWppimagefn (synCfdpointrel A) p0013
  have p0015 :=
    @gFvco2 (synCvv) (.cv q) (synCimage (synCfdglobalrowmap R A B))
      (synCimage (synCfdpointrel A))
  have p0016 :=
    @gMpan (synWfn (synCimage (synCfdpointrel A)) (synCvv))
      (.classMem (.cv q) (synCvv))
      (.classEq (synCfv (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (.cv q))
        (synCfv (synCimage (synCfdglobalrowmap R A B))
          (synCfv (synCimage (synCfdpointrel A)) (.cv q))))
      p0014 p0015
  have p0017 := Nominal.mp p0012 p0016
  have p0018 :=
    @gA1i
      (.classEq (synCfv (synCcom (synCimage (synCfdglobalrowmap R A B))
            (synCimage (synCfdpointrel A))) (.cv q))
        (synCfv (synCimage (synCfdglobalrowmap R A B))
          (synCfv (synCimage (synCfdpointrel A)) (.cv q))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))) p0017
  have p0019 :=
    @gEqtrd (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCfv (synCcom (synCimage (synCfdglobalrowmap R A B))
          (synCimage (synCfdpointrel A))) (.cv q))
      (synCfv (synCimage (synCfdglobalrowmap R A B))
        (synCfv (synCimage (synCfdpointrel A)) (.cv q)))
      p0011 p0018
  have p0020 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfv (synCimage (synCfdglobalrowmap R A B))
          (synCfv (synCimage (synCfdpointrel A)) (.cv q))))
      p0004 p0019
  have p0023 := @gWppfvimage (.cv q) (synCfdpointrel A) dv_cache_0003 p0013 p0012
  have p0024 :=
    @gA1i
      (.classEq (synCfv (synCimage (synCfdpointrel A)) (.cv q))
        (synCima (synCfdpointrel A) (.cv q)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      p0023
  have p0025 :=
    @gSimprr (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))
  have p0026 :=
    @gImaeq2d
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.cv q) (synCsn (synCsn (.cv x))) (synCfdpointrel A) p0025
  have p0027 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCimage (synCfdpointrel A)) (.cv q))
      (synCima (synCfdpointrel A) (.cv q))
      (synCima (synCfdpointrel A) (synCsn (synCsn (.cv x)))) p0024 p0026
  have p0028 :=
    @gSimprl (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))
  have p0029 := @gFdpointimage A x dv_cache_0002 hyp_fdcolcodemapval_2
  have p0030 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.classMem (.cv x) A)
      (.classEq (synCima (synCfdpointrel A) (synCsn (synCsn (.cv x))))
        (synCpw1 (synCpw1 (.cv x))))
      p0028 p0029
  have p0031 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCimage (synCfdpointrel A)) (.cv q))
      (synCima (synCfdpointrel A) (synCsn (synCsn (.cv x))))
      (synCpw1 (synCpw1 (.cv x))) p0027 p0030
  have p0032 :=
    @gFveq2d
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCimage (synCfdpointrel A)) (.cv q)) (synCpw1 (synCpw1 (.cv x)))
      (synCimage (synCfdglobalrowmap R A B)) p0031
  have p0033 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCfv (synCimage (synCfdglobalrowmap R A B))
        (synCfv (synCimage (synCfdpointrel A)) (.cv q)))
      (synCfv (synCimage (synCfdglobalrowmap R A B)) (synCpw1 (synCpw1 (.cv x))))
      p0020 p0032
  have p0034 :=
    @gFdglobalrowex A B R dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdcolcodemapval_1
      hyp_fdcolcodemapval_2 hyp_fdcolcodemapval_3
  have p0035 := @gVex x
  have p0036 := @gPw1ex (.cv x) p0035
  have p0037 := @gPw1ex (synCpw1 (.cv x)) p0036
  have p0038 :=
    @gWppfvimage (synCpw1 (synCpw1 (.cv x))) (synCfdglobalrowmap R A B) dv_cache_0007
      p0034 p0037
  have p0039 :=
    @gA1i
      (.classEq (synCfv (synCimage (synCfdglobalrowmap R A B)) (synCpw1 (synCpw1 (.cv x))))
        (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 (.cv x)))))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      p0038
  have p0040 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCfv (synCimage (synCfdglobalrowmap R A B)) (synCpw1 (synCpw1 (.cv x))))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 (.cv x)))) p0033 p0039
  have p0042 :=
    @gUnieqd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.cv q) (synCsn (synCsn (.cv x))) p0025
  have p0043 := @gSnex (.cv x)
  have p0044 := @gUnisn (synCsn (.cv x)) p0043
  have p0045 :=
    @gA1i (.classEq (synCuni (synCsn (synCsn (.cv x)))) (synCsn (.cv x)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      p0044
  have p0046 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCuni (.cv q)) (synCuni (synCsn (synCsn (.cv x)))) (synCsn (.cv x)) p0042
      p0045
  have p0047 :=
    @gUnieqd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCuni (.cv q)) (synCsn (.cv x)) p0046
  have p0049 := @gUnisn (.cv x) p0035
  have p0050 :=
    @gA1i (.classEq (synCuni (synCsn (.cv x))) (.cv x))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      p0049
  have p0051 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCuni (synCuni (.cv q))) (synCuni (synCsn (.cv x))) (.cv x) p0047 p0050
  have p0052 :=
    @gEqcomd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCuni (synCuni (.cv q))) (.cv x) p0051
  have p0053 := @gPw1eq (.cv x) (synCuni (synCuni (.cv q)))
  have p0054 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.classEq (.cv x) (synCuni (synCuni (.cv q))))
      (.classEq (synCpw1 (.cv x)) (synCpw1 (synCuni (synCuni (.cv q))))) p0052 p0053
  have p0055 := @gPw1eq (synCpw1 (.cv x)) (synCpw1 (synCuni (synCuni (.cv q))))
  have p0056 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.classEq (synCpw1 (.cv x)) (synCpw1 (synCuni (synCuni (.cv q)))))
      (.classEq (synCpw1 (synCpw1 (.cv x)))
        (synCpw1 (synCpw1 (synCuni (synCuni (.cv q))))))
      p0054 p0055
  have p0057 :=
    @gImaeq2d
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCpw1 (synCpw1 (.cv x))) (synCpw1 (synCpw1 (synCuni (synCuni (.cv q)))))
      (synCfdglobalrowmap R A B) p0056
  have p0058 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 (.cv x))))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 (synCuni (synCuni (.cv q))))))
      p0040 p0057
  have p0060 :=
    @gSimpl (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))
  have p0061 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synWbr R (synCwe) A) p0004 p0060
  have p0075 :=
    @gEleq1d
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.cv x) (synCuni (synCuni (.cv q))) A p0052
  have p0076 :=
    @gMpbid
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (.classMem (.cv x) A) (.classMem (synCuni (synCuni (.cv q))) A) p0028 p0075
  have p0077 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synWbr R (synCwe) A) (.classMem (synCuni (synCuni (.cv q))) A) p0061 p0076
  have p0078 :=
    @gFdglobalrowima A B (synCuni (synCuni (.cv q))) R dv_cache_0004 dv_cache_0008
      dv_cache_0005 dv_cache_0009 dv_cache_0006 dv_cache_0010
  have p0079 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synWa (synWbr R (synCwe) A) (.classMem (synCuni (synCuni (.cv q))) A))
      (.classEq (synCima (synCfdglobalrowmap R A B)
          (synCpw1 (synCpw1 (synCuni (synCuni (.cv q))))))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      p0077 p0078
  have p0080 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
        (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCima (synCfdglobalrowmap R A B) (synCpw1 (synCpw1 (synCuni (synCuni (.cv q))))))
      (synCfdcode R A B (synCuni (synCuni (.cv q)))) p0058 p0079
  have p0081 :=
    @gEx (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      p0080
  have p0082 :=
    @gExp3a (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classMem (.cv x) A) (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      p0081
  have p0083 :=
    @gRexlimdv
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      x A dv_cache_0011 dv_cache_0012 p0082
  have p0084 :=
    @gMpd (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synWrex x A (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classEq (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCfdcode R A B (synCuni (synCuni (.cv q)))))
      p0003 p0083
  exact p0084

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodemapf`. -/
@[expose]
noncomputable def gFdcolcodemapf (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapf_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdcolcodemapf_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdcolcodemapf_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
          (synCpw (synCpw (synCfdif R A B))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
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
  have dv_cache_0005 : q ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_B, not_false_eq_true])
  have dv_cache_0006 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint (A).fv ((synCuni (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
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
  have dv_cache_0008 : Disjoint (B).fv ((synCuni (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
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
  have dv_cache_0009 : Disjoint ((synCuni (synCuni (.cv q)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
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
  have dv_cache_0010 : q ∉ ((synWbr R (synCwe) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : q ∉ ((synCpw1 (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0012 : q ∉ ((synCpw (synCpw (synCfdif R A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((synCfdcolcodemap R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcolcodemap,
          Finset.mem_union, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, or_false,
          not_false_eq_true])
  have p0000 :=
    @gFdcolcodemapfn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf_1
      hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3
  have p0002 :=
    @gFdcolcodemapval A B R q dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003
      dv_cache_0005 dv_cache_0006 hyp_fdcolcodemapf_1 hyp_fdcolcodemapf_2
      hyp_fdcolcodemapf_3
  have p0003 :=
    @gSimpl (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))
  have p0004 := @gVex q
  have p0005 := @gUniex (.cv q) p0004
  have p0006 := @gUniex (synCuni (.cv q)) p0005
  have p0007 :=
    @gFdcodeelpwpw2 A B (synCuni (synCuni (.cv q))) R dv_cache_0001 dv_cache_0007
      dv_cache_0002 dv_cache_0008 dv_cache_0003 dv_cache_0009 hyp_fdcolcodemapf_1
      hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3 p0006
  have p0008 :=
    @gSyl (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synWbr R (synCwe) A)
      (.classMem (synCfdcode R A B (synCuni (synCuni (.cv q))))
        (synCpw (synCpw (synCfdif R A B))))
      p0003 p0007
  have p0009 :=
    @gEqeltrd
      (synWa (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A))))
      (synCfv (synCfdcolcodemap R A B) (.cv q))
      (synCfdcode R A B (synCuni (synCuni (.cv q))))
      (synCpw (synCpw (synCfdif R A B))) p0002 p0008
  have p0010 :=
    @gEx (synWbr R (synCwe) A) (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (.classMem (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCpw (synCpw (synCfdif R A B))))
      p0009
  have p0011 :=
    @gRalrimiv (synWbr R (synCwe) A)
      (.classMem (synCfv (synCfdcolcodemap R A B) (.cv q))
        (synCpw (synCpw (synCfdif R A B))))
      q (synCpw1 (synCpw1 A)) dv_cache_0010 p0010
  have p0012 :=
    @gJca (synWbr R (synCwe) A)
      (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))
      (synWral q (synCpw1 (synCpw1 A)) (.classMem (synCfv (synCfdcolcodemap R A B) (.cv q))
          (synCpw (synCpw (synCfdif R A B)))))
      p0000 p0011
  have p0013 :=
    @gFnfvrnss q (synCpw1 (synCpw1 A)) (synCpw (synCpw (synCfdif R A B)))
      (synCfdcolcodemap R A B) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0014 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))
        (synWral q (synCpw1 (synCpw1 A))
          (.classMem (synCfv (synCfdcolcodemap R A B) (.cv q))
            (synCpw (synCpw (synCfdif R A B))))))
      (synWss (synCrn (synCfdcolcodemap R A B)) (synCpw (synCpw (synCfdif R A B))))
      p0012 p0013
  have p0015 :=
    @gJca (synWbr R (synCwe) A)
      (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))
      (synWss (synCrn (synCfdcolcodemap R A B)) (synCpw (synCpw (synCfdif R A B))))
      p0000 p0014
  have p0016 :=
    (Nominal.biimpRefl (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B)))))
  have p0017 :=
    @gSylibr (synWbr R (synCwe) A)
      (synWa (synWfn (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A)))
        (synWss (synCrn (synCfdcolcodemap R A B)) (synCpw (synCpw (synCfdif R A B)))))
      (synWf (synCfdcolcodemap R A B) (synCpw1 (synCpw1 A))
        (synCpw (synCpw (synCfdif R A B))))
      p0015 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_fdcolcodearg`. -/
@[expose]
noncomputable def gFdcolcodearg (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 A)))
        (synWa (.classMem (synCuni (synCuni (.cv q))) A)
          (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ q } : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_ne_q : c ≠ q := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : c ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_q, not_false_eq_true])
  have dv_cache_0002 : c ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0003 :
    c ∉
      ((synWa (.classMem (synCuni (synCuni (.cv q))) A)
          (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_q, fresh_c_not_A, or_false, not_false_eq_true])
  have p0000 := @gElpw12 c (.cv q) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (synWrex c A (.classEq (.cv q) (synCsn (synCsn (.cv c))))) p0000
  have p0002 :=
    @gSimpr (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c))))
  have p0003 :=
    @gUnieqd
      (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (.cv q) (synCsn (synCsn (.cv c))) p0002
  have p0004 := @gSnex (.cv c)
  have p0005 := @gUnisn (synCsn (.cv c)) p0004
  have p0006 :=
    @gA1i (.classEq (synCuni (synCsn (synCsn (.cv c)))) (synCsn (.cv c)))
      (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c))))) p0005
  have p0007 :=
    @gEqtrd (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCuni (.cv q)) (synCuni (synCsn (synCsn (.cv c)))) (synCsn (.cv c)) p0003
      p0006
  have p0008 :=
    @gUnieqd
      (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCuni (.cv q)) (synCsn (.cv c)) p0007
  have p0009 := @gVex c
  have p0010 := @gUnisn (.cv c) p0009
  have p0011 :=
    @gA1i (.classEq (synCuni (synCsn (.cv c))) (.cv c))
      (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c))))) p0010
  have p0012 :=
    @gEqtrd (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCuni (synCuni (.cv q))) (synCuni (synCsn (.cv c))) (.cv c) p0008 p0011
  have p0013 :=
    @gSimpl (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c))))
  have p0014 :=
    @gEqeltrd
      (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCuni (synCuni (.cv q))) (.cv c) A p0012 p0013
  have p0027 :=
    @gSneqd (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCuni (synCuni (.cv q))) (.cv c) p0012
  have p0028 :=
    @gSneqd (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCsn (.cv c)) p0027
  have p0029 :=
    @gEqcomd
      (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) (synCsn (synCsn (.cv c))) p0028
  have p0030 :=
    @gEqtrd (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (.cv q) (synCsn (synCsn (.cv c)))
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) p0002 p0029
  have p0031 :=
    @gJca (synWa (.classMem (.cv c) A) (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (.classMem (synCuni (synCuni (.cv q))) A)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0014 p0030
  have p0032 :=
    @gRexlimiva (.classEq (.cv q) (synCsn (synCsn (.cv c))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) A)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      c A dv_cache_0003 p0031
  have p0033 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 A)))
      (synWrex c A (.classEq (.cv q) (synCsn (synCsn (.cv c)))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) A)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      p0001 p0032
  exact p0033


end NFChoice.DirectNominalPrf.WPPReplay

end
