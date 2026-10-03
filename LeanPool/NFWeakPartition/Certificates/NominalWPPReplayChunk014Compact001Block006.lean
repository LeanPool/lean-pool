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

@[expose]
noncomputable def g_fdcodemap2ex (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdcodemap2ex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcodemap2ex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcodemap2ex_3 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_fdcodemap2ex_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcodemap2 R A B C) (syn_cvv))) :=
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
  have dv_cache_0018 : u ∉ ((syn_cpw1 (syn_cpw1 C))).fv :=
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
  have dv_cache_0019 : u ∉ ((syn_cfdrowrel R A B)).fv :=
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
  have dv_cache_0020 : d ∉ ((syn_cfdrowrel R A B)).fv :=
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
  have dv_cache_0021 : d ∉ ((syn_cfdrowfib R A B (.cv u))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcodemap2 u A B C R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfdcodemap2 R A B C)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))))
      (syn_wbr R (syn_cwe) A) p0000
  have p0002 := @g_vex d
  have p0003 :=
    @g_elfdrowfibg A B (.cv u) (.cv d) R dv_cache_0001 dv_cache_0011 dv_cache_0012
      dv_cache_0003 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0016
      dv_cache_0017
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_bicomi (.classMem (.cv d) (syn_cfdrowfib R A B (.cv u)))
      (.classMem (syn_cop (syn_csn (.cv d)) (.cv u)) (syn_cfdrowrel R A B)) p0004
  have p0006 :=
    @g_releqmpt u d (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowrel R A B)
      (syn_cfdrowfib R A B (.cv u)) dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0005
  have p0007 :=
    @g_a1i
      (.classEq (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
                (syn_c1c)))))
        (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))))
      (syn_wbr R (syn_cwe) A) p0006
  have p0008 := @g_pw1ex C hyp_fdcodemap2ex_4
  have p0009 := @g_pw1ex (syn_cpw1 C) p0008
  have p0010 :=
    @g_a1i (.classMem (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0009
  have p0011 := @g_vvex
  have p0012 := @g_a1i (.classMem (syn_cvv) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0011
  have p0013 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cpw1 (syn_cpw1 C)) (syn_cvv))
      (.classMem (syn_cvv) (syn_cvv)) p0010 p0012
  have p0014 := @g_xpexg (syn_cpw1 (syn_cpw1 C)) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)))
      (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_cvv)) p0013 p0014
  have p0016 := @g_ssetex
  have p0017 := @g_ins3ex (syn_csset) p0016
  have p0018 :=
    @g_a1i (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0017
  have p0019 :=
    @g_fdrowrelex2 A B R dv_cache_0001 dv_cache_0003 dv_cache_0006 hyp_fdcodemap2ex_1
      hyp_fdcodemap2ex_2 hyp_fdcodemap2ex_3
  have p0020 := @g_ins2exg (syn_cfdrowrel R A B) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrowrel R A B) (syn_cvv))
      (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cins3 (syn_csset)) (syn_cvv))
      (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0018 p0021
  have p0023 :=
    @g_symdifexg (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)
      (syn_cvv)
  have p0024 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cins3 (syn_csset)) (syn_cvv))
        (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)))
      (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
        (syn_cvv))
      p0022 p0023
  have p0025 := @g_n_1cex
  have p0026 := @g_a1i (.classMem (syn_c1c) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0025
  have p0027 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
        (syn_cvv))
      (.classMem (syn_c1c) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_imaexg (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
      (syn_c1c) (syn_cvv) (syn_cvv)
  have p0029 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)))
      (.classMem
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_c1c)) (syn_cvv))
      p0027 p0028
  have p0030 :=
    @g_complexg
      (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
        (syn_c1c))
      (syn_cvv)
  have p0031 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (.classMem
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_c1c)) (syn_cvv))
      (.classMem (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))
        (syn_cvv))
      p0029 p0030
  have p0032 :=
    @g_cnvexg
      (syn_ccompl
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_c1c)))
      (syn_cvv)
  have p0033 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (.classMem (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))
        (syn_cvv))
      (.classMem (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
              (syn_c1c)))) (syn_cvv))
      p0031 p0032
  have p0034 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_cvv))
      (.classMem (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
              (syn_c1c)))) (syn_cvv))
      p0015 p0033
  have p0035 :=
    @g_inexg (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv))
      (syn_ccnv (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))
      (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_cvv)) (.classMem
          (syn_ccnv (syn_ccompl (syn_cima
                (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
                (syn_c1c)))) (syn_cvv)))
      (.classMem (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
                (syn_c1c))))) (syn_cvv))
      p0034 p0035
  have p0037 :=
    @g_eqeltrrd (syn_wbr R (syn_cwe) A)
      (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 C)) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
              (syn_c1c)))))
      (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) (syn_cvv) p0007
      p0036
  have p0038 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdcodemap2 R A B C)
      (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) (syn_cvv) p0001
      p0037
  exact p0038

@[expose]
noncomputable def g_fdcodeeqrnmap2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.classEq (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C))) :=
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
  have dv_cache_0020 : q ∉ ((syn_cpw1 (syn_cpw1 C))).fv :=
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
  have dv_cache_0021 : q ∉ ((syn_cfdrowfib R A B (.cv u))).fv :=
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
  have dv_cache_0024 : x ∉ ((Wff.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))).fv :=
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
  have dv_cache_0027 : Disjoint (A).fv ((syn_csn (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (show Disjoint (A).fv ((syn_csn (syn_csn (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint ((A).fv) (((syn_csn (.cv x))).fv) from
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
  have dv_cache_0029 : Disjoint (B).fv ((syn_csn (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (show Disjoint (B).fv ((syn_csn (syn_csn (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint ((B).fv) (((syn_csn (.cv x))).fv) from
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
  have dv_cache_0030 : Disjoint ((Class.cv u)).fv ((syn_csn (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (show Disjoint ((Class.cv u)).fv ((syn_csn (syn_csn (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (({ u } : Finset Var)) (((syn_csn (.cv x))).fv) from
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
  have dv_cache_0032 : Disjoint ((syn_csn (syn_csn (.cv x)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (show Disjoint ((syn_csn (syn_csn (.cv x)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (((syn_csn (.cv x))).fv) ((R).fv) from
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
  have dv_cache_0033 : u ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
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
    u ∉ ((Wff.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcode x A B C R q
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcodemap2 u A B C R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0016 dv_cache_0006 dv_cache_0007
      dv_cache_0017 dv_cache_0010 dv_cache_0018 dv_cache_0019
  have p0002 :=
    @g_rnmpt u q (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))
      (syn_cfdcodemap2 R A B C) dv_cache_0020 dv_cache_0021 dv_cache_0022 p0001
  have p0003 :=
    (Nominal.biimpRefl (syn_wrex u (syn_cpw1 (syn_cpw1 C))
        (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
  have p0004 := @g_elpw12 x (.cv u) C dv_cache_0023 dv_cache_0012
  have p0005 :=
    @g_anbi1i (.classMem (.cv u) (syn_cpw1 (syn_cpw1 C)))
      (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))))
      (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))) p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv u) (syn_cpw1 (syn_cpw1 C)))
        (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))))
        (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      u p0005
  have p0007 :=
    @g_bitri
      (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wex u (syn_wa (.classMem (.cv u) (syn_cpw1 (syn_cpw1 C)))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      (syn_wex u (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      p0003 p0006
  have p0008 :=
    @g_r19_41v (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
      (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))) x C dv_cache_0024
  have p0009 :=
    @g_bicomi
      (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))))
        (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      p0008
  have p0010 :=
    @g_exbii
      (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))))
        (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      u p0009
  have p0011 :=
    @g_bitri
      (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wex u (syn_wa (syn_wrex x C (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      (syn_wex u (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
      p0007 p0010
  have p0012 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      x u C dv_cache_0018 dv_cache_0025
  have p0013 :=
    @g_bicomi
      (syn_wrex x C (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
      (syn_wex u (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
      p0012
  have p0014 :=
    @g_bitri
      (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wex u (syn_wrex x C (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
      (syn_wrex x C (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
      p0011 p0013
  have p0015 := @g_snex (syn_csn (.cv x))
  have p0016 :=
    @g_fdrowfibeq4 A B (.cv u) (syn_csn (syn_csn (.cv x))) R dv_cache_0001 dv_cache_0026
      dv_cache_0027 dv_cache_0003 dv_cache_0028 dv_cache_0029 dv_cache_0007 dv_cache_0030
      dv_cache_0031 dv_cache_0032
  have p0017 :=
    @g_eqeq2d (.classEq (.cv u) (syn_csn (syn_csn (.cv x)))) (syn_cfdrowfib R A B (.cv u))
      (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))) (.cv q) p0016
  have p0018 :=
    @g_ceqsexv (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))
      (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))) u
      (syn_csn (syn_csn (.cv x))) dv_cache_0033 dv_cache_0034 p0015 p0017
  have p0019 :=
    @g_rexbii
      (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))) x C p0018
  have p0020 :=
    @g_bitri
      (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wrex x C (syn_wex u (syn_wa (.classEq (.cv u) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))))
      p0014 p0019
  have p0021 := @g_vex x
  have p0022 :=
    @g_fdrowfibsn2 A B (.cv x) R dv_cache_0001 dv_cache_0035 dv_cache_0003 dv_cache_0036
      dv_cache_0007 dv_cache_0037 p0021
  have p0023 :=
    @g_eqeq2i (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))) (syn_cfdrow R A B (.cv x))
      (.cv q) p0022
  have p0024 :=
    @g_rexbii (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x)))))
      (.classEq (.cv q) (syn_cfdrow R A B (.cv x))) x C p0023
  have p0025 :=
    @g_bitri
      (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrowfib R A B (syn_csn (syn_csn (.cv x))))))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))) p0020 p0024
  have p0026 :=
    @g_abbii
      (syn_wrex u (syn_cpw1 (syn_cpw1 C)) (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u))))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))) q p0025
  have p0027 :=
    @g_eqtri (syn_crn (syn_cfdcodemap2 R A B C))
      (.cab q (syn_wrex u (syn_cpw1 (syn_cpw1 C))
          (.classEq (.cv q) (syn_cfdrowfib R A B (.cv u)))))
      (.cab q (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x))))) p0002 p0026
  have p0028 :=
    @g_eqtr4i (syn_cfdcode R A B C)
      (.cab q (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))))
      (syn_crn (syn_cfdcodemap2 R A B C)) p0000 p0027
  exact p0028

@[expose]
noncomputable def g_fdcodeex2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdcodeex2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcodeex2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcodeex2_3 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_fdcodeex2_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B C) (syn_cvv))) :=
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
    @g_fdcodeeqrnmap2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_a1i (.classEq (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C)))
      (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_fdcodemap2ex A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdcodeex2_1 hyp_fdcodeex2_2 hyp_fdcodeex2_3
      hyp_fdcodeex2_4
  have p0003 := @g_rnexg (syn_cfdcodemap2 R A B C) (syn_cvv)
  have p0004 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcodemap2 R A B C) (syn_cvv))
      (.classMem (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdcode R A B C)
      (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cvv) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_fdcodeelpwpw2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdcodeelpwpw2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcodeelpwpw2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcodeelpwpw2_3 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_fdcodeelpwpw2_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A)
        (.classMem (syn_cfdcode R A B C) (syn_cpw (syn_cpw (syn_cfdif R A B))))) :=
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
    @g_fdcodesspw2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_a1i (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B)))
      (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_fdcodeex2 A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdcodeelpwpw2_1 hyp_fdcodeelpwpw2_2
      hyp_fdcodeelpwpw2_3 hyp_fdcodeelpwpw2_4
  have p0003 := @g_elpwg (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B)) (syn_cvv)
  have p0004 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcode R A B C) (syn_cvv))
      (syn_wb (.classMem (syn_cfdcode R A B C) (syn_cpw (syn_cpw (syn_cfdif R A B))))
        (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B))))
      p0002 p0003
  have p0005 :=
    @g_mpbird (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cfdcode R A B C) (syn_cpw (syn_cpw (syn_cfdif R A B))))
      (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B))) p0001 p0004
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

@[expose]
noncomputable def g_fdroweq4 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq C D) (.classEq (syn_cfdrow R A B C) (syn_cfdrow R A B D))) :=
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
  have p0000 := @g_id (.classEq C D)
  have p0001 := @g_eleq1d (.classEq C D) C D (.cv d) p0000
  have p0002 :=
    @g_rabbidv (.classEq C D) (.classMem C (.cv d)) (.classMem D (.cv d)) d
      (syn_cfdif R A B) dv_cache_0001 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrow A B C R d
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrow A B D R d
      dv_cache_0002 dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0013 dv_cache_0007
      dv_cache_0008 dv_cache_0014 dv_cache_0015 dv_cache_0011
  have p0005 :=
    @g_n_3eqtr4g (.classEq C D) (syn_crab d (syn_cfdif R A B) (.classMem C (.cv d)))
      (syn_crab d (syn_cfdif R A B) (.classMem D (.cv d))) (syn_cfdrow R A B C)
      (syn_cfdrow R A B D) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_elfdcode2g (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv)
    (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cvv)) (syn_wb (.classMem D (syn_cfdcode R A B C))
          (syn_wrex x C (.classEq D (syn_cfdrow R A B (.cv x)))))) :=
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
  have dv_cache_0018 : q ∉ ((Wff.classMem D (syn_cfdcode R A B C))).fv :=
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
  have dv_cache_0019 : q ∉ ((syn_wrex x C (.classEq D (syn_cfdrow R A B (.cv x))))).fv :=
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
  have p0000 := @g_id (.classEq (.cv q) D)
  have p0001 := @g_eleq1d (.classEq (.cv q) D) (.cv q) D (syn_cfdcode R A B C) p0000
  have p0003 := @g_eqeq1d (.classEq (.cv q) D) (.cv q) D (syn_cfdrow R A B (.cv x)) p0000
  have p0004 :=
    @g_rexbidv (.classEq (.cv q) D) (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))
      (.classEq D (syn_cfdrow R A B (.cv x))) x C dv_cache_0001 p0003
  have p0005 := @g_vex q
  have p0006 :=
    @g_elfdcodeg x A B C (.cv q) R dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_vtoclbg (.classMem (.cv q) (syn_cfdcode R A B C))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x))))
      (.classMem D (syn_cfdcode R A B C))
      (syn_wrex x C (.classEq D (syn_cfdrow R A B (.cv x)))) q D (syn_cvv) dv_cache_0017
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

@[expose]
noncomputable def g_fdcodesub2 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_fdcodesub2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcodesub2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcodesub2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (syn_wss C D)) :=
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
    y ∉ ((Wff.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x)))).fv :=
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
  have dv_cache_0019 : y ∉ ((syn_cfdrow R A B (.cv x))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
              (syn_wa (.classMem C A) (.classMem D A)))
            (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))).fv :=
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
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem (.cv x) C)
  have p0001 := @g_eqid (syn_cfdrow R A B (.cv x))
  have p0002 :=
    @g_a1i (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      p0001
  have p0003 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv x) C)
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x))) p0000 p0002
  have p0004 :=
    @g_fdroweq4 A B (.cv y) (.cv x) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0005 :=
    @g_eqeq2d (.classEq (.cv y) (.cv x)) (syn_cfdrow R A B (.cv y))
      (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x)) p0004
  have p0006 :=
    @g_rspcev (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x))) y (.cv x) C
      dv_cache_0011 dv_cache_0012 dv_cache_0013 p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wa (.classMem (.cv x) C)
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv x))))
      (syn_wrex y C (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      p0003 p0006
  have p0008 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem (.cv x) C)
  have p0009 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0010 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem C A) (.classMem D A))
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0009 p0010
  have p0012 := @g_simpl (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wbr R (syn_cwe) A)
      p0011 p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wbr R (syn_cwe) A) p0008 p0013
  have p0015 :=
    @g_fdrowex2 A B (.cv x) R dv_cache_0001 dv_cache_0003 dv_cache_0004 dv_cache_0006
      dv_cache_0007 dv_cache_0010 hyp_fdcodesub2_1 hyp_fdcodesub2_2 hyp_fdcodesub2_3
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_elfdcode2g y A B C (syn_cfdrow R A B (.cv x)) R dv_cache_0001 dv_cache_0014
      dv_cache_0004 dv_cache_0015 dv_cache_0016 dv_cache_0007 dv_cache_0017 dv_cache_0018
      dv_cache_0012 dv_cache_0019 dv_cache_0020
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv))
      (syn_wb (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B C))
        (syn_wrex y C (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))))
      p0016 p0017
  have p0019 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B C))
      (syn_wrex y C (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      p0007 p0018
  have p0021 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)) p0008 p0021
  have p0023 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_cfdcode R A B C) (syn_cfdcode R A B D) (syn_cfdrow R A B (.cv x)) p0022
  have p0024 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B C))
      (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B D)) p0019 p0023
  have p0034 :=
    @g_elfdcode2g y A B D (syn_cfdrow R A B (.cv x)) R dv_cache_0001 dv_cache_0021
      dv_cache_0004 dv_cache_0015 dv_cache_0022 dv_cache_0007 dv_cache_0017 dv_cache_0023
      dv_cache_0024 dv_cache_0019 dv_cache_0020
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (syn_cfdrow R A B (.cv x)) (syn_cvv))
      (syn_wb (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B D))
        (syn_wrex y D (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))))
      p0016 p0034
  have p0036 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (syn_cfdrow R A B (.cv x)) (syn_cfdcode R A B D))
      (syn_wrex y D (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      p0024 p0035
  have p0037 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
              (syn_wa (.classMem C A) (.classMem D A)))
            (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0038 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv y) D)
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
              (syn_wa (.classMem C A) (.classMem D A)))
            (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classMem (.cv y) D) p0037 p0038
  have p0041 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv y) D)
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
              (syn_wa (.classMem C A) (.classMem D A)))
            (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      p0037 p0041
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wbr R (syn_cwe) A) p0042 p0014
  have p0057 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem C A) (.classMem D A))
  have p0058 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (syn_wa (.classMem C A) (.classMem D A)) p0009 p0057
  have p0059 := @g_simpl (.classMem C A) (.classMem D A)
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (.classMem C A) (.classMem D A)) (.classMem C A) p0058 p0059
  have p0064 := @g_simpr (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) (syn_wss A (syn_cpw B))
      p0011 p0064
  have p0066 :=
    @g_sseld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      A (syn_cpw B) C p0065
  have p0067 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem C A) (.classMem C (syn_cpw B)) p0060 p0066
  have p0073 := @g_elex C A
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem C A) (.classMem C (syn_cvv)) p0060 p0073
  have p0075 := @g_elpwg C B (syn_cvv)
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem C (syn_cvv)) (syn_wb (.classMem C (syn_cpw B)) (syn_wss C B)) p0074 p0075
  have p0077 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem C (syn_cpw B)) (syn_wss C B) p0067 p0076
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wss C B) p0008 p0077
  have p0079 :=
    @g_sseld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      C B (.cv x) p0078
  have p0080 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv x) C) (.classMem (.cv x) B) p0000 p0079
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classMem (.cv x) B) p0042 p0080
  have p0092 := @g_simpr (.classMem C A) (.classMem D A)
  have p0093 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (.classMem C A) (.classMem D A)) (.classMem D A) p0058 p0092
  have p0099 :=
    @g_sseld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      A (syn_cpw B) D p0065
  have p0100 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem D A) (.classMem D (syn_cpw B)) p0093 p0099
  have p0106 := @g_elex D A
  have p0107 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem D A) (.classMem D (syn_cvv)) p0093 p0106
  have p0108 := @g_elpwg D B (syn_cvv)
  have p0109 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem D (syn_cvv)) (syn_wb (.classMem D (syn_cpw B)) (syn_wss D B)) p0107 p0108
  have p0110 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem D (syn_cpw B)) (syn_wss D B) p0100 p0109
  have p0111 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wss D B) p0008 p0110
  have p0112 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wss D B) p0042 p0111
  have p0113 :=
    @g_sseld
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      D B (.cv y) p0112
  have p0114 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classMem (.cv y) D) (.classMem (.cv y) B) p0039 p0113
  have p0115 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B) p0050 p0081
      p0114
  have p0116 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
              (syn_wa (.classMem C A) (.classMem D A)))
            (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
  have p0117 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))) p0115 p0116
  have p0122 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      p0042 p0008
  have p0128 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem D A) p0122 p0093
  have p0129 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classMem D A) p0117 p0128
  have p0130 :=
    @g_fdroweqmem x y A B D R dv_cache_0001 dv_cache_0021 dv_cache_0004 dv_cache_0025
      dv_cache_0015 dv_cache_0022 dv_cache_0007 dv_cache_0026 dv_cache_0017 dv_cache_0023
      dv_cache_0027 dv_cache_0024 dv_cache_0028 dv_cache_0020 dv_cache_0029
  have p0131 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (syn_wa (syn_wa
          (syn_w3a (syn_wbr R (syn_cwe) A) (.classMem (.cv x) B) (.classMem (.cv y) B))
          (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))) (.classMem D A))
      (syn_wb (.classMem (.cv x) D) (.classMem (.cv y) D)) p0129 p0130
  have p0132 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
                (syn_wa (.classMem C A) (.classMem D A)))
              (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
          (.classMem (.cv y) D))
        (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classMem (.cv x) D) (.classMem (.cv y) D) p0039 p0131
  have p0133 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
              (syn_wa (.classMem C A) (.classMem D A)))
            (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
        (.classMem (.cv y) D))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
      (.classMem (.cv x) D) p0132
  have p0134 :=
    @g_rexlimdva
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y)))
      (.classMem (.cv x) D) y D dv_cache_0030 dv_cache_0031 p0133
  have p0135 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classMem (.cv x) C))
      (syn_wrex y D (.classEq (syn_cfdrow R A B (.cv x)) (syn_cfdrow R A B (.cv y))))
      (.classMem (.cv x) D) p0036 p0134
  have p0136 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem (.cv x) C) (.classMem (.cv x) D) p0135
  have p0137 :=
    @g_ssrdv
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
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

@[expose]
noncomputable def g_fdcodeinj2 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_fdcodeinj2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcodeinj2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcodeinj2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
            (syn_wa (.classMem C A) (.classMem D A)))
          (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))) (.classEq C D)) :=
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
    @g_fdcodesub2 A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      hyp_fdcodeinj2_1 hyp_fdcodeinj2_2 hyp_fdcodeinj2_3
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0002 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem C A) (.classMem D A))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B))) p0001 p0002
  have p0005 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem C A) (.classMem D A))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (syn_wa (.classMem C A) (.classMem D A)) p0001 p0005
  have p0007 := @g_simpr (.classMem C A) (.classMem D A)
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (.classMem C A) (.classMem D A)) (.classMem D A) p0006 p0007
  have p0012 := @g_simpl (.classMem C A) (.classMem D A)
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (.classMem C A) (.classMem D A)) (.classMem C A) p0006 p0012
  have p0014 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (.classMem D A) (.classMem C A) p0008 p0013
  have p0015 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
      (syn_wa (.classMem D A) (.classMem C A)) p0003 p0014
  have p0016 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem C A) (.classMem D A)))
      (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D))
  have p0017 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_cfdcode R A B C) (syn_cfdcode R A B D) p0016
  have p0018 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
        (syn_wa (.classMem D A) (.classMem C A)))
      (.classEq (syn_cfdcode R A B D) (syn_cfdcode R A B C)) p0015 p0017
  have p0019 :=
    @g_fdcodesub2 A B D C R dv_cache_0001 dv_cache_0003 dv_cache_0002 dv_cache_0004
      dv_cache_0006 dv_cache_0005 dv_cache_0007 dv_cache_0011 dv_cache_0010 dv_cache_0009
      hyp_fdcodeinj2_1 hyp_fdcodeinj2_2 hyp_fdcodeinj2_3
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem D A) (.classMem C A)))
        (.classEq (syn_cfdcode R A B D) (syn_cfdcode R A B C)))
      (syn_wss D C) p0018 p0019
  have p0021 :=
    @g_eqssd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (syn_wss A (syn_cpw B)))
          (syn_wa (.classMem C A) (.classMem D A)))
        (.classEq (syn_cfdcode R A B C) (syn_cfdcode R A B D)))
      C D p0000 p0020
  exact p0021

@[expose]
noncomputable def g_wppimagefn (R : Class)
    (hyp_wppimagefn_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cimage R) (syn_cvv)) :=
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
  have dv_cache_0001 : y ∉ ((syn_cima R (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cimage R)).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_cimage R)).fv :=
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
  have p0000 := @g_vex x
  have p0001 := @g_imaex R (.cv x) hyp_wppimagefn_1 p0000
  have p0002 := @g_eueq y (syn_cima R (.cv x)) dv_cache_0001
  have p0003 :=
    @g_mpbi (.classMem (syn_cima R (.cv x)) (syn_cvv))
      (syn_weu y (.classEq (.cv y) (syn_cima R (.cv x)))) p0001 p0002
  have p0005 := @g_vex y
  have p0006 := @g_brimage (.cv x) (.cv y) R p0000 p0005
  have p0007 :=
    @g_eubii (syn_wbr (.cv x) (syn_cimage R) (.cv y))
      (.classEq (.cv y) (syn_cima R (.cv x))) y p0006
  have p0008 :=
    @g_mpbir (syn_weu y (syn_wbr (.cv x) (syn_cimage R) (.cv y)))
      (syn_weu y (.classEq (.cv y) (syn_cima R (.cv x)))) p0003 p0007
  have p0009 :=
    @g_rgenw (syn_weu y (syn_wbr (.cv x) (syn_cimage R) (.cv y))) x (syn_cvv) p0008
  have p0010 :=
    @g_fnres x y (syn_cvv) (syn_cimage R) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_mpbir (syn_wfn (syn_cres (syn_cimage R) (syn_cvv)) (syn_cvv))
      (syn_wral x (syn_cvv) (syn_weu y (syn_wbr (.cv x) (syn_cimage R) (.cv y)))) p0009
      p0010
  have p0012 := @g_resid (syn_cimage R)
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cimage R) (syn_cvv)) (syn_cimage R) p0012
  have p0014 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cimage R) (syn_cvv)) (syn_cvv))
      (syn_wfn (syn_cimage R) (syn_cvv)) p0011 p0013
  exact p0014

@[expose]
noncomputable def g_wppfvimage (A : Class) (R : Class) (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_wppfvimage_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_wppfvimage_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage R) A) (syn_cima R A)) :=
  by
  have p0000 := @g_eqid (syn_cima R A)
  have p0001 := @g_imaex R A hyp_wppfvimage_1 hyp_wppfvimage_2
  have p0002 := @g_brimage A (syn_cima R A) R hyp_wppfvimage_2 p0001
  have p0003 :=
    @g_mpbir (syn_wbr A (syn_cimage R) (syn_cima R A))
      (.classEq (syn_cima R A) (syn_cima R A)) p0000 p0002
  have p0004 := @g_tru
  have p0005 := @g_wppimagefn R hyp_wppfvimage_1
  have p0006 := @g_a1i (syn_wfn (syn_cimage R) (syn_cvv)) syn_wtru p0005
  have p0007 := @g_a1i (.classMem A (syn_cvv)) syn_wtru hyp_wppfvimage_2
  have p0008 :=
    @g_jca syn_wtru (syn_wfn (syn_cimage R) (syn_cvv)) (.classMem A (syn_cvv)) p0006 p0007
  have p0009 := Nominal.mp p0004 p0008
  have p0010 := @g_fnbrfvb (syn_cvv) A (syn_cima R A) (syn_cimage R)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage R) A) (syn_cima R A))
      (syn_wbr A (syn_cimage R) (syn_cima R A)) p0003 p0011
  exact p0012

@[expose]
noncomputable def g_fdpointrelex (A : Class)
    (hyp_fdpointrelex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdpointrel A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdpointrel A))
  have p0001 := @g_fdmemex
  have p0002 := @g_kqrelex (syn_cfdmem) p0001
  have p0003 := @g_vvex
  have p0004 := @g_uniex A hyp_fdpointrelex_1
  have p0005 := @g_pw1ex (syn_cuni A) p0004
  have p0006 := @g_pw1ex (syn_cpw1 (syn_cuni A)) p0005
  have p0007 := @g_xpex (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))) p0003 p0006
  have p0008 :=
    @g_inex (syn_ckqrel (syn_cfdmem))
      (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0002 p0007
  have p0009 :=
    @g_eqeltri (syn_cfdpointrel A)
      (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (syn_cvv) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_fdglobalrowex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdglobalrowex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdglobalrowex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdglobalrowex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdglobalrowmap R A B) (syn_cvv)) :=
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
  have dv_cache_0014 : u ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv :=
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
  have dv_cache_0015 : u ∉ ((syn_cfdrowrel R A B)).fv :=
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
  have dv_cache_0016 : d ∉ ((syn_cfdrowrel R A B)).fv :=
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
  have dv_cache_0017 : d ∉ ((syn_cfdrowfib R A B (.cv u))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdglobalrowmap u A B
      R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @g_iftrue (syn_wbr R (syn_cwe) A)
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_c0)
  have p0002 := @g_vex d
  have p0003 :=
    @g_elfdrowfibg A B (.cv u) (.cv d) R dv_cache_0001 dv_cache_0007 dv_cache_0008
      dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0004 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_bicomi (.classMem (.cv d) (syn_cfdrowfib R A B (.cv u)))
      (.classMem (syn_cop (syn_csn (.cv d)) (.cv u)) (syn_cfdrowrel R A B)) p0004
  have p0006 :=
    @g_releqmpt u d (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowrel R A B)
      (syn_cfdrowfib R A B (.cv u)) dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 p0005
  have p0007 :=
    @g_a1i
      (.classEq (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv
            (syn_ccompl (syn_cima
                (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
                (syn_c1c)))))
        (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))))
      (syn_wbr R (syn_cwe) A) p0006
  have p0008 := @g_uniex A hyp_fdglobalrowex_2
  have p0009 := @g_pw1ex (syn_cuni A) p0008
  have p0010 := @g_pw1ex (syn_cpw1 (syn_cuni A)) p0009
  have p0011 :=
    @g_a1i (.classMem (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv))
      (syn_wbr R (syn_cwe) A) p0010
  have p0012 := @g_vvex
  have p0013 := @g_a1i (.classMem (syn_cvv) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0012
  have p0014 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv))
      (.classMem (syn_cvv) (syn_cvv)) p0011 p0013
  have p0015 := @g_xpexg (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0016 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv))
        (.classMem (syn_cvv) (syn_cvv)))
      (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_cvv)) p0014
      p0015
  have p0017 := @g_ssetex
  have p0018 := @g_ins3ex (syn_csset) p0017
  have p0019 :=
    @g_a1i (.classMem (syn_cins3 (syn_csset)) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0018
  have p0020 :=
    @g_fdrowrelex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0004 hyp_fdglobalrowex_1
      hyp_fdglobalrowex_2 hyp_fdglobalrowex_3
  have p0021 := @g_ins2exg (syn_cfdrowrel R A B) (syn_cvv)
  have p0022 :=
    @g_syl (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrowrel R A B) (syn_cvv))
      (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cins3 (syn_csset)) (syn_cvv))
      (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)) p0019 p0022
  have p0024 :=
    @g_symdifexg (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)
      (syn_cvv)
  have p0025 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cins3 (syn_csset)) (syn_cvv))
        (.classMem (syn_cins2 (syn_cfdrowrel R A B)) (syn_cvv)))
      (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
        (syn_cvv))
      p0023 p0024
  have p0026 := @g_n_1cex
  have p0027 := @g_a1i (.classMem (syn_c1c) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0026
  have p0028 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
        (syn_cvv))
      (.classMem (syn_c1c) (syn_cvv)) p0025 p0027
  have p0029 :=
    @g_imaexg (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
      (syn_c1c) (syn_cvv) (syn_cvv)
  have p0030 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)))
      (.classMem
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_c1c)) (syn_cvv))
      p0028 p0029
  have p0031 :=
    @g_complexg
      (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
        (syn_c1c))
      (syn_cvv)
  have p0032 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (.classMem
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_c1c)) (syn_cvv))
      (.classMem (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))
        (syn_cvv))
      p0030 p0031
  have p0033 :=
    @g_cnvexg
      (syn_ccompl
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
          (syn_c1c)))
      (syn_cvv)
  have p0034 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (.classMem (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c)))
        (syn_cvv))
      (.classMem (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
              (syn_c1c)))) (syn_cvv))
      p0032 p0033
  have p0035 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_cvv))
      (.classMem (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
              (syn_c1c)))) (syn_cvv))
      p0016 p0034
  have p0036 :=
    @g_inexg (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv))
      (syn_ccnv (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B))) (syn_c1c))))
      (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_cvv))
        (.classMem (syn_ccnv (syn_ccompl (syn_cima
                (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
                (syn_c1c)))) (syn_cvv)))
      (.classMem (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv
            (syn_ccompl (syn_cima
                (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
                (syn_c1c))))) (syn_cvv))
      p0035 p0036
  have p0038 :=
    @g_eqeltrrd (syn_wbr R (syn_cwe) A)
      (syn_cin (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cvv)) (syn_ccnv (syn_ccompl
            (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cfdrowrel R A B)))
              (syn_c1c)))))
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_cvv) p0007 p0037
  have p0039 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A)
      (syn_cif (syn_wbr R (syn_cwe) A)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0))
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_cvv) p0001 p0038
  have p0040 :=
    @g_iffalse (syn_wbr R (syn_cwe) A)
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_c0)
  have p0041 := @g_n_0ex
  have p0042 := @g_a1i (.classMem (syn_c0) (syn_cvv)) (.neg (syn_wbr R (syn_cwe) A)) p0041
  have p0043 :=
    @g_eqeltrd (.neg (syn_wbr R (syn_cwe) A))
      (syn_cif (syn_wbr R (syn_cwe) A)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0))
      (syn_c0) (syn_cvv) p0040 p0042
  have p0044 :=
    @g_pm2_61i (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cif (syn_wbr R (syn_cwe) A)
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_c0)) (syn_cvv))
      p0039 p0043
  have p0045 :=
    @g_eqeltri (syn_cfdglobalrowmap R A B)
      (syn_cif (syn_wbr R (syn_cwe) A)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0))
      (syn_cvv) p0000 p0044
  exact p0045

@[expose]
noncomputable def g_fdglobalrowval (u : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_u : u ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_u : u ∉ B.fv) (dv_R_u : u ∉ R.fv) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (.classEq (syn_cfdglobalrowmap R A B)
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdglobalrowmap u A B
      R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfdglobalrowmap R A B) (syn_cif (syn_wbr R (syn_cwe) A)
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_c0)))
      (syn_wbr R (syn_cwe) A) p0000
  have p0002 :=
    @g_iftrue (syn_wbr R (syn_cwe) A)
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_c0)
  have p0003 :=
    @g_eqtrd (syn_wbr R (syn_cwe) A) (syn_cfdglobalrowmap R A B)
      (syn_cif (syn_wbr R (syn_cwe) A)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) (syn_c0))
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))) p0001
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

@[expose]
noncomputable def g_fdpointimage (A : Class) (c : Var) (_dv_A_c : c ∉ A.fv)
    (_hyp_fdpointimage_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv c) A)
        (.classEq (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))
          (syn_cpw1 (syn_cpw1 (.cv c))))) :=
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
  have dv_cache_0001 : Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv c))).fv := by
    exact
      (show Disjoint ((syn_cfdmem)).fv ((syn_csn (.cv c))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact (show Disjoint ((∅ : Finset Var)) (((Class.cv c)).fv) from (by simp))))
  have dv_cache_0002 : Disjoint ((syn_cfdmem)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((syn_cfdmem)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact (show Disjoint ((∅ : Finset Var)) (({ d } : Finset Var)) from (by simp))))
  have dv_cache_0003 : Disjoint ((syn_csn (.cv c))).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((syn_csn (.cv c))).fv ((Class.cv d)).fv from (by
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
  have dv_cache_0005 : x ∉ ((syn_cuni A)).fv :=
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
  have dv_cache_0009 : y ∉ ((Wff.classEq (.cv d) (syn_csn (syn_csn (.cv x))))).fv :=
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
    x ∉ ((syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))).fv :=
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
    x ∉ ((Wff.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))).fv :=
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
  have dv_cache_0014 : x ∉ ((Wff.classEq (.cv d) (syn_csn (syn_csn (.cv y))))).fv :=
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
      ((syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
          (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))).fv :=
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
    d ∉ ((syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))).fv :=
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
  have dv_cache_0019 : d ∉ ((syn_cpw1 (syn_cpw1 (.cv c)))).fv :=
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
  have p0000 := @g_elimasn (syn_cfdpointrel A) (syn_csn (.cv c)) (.cv d)
  have p0001 := (Nominal.classEqRefl (syn_cfdpointrel A))
  have p0002 :=
    @g_eleq2i (syn_cfdpointrel A)
      (syn_cin (syn_ckqrel (syn_cfdmem)) (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (syn_cop (syn_csn (.cv c)) (.cv d)) p0001
  have p0003 :=
    @g_bitri
      (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c)))))
      (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cfdpointrel A))
      (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cin (syn_ckqrel (syn_cfdmem))
          (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))))
      p0000 p0002
  have p0004 :=
    @g_elin (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_ckqrel (syn_cfdmem))
      (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
  have p0005 := @g_snex (.cv c)
  have p0006 := @g_vex d
  have p0007 :=
    @g_kqrelbr (syn_cfdmem) (syn_csn (.cv c)) (.cv d) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0005 p0006
  have p0009 :=
    @g_opelxp (syn_csn (.cv c)) (.cv d) (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
  have p0010 :=
    @g_mpbiran
      (.classMem (syn_cop (syn_csn (.cv c)) (.cv d))
        (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (.classMem (syn_csn (.cv c)) (syn_cvv))
      (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0005 p0009
  have p0011 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_ckqrel (syn_cfdmem)))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classMem (syn_cop (syn_csn (.cv c)) (.cv d))
        (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0007 p0010
  have p0012 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cin (syn_ckqrel (syn_cfdmem))
          (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_ckqrel (syn_cfdmem)))
        (.classMem (syn_cop (syn_csn (.cv c)) (.cv d))
          (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      p0004 p0011
  have p0013 :=
    @g_bitri
      (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c)))))
      (.classMem (syn_cop (syn_csn (.cv c)) (.cv d)) (syn_cin (syn_ckqrel (syn_cfdmem))
          (syn_cxp (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cuni A))))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      p0003 p0012
  have p0014 :=
    @g_a1i
      (syn_wb (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c)))))
        (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
          (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))))
      (.classMem (.cv c) A) p0013
  have p0015 := @g_elpw12 x (.cv d) (syn_cuni A) dv_cache_0004 dv_cache_0005
  have p0016 :=
    @g_a1i
      (syn_wb (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
        (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
      (.classMem (.cv c) A) p0015
  have p0017 :=
    @g_anbi2d (.classMem (.cv c) A) (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) p0016
  have p0018 :=
    @g_simpl (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0019 :=
    @g_simpr (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0020 := @g_id (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
  have p0021 :=
    @g_opkeq2d (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) (.cv d)
      (syn_csn (syn_csn (.cv x))) (syn_csn (.cv c)) p0020
  have p0022 :=
    @g_eleq1d (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
      (syn_copk (syn_csn (.cv c)) (.cv d))
      (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv x)))) (syn_cfdmem) p0021
  have p0023 := @g_vex x
  have p0024 := @g_fdmemval (.cv x) c dv_cache_0006 p0023
  have p0025 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv x)))) (syn_cfdmem))
        (.classMem (.cv x) (.cv c)))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) p0024
  have p0026 :=
    @g_bitrd (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv x)))) (syn_cfdmem))
      (.classMem (.cv x) (.cv c)) p0022 p0025
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classMem (.cv x) (.cv c)))
      p0019 p0026
  have p0028 :=
    @g_mpbid
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classMem (.cv x) (.cv c)) p0018 p0027
  have p0030 :=
    @g_jca
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (.classMem (.cv x) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) p0028
      p0019
  have p0031 := @g_id (.classEq (.cv y) (.cv x))
  have p0032 := @g_sneqd (.classEq (.cv y) (.cv x)) (.cv y) (.cv x) p0031
  have p0033 :=
    @g_sneqd (.classEq (.cv y) (.cv x)) (syn_csn (.cv y)) (syn_csn (.cv x)) p0032
  have p0034 :=
    @g_eqeq2d (.classEq (.cv y) (.cv x)) (syn_csn (syn_csn (.cv y)))
      (syn_csn (syn_csn (.cv x))) (.cv d) p0033
  have p0035 :=
    @g_rspcev (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))) y (.cv x) (.cv c) dv_cache_0007
      dv_cache_0008 dv_cache_0009 p0034
  have p0036 :=
    @g_syl
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv x) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0030 p0035
  have p0037 :=
    @g_ex (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0036
  have p0038 :=
    @g_a1d (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.imp (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
        (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classMem (.cv x) (syn_cuni A)) p0037
  have p0039 :=
    @g_rexlimdv (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) x (syn_cuni A)
      dv_cache_0010 dv_cache_0011 p0038
  have p0040 :=
    @g_imp (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x)))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0039
  have p0041 :=
    @g_a1i
      (.imp (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
          (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
        (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classMem (.cv c) A) p0040
  have p0042 :=
    @g_simprl (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0043 :=
    @g_simprr (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0044 := @g_id (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
  have p0045 :=
    @g_opkeq2d (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) (.cv d)
      (syn_csn (syn_csn (.cv y))) (syn_csn (.cv c)) p0044
  have p0046 :=
    @g_eleq1d (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (syn_copk (syn_csn (.cv c)) (.cv d))
      (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv y)))) (syn_cfdmem) p0045
  have p0047 := @g_vex y
  have p0048 := @g_fdmemval (.cv y) c dv_cache_0012 p0047
  have p0049 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv y)))) (syn_cfdmem))
        (.classMem (.cv y) (.cv c)))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) p0048
  have p0050 :=
    @g_bitrd (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv c)) (syn_csn (syn_csn (.cv y)))) (syn_cfdmem))
      (.classMem (.cv y) (.cv c)) p0046 p0049
  have p0051 :=
    @g_biimprd (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (.classMem (.cv y) (.cv c)) p0050
  have p0052 :=
    @g_syl
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (.imp (.classMem (.cv y) (.cv c))
        (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)))
      p0043 p0051
  have p0053 :=
    @g_mpd
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classMem (.cv y) (.cv c))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem)) p0042 p0052
  have p0054 :=
    @g_simpl (.classMem (.cv c) A)
      (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))
  have p0056 :=
    @g_jca
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)) p0054 p0042
  have p0057 := @g_elssuni (.cv c) A
  have p0058 := @g_sselda (.classMem (.cv c) A) (.cv c) (syn_cuni A) (.cv y) p0057
  have p0059 :=
    @g_syl
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv c) A) (.classMem (.cv y) (.cv c)))
      (.classMem (.cv y) (syn_cuni A)) p0056 p0058
  have p0061 :=
    @g_jca
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classMem (.cv y) (syn_cuni A)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      p0059 p0043
  have p0062 := @g_id (.classEq (.cv x) (.cv y))
  have p0063 := @g_sneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0062
  have p0064 :=
    @g_sneqd (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) p0063
  have p0065 :=
    @g_eqeq2d (.classEq (.cv x) (.cv y)) (syn_csn (syn_csn (.cv x)))
      (syn_csn (syn_csn (.cv y))) (.cv d) p0064
  have p0066 :=
    @g_rspcev (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))) x (.cv y) (syn_cuni A) dv_cache_0013
      dv_cache_0005 dv_cache_0014 p0065
  have p0067 :=
    @g_syl
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (syn_wa (.classMem (.cv y) (syn_cuni A)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))
      (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) p0061 p0066
  have p0068 :=
    @g_jca
      (syn_wa (.classMem (.cv c) A) (syn_wa (.classMem (.cv y) (.cv c))
          (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
      (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))) p0053 p0067
  have p0069 :=
    @g_ex (.classMem (.cv c) A)
      (syn_wa (.classMem (.cv y) (.cv c)) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
      p0068
  have p0070 :=
    @g_exp3a (.classMem (.cv c) A) (.classMem (.cv y) (.cv c))
      (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
      p0069
  have p0071 :=
    @g_rexlimdv (.classMem (.cv c) A) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
      y (.cv c) dv_cache_0015 dv_cache_0016 p0070
  have p0072 :=
    @g_impbid (.classMem (.cv c) A)
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0041 p0071
  have p0073 :=
    @g_bitrd (.classMem (.cv c) A)
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (syn_wrex x (syn_cuni A) (.classEq (.cv d) (syn_csn (syn_csn (.cv x))))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0017 p0072
  have p0074 := @g_elpw12 y (.cv d) (.cv c) dv_cache_0017 dv_cache_0008
  have p0075 :=
    @g_bicomi (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y))))) p0074
  have p0076 :=
    @g_a1i
      (syn_wb (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))
        (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c)))))
      (.classMem (.cv c) A) p0075
  have p0077 :=
    @g_bitrd (.classMem (.cv c) A)
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (syn_wrex y (.cv c) (.classEq (.cv d) (syn_csn (syn_csn (.cv y)))))
      (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c)))) p0073 p0076
  have p0078 :=
    @g_bitrd (.classMem (.cv c) A)
      (.classMem (.cv d) (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c)))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv c)) (.cv d)) (syn_cfdmem))
        (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (syn_cuni A)))))
      (.classMem (.cv d) (syn_cpw1 (syn_cpw1 (.cv c)))) p0014 p0077
  have p0079 :=
    @g_eqrdv (.classMem (.cv c) A) d
      (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv c))))
      (syn_cpw1 (syn_cpw1 (.cv c))) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0078
  exact p0079

@[expose]
noncomputable def g_fdglobalrowima (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
        (.classEq (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C)))
          (syn_cfdcode R A B C))) :=
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
  have dv_cache_0007 : u ∉ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv :=
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
  have dv_cache_0008 : u ∉ ((syn_cpw1 (syn_cpw1 C))).fv :=
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
  have p0000 := @g_simpl (syn_wbr R (syn_cwe) A) (.classMem C A)
  have p0001 :=
    @g_fdglobalrowval u A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_wbr R (syn_cwe) A)
      (.classEq (syn_cfdglobalrowmap R A B)
        (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u))))
      p0000 p0001
  have p0003 :=
    @g_imaeq1d (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_cfdglobalrowmap R A B)
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_cpw1 (syn_cpw1 C)) p0002
  have p0004 :=
    @g_dfima3
      (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
      (syn_cpw1 (syn_cpw1 C))
  have p0005 :=
    @g_a1i
      (.classEq (syn_cima
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_cpw1 (syn_cpw1 C))) (syn_crn (syn_cres
            (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
            (syn_cpw1 (syn_cpw1 C)))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) p0004
  have p0006 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C)))
      (syn_cima (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
        (syn_cpw1 (syn_cpw1 C)))
      (syn_crn (syn_cres
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_cpw1 (syn_cpw1 C))))
      p0003 p0005
  have p0007 := @g_simpr (syn_wbr R (syn_cwe) A) (.classMem C A)
  have p0008 := @g_elssuni C A
  have p0009 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (.classMem C A)
      (syn_wss C (syn_cuni A)) p0007 p0008
  have p0010 := @g_pw1ss C (syn_cuni A)
  have p0011 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) (syn_wss C (syn_cuni A))
      (syn_wss (syn_cpw1 C) (syn_cpw1 (syn_cuni A))) p0009 p0010
  have p0012 := @g_pw1ss (syn_cpw1 C) (syn_cpw1 (syn_cuni A))
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_wss (syn_cpw1 C) (syn_cpw1 (syn_cuni A)))
      (syn_wss (syn_cpw1 (syn_cpw1 C)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) p0011 p0012
  have p0014 :=
    @g_resmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cpw1 (syn_cpw1 C))
      (syn_cfdrowfib R A B (.cv u)) dv_cache_0007 dv_cache_0008
  have p0015 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_wss (syn_cpw1 (syn_cpw1 C)) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
      (.classEq (syn_cres
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_cpw1 (syn_cpw1 C)))
        (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))))
      p0013 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcodemap2 u A B C R
      dv_cache_0001 dv_cache_0009 dv_cache_0002 dv_cache_0003 dv_cache_0010 dv_cache_0004
      dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0006
  have p0017 :=
    @g_eqcomi (syn_cfdcodemap2 R A B C)
      (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u))) p0016
  have p0018 :=
    @g_a1i
      (.classEq (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))
        (syn_cfdcodemap2 R A B C))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) p0017
  have p0019 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
        (syn_cpw1 (syn_cpw1 C)))
      (syn_cmpt u (syn_cpw1 (syn_cpw1 C)) (syn_cfdrowfib R A B (.cv u)))
      (syn_cfdcodemap2 R A B C) p0015 p0018
  have p0020 :=
    @g_rneqd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_cres (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
        (syn_cpw1 (syn_cpw1 C)))
      (syn_cfdcodemap2 R A B C) p0019
  have p0021 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C)))
      (syn_crn (syn_cres
          (syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (.cv u)))
          (syn_cpw1 (syn_cpw1 C))))
      (syn_crn (syn_cfdcodemap2 R A B C)) p0006 p0020
  have p0022 :=
    @g_fdcodeeqrnmap2 A B C R dv_cache_0001 dv_cache_0009 dv_cache_0002 dv_cache_0010
      dv_cache_0004 dv_cache_0011
  have p0023 := @g_eqcomi (syn_cfdcode R A B C) (syn_crn (syn_cfdcodemap2 R A B C)) p0022
  have p0024 :=
    @g_a1i (.classEq (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cfdcode R A B C))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A)) p0023
  have p0025 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem C A))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 C)))
      (syn_crn (syn_cfdcodemap2 R A B C)) (syn_cfdcode R A B C) p0021 p0024
  exact p0025

@[expose]
noncomputable def g_fdcolcodemapex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodemapex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodemapex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdcolcodemap R A B) (syn_cvv))) :=
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
  have p0000 := (Nominal.classEqRefl (syn_cfdcolcodemap R A B))
  have p0001 :=
    @g_fdglobalrowex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapex_1
      hyp_fdcolcodemapex_2 hyp_fdcolcodemapex_3
  have p0002 := @g_imageex (syn_cfdglobalrowmap R A B) p0001
  have p0003 := @g_fdpointrelex A hyp_fdcolcodemapex_2
  have p0004 := @g_imageex (syn_cfdpointrel A) p0003
  have p0005 :=
    @g_coex (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A))
      p0002 p0004
  have p0006 := @g_pw1ex A hyp_fdcolcodemapex_2
  have p0007 := @g_pw1ex (syn_cpw1 A) p0006
  have p0008 :=
    @g_resex
      (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
      (syn_cpw1 (syn_cpw1 A)) p0005 p0007
  have p0009 :=
    @g_eqeltri (syn_cfdcolcodemap R A B)
      (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
      (syn_cvv) p0000 p0008
  have p0010 :=
    @g_a1i (.classMem (syn_cfdcolcodemap R A B) (syn_cvv)) (syn_wbr R (syn_cwe) A) p0009
  exact p0010

@[expose]
noncomputable def g_fdcolcodemapfn (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapfn_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodemapfn_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodemapfn_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A)
        (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))) :=
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
  have dv_cache_0004 : x ∉ ((syn_crn (syn_cimage (syn_cfdpointrel A)))).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
    @g_fdglobalrowex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapfn_1
      hyp_fdcolcodemapfn_2 hyp_fdcolcodemapfn_3
  have p0001 := @g_wppimagefn (syn_cfdglobalrowmap R A B) p0000
  have p0002 := @g_fdpointrelex A hyp_fdcolcodemapfn_2
  have p0003 := @g_wppimagefn (syn_cfdpointrel A) p0002
  have p0004 := @g_elex (.cv x) (syn_crn (syn_cimage (syn_cfdpointrel A)))
  have p0005 :=
    @g_ssriv x (syn_crn (syn_cimage (syn_cfdpointrel A))) (syn_cvv) dv_cache_0004
      dv_cache_0005 p0004
  have p0006 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cfdglobalrowmap R A B))
      (syn_cimage (syn_cfdpointrel A))
  have p0007 :=
    @g_mp3an (syn_wfn (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cvv))
      (syn_wfn (syn_cimage (syn_cfdpointrel A)) (syn_cvv))
      (syn_wss (syn_crn (syn_cimage (syn_cfdpointrel A))) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cvv))
      p0001 p0003 p0005 p0006
  have p0008 :=
    @g_fnresin1 (syn_cvv) (syn_cpw1 (syn_cpw1 A))
      (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_elex (.cv x) (syn_cpw1 (syn_cpw1 A))
  have p0011 :=
    @g_ssriv x (syn_cpw1 (syn_cpw1 A)) (syn_cvv) dv_cache_0006 dv_cache_0005 p0010
  have p0012 := @g_sseqin2 (syn_cpw1 (syn_cpw1 A)) (syn_cvv)
  have p0013 :=
    @g_mpbi (syn_wss (syn_cpw1 (syn_cpw1 A)) (syn_cvv))
      (.classEq (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))) p0011
      p0012
  have p0014 :=
    @g_reseq2i (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))
      (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
      p0013
  have p0015 :=
    @g_fneq1i (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A)))
      (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))))
      (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
      p0014
  have p0016 :=
    @g_mpbi
      (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))))
        (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))))
      (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
        (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))))
      p0009 p0015
  have p0021 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A))
      (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
      p0013
  have p0022 :=
    @g_mpbi
      (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
        (syn_cin (syn_cvv) (syn_cpw1 (syn_cpw1 A))))
      (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A)))
      p0016 p0021
  have p0023 := (Nominal.classEqRefl (syn_cfdcolcodemap R A B))
  have p0024 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 A)) (syn_cfdcolcodemap R A B)
      (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
      p0023
  have p0025 :=
    @g_mpbir (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))
      (syn_wfn (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 A)))
      p0022 p0024
  have p0026 :=
    @g_a1i (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))
      (syn_wbr R (syn_cwe) A) p0025
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

@[expose]
noncomputable def g_fdcolcodemapval (A : Class) (B : Class) (R : Class) (q : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_q : q ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_q : q ∉ B.fv) (dv_R_q : q ∉ R.fv)
    (hyp_fdcolcodemapval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodemapval_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodemapval_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))) :=
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
  have dv_cache_0003 : Disjoint ((Class.cv q)).fv ((syn_cfdpointrel A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((Class.cv q)).fv ((syn_cfdpointrel A)).fv from (by
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
    Disjoint ((syn_cpw1 (syn_cpw1 (.cv x)))).fv ((syn_cfdglobalrowmap R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((syn_cpw1 (syn_cpw1 (.cv x)))).fv ((syn_cfdglobalrowmap R A B)).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdglobalrowmap];
          exact
            (show Disjoint (((syn_cpw1 (.cv x))).fv) (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(Finset.disjoint_union_right.mpr
                    ⟨(show Disjoint (((syn_cpw1 (.cv x))).fv) ((A).fv) from
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
                      (show Disjoint (((syn_cpw1 (.cv x))).fv) ((B).fv) from
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
                  (show Disjoint (((syn_cpw1 (.cv x))).fv) ((R).fv) from
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
  have dv_cache_0008 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
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
                            (show q ∉ (A).fv from (by exact dv_A_q))))))))))
  have dv_cache_0009 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
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
                            (show q ∉ (B).fv from (by exact dv_B_q))))))))))
  have dv_cache_0010 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
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
                            (show q ∉ (R).fv from (by exact dv_R_q))))))))))
  have dv_cache_0011 :
    x ∉
      ((Wff.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))).fv :=
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
      ((syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))).fv :=
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
    @g_simpr (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0001 := @g_elpw12 x (.cv q) A dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
        (syn_wrex x A (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) p0001
  have p0003 :=
    @g_mpbid (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (syn_wrex x A (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))) p0000 p0002
  have p0004 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
  have p0005 := (Nominal.classEqRefl (syn_cfdcolcodemap R A B))
  have p0006 :=
    @g_fveq1i (.cv q) (syn_cfdcolcodemap R A B)
      (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A)))
      p0005
  have p0007 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q)) (syn_cfv (syn_cres
            (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
            (syn_cpw1 (syn_cpw1 A))) (.cv q)))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) p0006
  have p0009 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cpw1 A))
      (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
  have p0010 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (.classEq (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
              (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (.cv q)) (syn_cfv
          (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cimage (syn_cfdpointrel A)))
          (.cv q)))
      p0000 p0009
  have p0011 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cfv (syn_cres (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (syn_cpw1 (syn_cpw1 A))) (.cv q))
      (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (.cv q))
      p0007 p0010
  have p0012 := @g_vex q
  have p0013 := @g_fdpointrelex A hyp_fdcolcodemapval_2
  have p0014 := @g_wppimagefn (syn_cfdpointrel A) p0013
  have p0015 :=
    @g_fvco2 (syn_cvv) (.cv q) (syn_cimage (syn_cfdglobalrowmap R A B))
      (syn_cimage (syn_cfdpointrel A))
  have p0016 :=
    @g_mpan (syn_wfn (syn_cimage (syn_cfdpointrel A)) (syn_cvv))
      (.classMem (.cv q) (syn_cvv))
      (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (.cv q))
        (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))))
      p0014 p0015
  have p0017 := Nominal.mp p0012 p0016
  have p0018 :=
    @g_a1i
      (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
            (syn_cimage (syn_cfdpointrel A))) (.cv q))
        (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))) p0017
  have p0019 :=
    @g_eqtrd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cfv (syn_ccom (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cimage (syn_cfdpointrel A))) (.cv q))
      (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B))
        (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)))
      p0011 p0018
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B))
          (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))))
      p0004 p0019
  have p0023 := @g_wppfvimage (.cv q) (syn_cfdpointrel A) dv_cache_0003 p0013 p0012
  have p0024 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))
        (syn_cima (syn_cfdpointrel A) (.cv q)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      p0023
  have p0025 :=
    @g_simprr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0026 :=
    @g_imaeq2d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.cv q) (syn_csn (syn_csn (.cv x))) (syn_cfdpointrel A) p0025
  have p0027 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))
      (syn_cima (syn_cfdpointrel A) (.cv q))
      (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv x)))) p0024 p0026
  have p0028 :=
    @g_simprl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0029 := @g_fdpointimage A x dv_cache_0002 hyp_fdcolcodemapval_2
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.classMem (.cv x) A)
      (.classEq (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv x))))
        (syn_cpw1 (syn_cpw1 (.cv x))))
      p0028 p0029
  have p0031 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q))
      (syn_cima (syn_cfdpointrel A) (syn_csn (syn_csn (.cv x))))
      (syn_cpw1 (syn_cpw1 (.cv x))) p0027 p0030
  have p0032 :=
    @g_fveq2d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)) (syn_cpw1 (syn_cpw1 (.cv x)))
      (syn_cimage (syn_cfdglobalrowmap R A B)) p0031
  have p0033 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B))
        (syn_cfv (syn_cimage (syn_cfdpointrel A)) (.cv q)))
      (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cpw1 (syn_cpw1 (.cv x))))
      p0020 p0032
  have p0034 :=
    @g_fdglobalrowex A B R dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_fdcolcodemapval_1
      hyp_fdcolcodemapval_2 hyp_fdcolcodemapval_3
  have p0035 := @g_vex x
  have p0036 := @g_pw1ex (.cv x) p0035
  have p0037 := @g_pw1ex (syn_cpw1 (.cv x)) p0036
  have p0038 :=
    @g_wppfvimage (syn_cpw1 (syn_cpw1 (.cv x))) (syn_cfdglobalrowmap R A B) dv_cache_0007
      p0034 p0037
  have p0039 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cpw1 (syn_cpw1 (.cv x))))
        (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (.cv x)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      p0038
  have p0040 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cfv (syn_cimage (syn_cfdglobalrowmap R A B)) (syn_cpw1 (syn_cpw1 (.cv x))))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (.cv x)))) p0033 p0039
  have p0042 :=
    @g_unieqd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.cv q) (syn_csn (syn_csn (.cv x))) p0025
  have p0043 := @g_snex (.cv x)
  have p0044 := @g_unisn (syn_csn (.cv x)) p0043
  have p0045 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      p0044
  have p0046 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0042
      p0045
  have p0047 :=
    @g_unieqd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cuni (.cv q)) (syn_csn (.cv x)) p0046
  have p0049 := @g_unisn (.cv x) p0035
  have p0050 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv x))) (.cv x))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      p0049
  have p0051 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_csn (.cv x))) (.cv x) p0047 p0050
  have p0052 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cuni (syn_cuni (.cv q))) (.cv x) p0051
  have p0053 := @g_pw1eq (.cv x) (syn_cuni (syn_cuni (.cv q)))
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.classEq (.cv x) (syn_cuni (syn_cuni (.cv q))))
      (.classEq (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))) p0052 p0053
  have p0055 := @g_pw1eq (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.classEq (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni (syn_cuni (.cv q)))))
      (.classEq (syn_cpw1 (syn_cpw1 (.cv x)))
        (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))))
      p0054 p0055
  have p0057 :=
    @g_imaeq2d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cpw1 (syn_cpw1 (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q)))))
      (syn_cfdglobalrowmap R A B) p0056
  have p0058 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (.cv x))))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))))
      p0040 p0057
  have p0060 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_wbr R (syn_cwe) A) p0004 p0060
  have p0075 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.cv x) (syn_cuni (syn_cuni (.cv q))) A p0052
  have p0076 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (.classMem (.cv x) A) (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0028 p0075
  have p0077 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_wbr R (syn_cwe) A) (.classMem (syn_cuni (syn_cuni (.cv q))) A) p0061 p0076
  have p0078 :=
    @g_fdglobalrowima A B (syn_cuni (syn_cuni (.cv q))) R dv_cache_0004 dv_cache_0008
      dv_cache_0005 dv_cache_0009 dv_cache_0006 dv_cache_0010
  have p0079 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (syn_cuni (syn_cuni (.cv q))) A))
      (.classEq (syn_cima (syn_cfdglobalrowmap R A B)
          (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      p0077 p0078
  have p0080 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
        (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cima (syn_cfdglobalrowmap R A B) (syn_cpw1 (syn_cpw1 (syn_cuni (syn_cuni (.cv q))))))
      (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))) p0058 p0079
  have p0081 :=
    @g_ex (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      p0080
  have p0082 :=
    @g_exp3a (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv x) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      p0081
  have p0083 :=
    @g_rexlimdv
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      x A dv_cache_0011 dv_cache_0012 p0082
  have p0084 :=
    @g_mpd (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_wrex x A (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q)))))
      p0003 p0083
  exact p0084

@[expose]
noncomputable def g_fdcolcodemapf (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdcolcodemapf_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdcolcodemapf_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdcolcodemapf_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
          (syn_cpw (syn_cpw (syn_cfdif R A B))))) :=
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
  have dv_cache_0007 : Disjoint (A).fv ((syn_cuni (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
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
  have dv_cache_0008 : Disjoint (B).fv ((syn_cuni (syn_cuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
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
  have dv_cache_0009 : Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
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
  have dv_cache_0010 : q ∉ ((syn_wbr R (syn_cwe) A)).fv :=
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
  have dv_cache_0011 : q ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
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
  have dv_cache_0012 : q ∉ ((syn_cpw (syn_cpw (syn_cfdif R A B)))).fv :=
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
  have dv_cache_0013 : q ∉ ((syn_cfdcolcodemap R A B)).fv :=
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
    @g_fdcolcodemapfn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdcolcodemapf_1
      hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3
  have p0002 :=
    @g_fdcolcodemapval A B R q dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003
      dv_cache_0005 dv_cache_0006 hyp_fdcolcodemapf_1 hyp_fdcolcodemapf_2
      hyp_fdcolcodemapf_3
  have p0003 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
  have p0004 := @g_vex q
  have p0005 := @g_uniex (.cv q) p0004
  have p0006 := @g_uniex (syn_cuni (.cv q)) p0005
  have p0007 :=
    @g_fdcodeelpwpw2 A B (syn_cuni (syn_cuni (.cv q))) R dv_cache_0001 dv_cache_0007
      dv_cache_0002 dv_cache_0008 dv_cache_0003 dv_cache_0009 hyp_fdcolcodemapf_1
      hyp_fdcolcodemapf_2 hyp_fdcolcodemapf_3 p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      p0003 p0007
  have p0009 :=
    @g_eqeltrd
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A))))
      (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
      (syn_cfdcode R A B (syn_cuni (syn_cuni (.cv q))))
      (syn_cpw (syn_cpw (syn_cfdif R A B))) p0002 p0008
  have p0010 :=
    @g_ex (syn_wbr R (syn_cwe) A) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      p0009
  have p0011 :=
    @g_ralrimiv (syn_wbr R (syn_cwe) A)
      (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      q (syn_cpw1 (syn_cpw1 A)) dv_cache_0010 p0010
  have p0012 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))
      (syn_wral q (syn_cpw1 (syn_cpw1 A)) (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
          (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      p0000 p0011
  have p0013 :=
    @g_fnfvrnss q (syn_cpw1 (syn_cpw1 A)) (syn_cpw (syn_cpw (syn_cfdif R A B)))
      (syn_cfdcolcodemap R A B) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0014 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))
        (syn_wral q (syn_cpw1 (syn_cpw1 A))
          (.classMem (syn_cfv (syn_cfdcolcodemap R A B) (.cv q))
            (syn_cpw (syn_cpw (syn_cfdif R A B))))))
      (syn_wss (syn_crn (syn_cfdcolcodemap R A B)) (syn_cpw (syn_cpw (syn_cfdif R A B))))
      p0012 p0013
  have p0015 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))
      (syn_wss (syn_crn (syn_cfdcolcodemap R A B)) (syn_cpw (syn_cpw (syn_cfdif R A B))))
      p0000 p0014
  have p0016 :=
    (Nominal.biimpRefl (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B)))))
  have p0017 :=
    @g_sylibr (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wfn (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A)))
        (syn_wss (syn_crn (syn_cfdcolcodemap R A B)) (syn_cpw (syn_cpw (syn_cfdif R A B)))))
      (syn_wf (syn_cfdcolcodemap R A B) (syn_cpw1 (syn_cpw1 A))
        (syn_cpw (syn_cpw (syn_cfdif R A B))))
      p0015 p0016
  exact p0017

@[expose]
noncomputable def g_fdcolcodearg (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
        (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
          (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))) :=
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
      ((syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
          (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))).fv :=
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
  have p0000 := @g_elpw12 c (.cv q) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (syn_wrex c A (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0000
  have p0002 :=
    @g_simpr (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
  have p0003 :=
    @g_unieqd
      (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (.cv q) (syn_csn (syn_csn (.cv c))) p0002
  have p0004 := @g_snex (.cv c)
  have p0005 := @g_unisn (syn_csn (.cv c)) p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (syn_csn (.cv c)))) (syn_csn (.cv c)))
      (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0005
  have p0007 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv c)))) (syn_csn (.cv c)) p0003
      p0006
  have p0008 :=
    @g_unieqd
      (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_cuni (.cv q)) (syn_csn (.cv c)) p0007
  have p0009 := @g_vex c
  have p0010 := @g_unisn (.cv c) p0009
  have p0011 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv c))) (.cv c))
      (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))) p0010
  have p0012 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_csn (.cv c))) (.cv c) p0008 p0011
  have p0013 :=
    @g_simpl (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
  have p0014 :=
    @g_eqeltrd
      (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_cuni (syn_cuni (.cv q))) (.cv c) A p0012 p0013
  have p0027 :=
    @g_sneqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_cuni (syn_cuni (.cv q))) (.cv c) p0012
  have p0028 :=
    @g_sneqd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (.cv c)) p0027
  have p0029 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (.cv c))) p0028
  have p0030 :=
    @g_eqtrd (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (.cv q) (syn_csn (syn_csn (.cv c)))
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) p0002 p0029
  have p0031 :=
    @g_jca (syn_wa (.classMem (.cv c) A) (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) A)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0014 p0030
  have p0032 :=
    @g_rexlimiva (.classEq (.cv q) (syn_csn (syn_csn (.cv c))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      c A dv_cache_0003 p0031
  have p0033 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 A)))
      (syn_wrex c A (.classEq (.cv q) (syn_csn (syn_csn (.cv c)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) A)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0001 p0032
  exact p0033


end NFChoice.DirectNominalPrf.WPPReplay

end
