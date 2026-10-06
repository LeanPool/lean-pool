/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block002

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part006. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnadjoinlem1`. -/
@[expose]
noncomputable def gNnadjoinlem1 (x : Var) (y : Var) (n : Var) (b : Var) (l : Var)
    (dv_b_l : b ≠ l) (_dv_b_n : b ≠ n) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_l_n : l ≠ n)
    (dv_l_x : l ≠ x) (dv_l_y : l ≠ y) (_dv_n_x : n ≠ x) (dv_n_y : n ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (.cab n (synWral l (.cv n)
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv n))))) (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ n } : Finset Var) ∪
        ({ b } : Finset Var) ∪
      ({ l } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
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
  have fresh_z_ne_n : z ≠ n := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_z : n ≠ z := Ne.symm fresh_z_ne_n
  have fresh_z_ne_b : z ≠ b := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_l : z ≠ l := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_l_ne_z : l ≠ z := Ne.symm fresh_z_ne_l
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_t_ne_b : t ≠ b := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_t_ne_l : t ≠ l := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_l_ne_t : l ≠ t := Ne.symm fresh_t_ne_l
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have dv_cache_0001 : t ∉ ((synCsn (.cv l))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_l,
          not_false_eq_true])
  have dv_cache_0002 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCin (synCssetk) (synCdif
              (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_l,
          fresh_t_ne_n, fresh_t_ne_y, fresh_t_ne_z, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0003 :
    t ∉
      ((synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y,
          fresh_t_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv l)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_l, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0007 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t,
          (Ne.symm dv_l_x), dv_x_y, fresh_x_ne_z, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0009 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv x)) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x,
          fresh_t_ne_l, fresh_t_ne_y, fresh_t_ne_z, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Wff.objMem y x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv l)).fv :=
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
          (Ne.symm dv_l_x), not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0015 :
    z ∉
      ((Class.cab x (synWrex b (.cv l)
            (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_l, fresh_z_ne_x,
          fresh_z_ne_b, fresh_z_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Class.cv n)).fv :=
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
          fresh_z_ne_n, not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((synCin (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0018 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0019 : t ∉ ((synCopk (synCsn (.cv l)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_l, fresh_t_ne_n, or_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((Class.cv t)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0021 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_l, fresh_z_ne_n, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((synCsn (synCsn (synCsn (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
          not_false_eq_true])
  have dv_cache_0023 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k (synCsik (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_l, fresh_t_ne_n, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 :
    t ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0025 : t ∉ ((synCopk (.cv z) (.cv l))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_l, or_false, not_false_eq_true])
  have dv_cache_0026 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_z, (Ne.symm dv_l_x), dv_x_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0028 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_z, fresh_t_ne_l, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 :
    t ∉
      ((synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0030 : t ∉ ((synCopk (synCsn (.cv x)) (.cv l))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_l, or_false, not_false_eq_true])
  have dv_cache_0031 : b ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_t, not_false_eq_true])
  have dv_cache_0032 :
    b ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_t, dv_b_x, dv_b_l, dv_b_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0033 : t ∉ ((synCsn (synCsn (synCsn (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
          not_false_eq_true])
  have dv_cache_0034 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
            (synCopk (synCsn (.cv x)) (.cv l))) (synCin (synCins2k (synCssetk)) (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_x, fresh_t_ne_l, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 : z ∉ ((synCun (.cv b) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_b, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0036 :
    t ∉
      ((synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0037 : t ∉ ((synCopk (.cv b) (.cv x))).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0038 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_b, fresh_z_ne_x, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0039 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_b, fresh_t_ne_x, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0040 :
    t ∉
      ((synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0041 : t ∉ ((Class.cv n)).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_n, not_false_eq_true])
  have dv_cache_0042 : l ∉ ((Class.cv t)).fv :=
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
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_l_ne_t, not_false_eq_true])
  have dv_cache_0043 :
    l ∉
      ((Wff.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
        have compact_fv_not_mem_empty : l ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_l_ne_t, dv_l_n,
          dv_l_y, fresh_l_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0044 :
    n ∉
      ((synCcompl (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1
                      (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synC1c)))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, dv_n_y, fresh_n_ne_z,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0045 : z ∉ ((Class.cv y)).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have p0000 := @gSnex (.cv l)
  have p0001 := @gOpkeq1 (.cv t) (synCsn (.cv l)) (.cv n)
  have p0002 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv l))) (synCopk (.cv t) (.cv n))
      (synCopk (synCsn (.cv l)) (.cv n))
      (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                  (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                  (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k (synCsik (synCcompl
                    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      p0001
  have p0003 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
              (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
              (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      t (synCsn (.cv l)) dv_cache_0001 dv_cache_0002 p0000 p0002
  have p0004 :=
    @gElin (synCopk (synCsn (.cv l)) (.cv n)) (synCssetk)
      (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k (synCsik (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
  have p0005 := @gVex l
  have p0006 := @gVex n
  have p0007 := @gElssetk (.cv l) (.cv n) p0005 p0006
  have p0008 :=
    @gEldif (synCopk (synCsn (.cv l)) (.cv n))
      (synCxpk (synCcompl (synCpw1 (synCimak
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
              (synC1c)))) (synCvv))
      (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))
  have p0009 :=
    @gElcompl (synCsn (.cv l))
      (synCpw1 (synCimak
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
          (synC1c)))
      p0000
  have p0010 :=
    @gElimak t
      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
      (synC1c) (.cv l) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0005
  have p0011 := @gEl1c x (.cv t) dv_cache_0006
  have p0012 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex x (.classEq (.cv t) (synCsn (.cv x))))
      (.classMem (synCopk (.cv t) (.cv l))
        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))
      p0011
  have p0013 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCopk (.cv t) (.cv l))
        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))
      x dv_cache_0007
  have p0014 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (.cv x))))
        (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv l))
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))))
      p0012 p0013
  have p0015 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv l))
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))))
      t p0014
  have p0016 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))))
  have p0017 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))
      x t
  have p0018 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv l))
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv l))
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv l))
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))))
      p0015 p0016 p0017
  have p0019 := @gSnex (.cv x)
  have p0020 := @gOpkeq1 (.cv t) (synCsn (.cv x)) (.cv l)
  have p0021 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv x))) (synCopk (.cv t) (.cv l))
      (synCopk (synCsn (.cv x)) (.cv l))
      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)) p0020
  have p0022 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv l))
        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv l))
        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))
      t (synCsn (.cv x)) dv_cache_0008 dv_cache_0009 p0019 p0021
  have p0023 :=
    @gElin (synCopk (synCsn (.cv x)) (.cv l))
      (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)
  have p0024 :=
    @gOpkelxpk (synCsn (.cv x)) (.cv l) (synCpw1 (.cab z (.objMem y z))) (synCvv)
      p0019 p0005
  have p0025 :=
    @gMpbiran2
      (.classMem (synCopk (synCsn (.cv x)) (.cv l))
        (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)))
      (.classMem (synCsn (.cv x)) (synCpw1 (.cab z (.objMem y z))))
      (.classMem (.cv l) (synCvv)) p0005 p0024
  have p0026 := @gSnelpw1 (.cv x) (.cab z (.objMem y z))
  have p0027 := @gVex x
  have p0028 := @gElequ2 z x y
  have p0029_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv z) (.cv x)) (synWb (.objMem y z) (.objMem y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0028
  have p0029 :=
    @gElab (.objMem y z) (.objMem y x) z (.cv x) dv_cache_0010 dv_cache_0011 p0027
      p0029_e01_recanon
  have p0030 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv x)) (.cv l))
        (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)))
      (.classMem (synCsn (.cv x)) (synCpw1 (.cab z (.objMem y z))))
      (.classMem (.cv x) (.cab z (.objMem y z))) (.objMem y x) p0025 p0026 p0029
  have p0031 := @gElssetk (.cv x) (.cv l) p0027 p0005
  have p0032_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv l)) (synCssetk)) (.objMem x l)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (.cv x)) (.cv l))
        (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)))
      (.objMem y x) (.classMem (synCopk (synCsn (.cv x)) (.cv l)) (synCssetk))
      (.objMem x l) p0030 p0032_e01_recanon
  have p0033 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv l))
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv l))
        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))
      (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv l))
          (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)))
        (.classMem (synCopk (synCsn (.cv x)) (.cv l)) (synCssetk)))
      (synWa (.objMem y x) (.objMem x l)) p0022 p0023 p0032
  have p0034 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv l))
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk)))))
      (synWa (.objMem y x) (.objMem x l)) x p0033
  have p0035 :=
    @gN3bitri
      (.classMem (.cv l) (synCimak
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
          (synC1c)))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv l))
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv l))
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))))))
      (synWex x (synWa (.objMem y x) (.objMem x l))) p0010 p0018 p0034
  have p0036 :=
    @gSnelpw1 (.cv l)
      (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
        (synC1c))
  have p0037 := @gEluni x (.cv y) (.cv l) dv_cache_0012 dv_cache_0013
  have p0038_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv y) (synCuni (.cv l)))
        (synWex x (synWa (.objMem y x) (.objMem x l)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @gN3bitr4i
      (.classMem (.cv l) (synCimak
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
          (synC1c)))
      (synWex x (synWa (.objMem y x) (.objMem x l)))
      (.classMem (synCsn (.cv l)) (synCpw1 (synCimak
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
            (synC1c))))
      (.classMem (.cv y) (synCuni (.cv l))) p0035 p0036 p0038_e02_recanon
  have p0039 :=
    @gXchbinx
      (.classMem (synCsn (.cv l)) (synCcompl (synCpw1 (synCimak
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
              (synC1c)))))
      (.classMem (synCsn (.cv l)) (synCpw1 (synCimak
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
            (synC1c))))
      (.classMem (.cv y) (synCuni (.cv l))) p0009 p0038
  have p0040 :=
    @gOpkelxpk (synCsn (.cv l)) (.cv n)
      (synCcompl (synCpw1 (synCimak
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
            (synC1c))))
      (synCvv) p0000 p0006
  have p0041 :=
    @gMpbiran2
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCxpk (synCcompl (synCpw1 (synCimak
                (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                (synC1c)))) (synCvv)))
      (.classMem (synCsn (.cv l)) (synCcompl (synCpw1 (synCimak
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
              (synC1c)))))
      (.classMem (.cv n) (synCvv)) p0006 p0040
  have p0042 := @gVex y
  have p0043 := @gElcompl (.cv y) (synCuni (.cv l)) p0042
  have p0044 :=
    @gN3bitr4i
      (.classMem (synCsn (.cv l)) (synCcompl (synCpw1 (synCimak
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
              (synC1c)))))
      (.neg (.classMem (.cv y) (synCuni (.cv l))))
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCxpk (synCcompl (synCpw1 (synCimak
                (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                (synC1c)))) (synCvv)))
      (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) p0039 p0041 p0043
  have p0045 :=
    @gEqabb (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) x
      (.cv z) dv_cache_0014
  have p0046_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv z) (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
        (.all x (synWb (.objMem x z) (synWrex b (.cv l)
              (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCun, synCnin, synWnan,
          synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @gAnbi1i
      (.classEq (.cv z) (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (.all x (synWb (.objMem x z)
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (.objMem z n) p0046_e00_recanon
  have p0047 :=
    @gExbii
      (synWa (.classEq (.cv z) (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
        (.objMem z n))
      (synWa (.all x (synWb (.objMem x z)
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
        (.objMem z n))
      z p0046
  have p0048 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV z
      (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.cv n) dv_cache_0015 dv_cache_0016)
  have p0049 := @gOpkex (synCsn (.cv l)) (.cv n)
  have p0050 :=
    @gElimak t
      (synCin (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                    (synCun (synCssetk)
                                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
        (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn (.cv l)) (.cv n)) dv_cache_0017
      dv_cache_0018 dv_cache_0019 p0049
  have p0051 := @gElpw121c z (.cv t) dv_cache_0020
  have p0052 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
            (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      p0051
  have p0053 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
            (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      z dv_cache_0021
  have p0054 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      p0052 p0053
  have p0055 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      t p0054
  have p0056 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))))))
  have p0057 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      z t
  have p0058 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
                (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
                (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))))))
      p0055 p0056 p0057
  have p0059 := @gSnex (synCsn (synCsn (.cv z)))
  have p0060 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv z))))
      (synCopk (synCsn (.cv l)) (.cv n))
  have p0061 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n)))
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn (.cv l)) (.cv n)))
      (synCin (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                    (synCun (synCssetk)
                                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
        (synCins2k (synCssetk)))
      p0060
  have p0062 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
            (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k (synCsik (synCcompl
                (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv z)))) dv_cache_0022 dv_cache_0023 p0059 p0061
  have p0063 :=
    @gElin
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn (.cv l)) (.cv n)))
      (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCssetk)
                                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
      (synCins2k (synCssetk))
  have p0064 := @gSnex (.cv z)
  have p0065 :=
    @gOtkelins3k (synCsn (.cv z)) (synCsn (.cv l)) (.cv n)
      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
      p0064 p0000 p0006
  have p0066 := @gVex z
  have p0067 :=
    @gOpksnelsik (.cv z) (.cv l)
      (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))
      p0066 p0005
  have p0068 := @gOpkex (.cv z) (.cv l)
  have p0069 :=
    @gElimak t
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv z) (.cv l)) dv_cache_0024
      dv_cache_0018 dv_cache_0025 p0068
  have p0070 := @gElpw121c x (.cv t) dv_cache_0006
  have p0071 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      p0070
  have p0072 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      x dv_cache_0026
  have p0073 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0071 p0072
  have p0074 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      t p0073
  have p0075 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))))))
  have p0076 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      x t
  have p0077 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                  (synCun (synCssetk)
                                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                  (synCun (synCssetk)
                                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0074 p0075 p0076
  have p0078 := @gSnex (synCsn (synCsn (.cv x)))
  have p0079 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l))
  have p0080 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
      (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      p0079
  have p0081 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      t (synCsn (synCsn (synCsn (.cv x)))) dv_cache_0027 dv_cache_0028 p0078 p0080
  have p0082 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
      (synCins3k (synCssetk))
      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
  have p0083 :=
    @gOtkelins3k (synCsn (.cv x)) (.cv z) (.cv l) (synCssetk) p0019 p0066 p0005
  have p0084 := @gElssetk (.cv x) (.cv z) p0027 p0066
  have p0085_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCssetk)) (.objMem x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0084
  have p0085 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCssetk)) (.objMem x z) p0083
      p0085_e01_recanon
  have p0086 := @gOpkex (synCsn (.cv x)) (.cv l)
  have p0087 :=
    @gElimak t
      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn (.cv x)) (.cv l)) dv_cache_0029
      dv_cache_0018 dv_cache_0030 p0086
  have p0088 := @gElpw121c b (.cv t) dv_cache_0031
  have p0089 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0088
  have p0090 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      b dv_cache_0032
  have p0091 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWa (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex b (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      p0089 p0090
  have p0092 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex b (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      t p0091
  have p0093 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))))))
  have p0094 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      b t
  have p0095 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex t (synWex b (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex b (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      p0092 p0093 p0094
  have p0096 := @gSnex (synCsn (synCsn (.cv b)))
  have p0097 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv b))))
      (synCopk (synCsn (.cv x)) (.cv l))
  have p0098 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
      (synCopk (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv x)) (.cv l)))
      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))))))
      p0097
  have p0099 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv x)) (.cv l))) (synCin (synCins2k (synCssetk)) (synCins3k
            (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      t (synCsn (synCsn (synCsn (.cv b)))) dv_cache_0033 dv_cache_0034 p0096 p0098
  have p0100 :=
    @gElin
      (synCopk (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv x)) (.cv l)))
      (synCins2k (synCssetk))
      (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCssetk)
                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))))
  have p0101 := @gSnex (.cv b)
  have p0102 :=
    @gOtkelins2k (synCsn (.cv b)) (synCsn (.cv x)) (.cv l) (synCssetk) p0101 p0019
      p0005
  have p0103 := @gVex b
  have p0104 := @gElssetk (.cv b) (.cv l) p0103 p0005
  have p0105_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv l)) (synCssetk)) (.objMem b l)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0104
  have p0105 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv x)) (.cv l))) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv b)) (.cv l)) (synCssetk)) (.objMem b l) p0102
      p0105_e01_recanon
  have p0106 :=
    @gOtkelins3k (synCsn (.cv b)) (synCsn (.cv x)) (.cv l)
      (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0101 p0019 p0005
  have p0107 :=
    @gOpksnelsik (.cv b) (.cv x)
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0103 p0027
  have p0108 :=
    @gAlex (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y)))))
      z
  have p0109 :=
    @gDfcleq z (.cv x) (synCun (.cv b) (synCsn (.cv y))) dv_cache_0010 dv_cache_0035
  have p0110 := @gOpkex (.cv b) (.cv x)
  have p0111 :=
    @gElcompl (synCopk (.cv b) (.cv x))
      (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c))))
      p0110
  have p0112 :=
    @gElimak t
      (synCsymdif (synCins2k (synCssetk)) (synCins3k
          (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv b) (.cv x)) dv_cache_0036
      dv_cache_0018 dv_cache_0037 p0110
  have p0113 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
      (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      p0051
  have p0114 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      z dv_cache_0038
  have p0115 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))))
      p0113 p0114
  have p0116 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))))
      t p0115
  have p0117 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))))
  have p0118 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))
      z t
  have p0119 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))))
      p0116 p0117 p0118
  have p0120 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x))
  have p0121 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
      (synCsymdif (synCins2k (synCssetk)) (synCins3k
          (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
      p0120
  have p0122 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      t (synCsn (synCsn (synCsn (.cv z)))) dv_cache_0022 dv_cache_0039 p0059 p0121
  have p0123 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
      (synCins2k (synCssetk))
      (synCins3k (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))
  have p0124 :=
    @gOtkelins2k (synCsn (.cv z)) (.cv b) (.cv x) (synCssetk) p0064 p0103 p0027
  have p0125 := @gElssetk (.cv z) (.cv x) p0066 p0027
  have p0126_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCssetk)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0125
  have p0126 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCssetk)) (.objMem z x) p0124
      p0126_e01_recanon
  have p0127 :=
    @gOtkelins3k (synCsn (.cv z)) (.cv b) (.cv x)
      (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))) p0064 p0103
      p0027
  have p0128 := @gElssetk (.cv z) (.cv b) p0066 p0103
  have p0129 := @gElsnc (synCsn (.cv z)) (synCsn (.cv y)) p0064
  have p0130 := @gSneqb (.cv z) (.cv y) p0066
  have p0131_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv z)) (synCsn (.cv y))) (.objEq z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0130
  have p0131 :=
    @gBitri (.classMem (synCsn (.cv z)) (synCsn (synCsn (.cv y))))
      (.classEq (synCsn (.cv z)) (synCsn (.cv y))) (.objEq z y) p0129 p0131_e01_recanon
  have p0132 :=
    @gOpkelxpk (synCsn (.cv z)) (.cv b) (synCsn (synCsn (.cv y))) (synCvv) p0064
      p0103
  have p0133 :=
    @gMpbiran2
      (.classMem (synCopk (synCsn (.cv z)) (.cv b))
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))
      (.classMem (synCsn (.cv z)) (synCsn (synCsn (.cv y))))
      (.classMem (.cv b) (synCvv)) p0103 p0132
  have p0134 := @gElsnc (.cv z) (.cv y) p0066
  have p0135_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv z) (synCsn (.cv y))) (.objEq z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0134
  have p0135 :=
    @gN3bitr4i (.classMem (synCsn (.cv z)) (synCsn (synCsn (.cv y)))) (.objEq z y)
      (.classMem (synCopk (synCsn (.cv z)) (.cv b))
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))
      (.classMem (.cv z) (synCsn (.cv y))) p0131 p0133 p0135_e02_recanon
  have p0136_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv b)) (synCssetk)) (.objMem z b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0128
  have p0136 :=
    @gOrbi12i (.classMem (synCopk (synCsn (.cv z)) (.cv b)) (synCssetk)) (.objMem z b)
      (.classMem (synCopk (synCsn (.cv z)) (.cv b))
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))
      (.classMem (.cv z) (synCsn (.cv y))) p0136_e00_recanon p0135
  have p0137 :=
    @gElun (synCopk (synCsn (.cv z)) (.cv b)) (synCssetk)
      (synCxpk (synCsn (synCsn (.cv y))) (synCvv))
  have p0138 := @gElun (.cv z) (.cv b) (synCsn (.cv y))
  have p0139_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))
        (synWo (.objMem z b) (.classMem (.cv z) (synCsn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCsn synWo
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0138
  have p0139 :=
    @gN3bitr4i
      (synWo (.classMem (synCopk (synCsn (.cv z)) (.cv b)) (synCssetk))
        (.classMem (synCopk (synCsn (.cv z)) (.cv b))
          (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))
      (synWo (.objMem z b) (.classMem (.cv z) (synCsn (.cv y))))
      (.classMem (synCopk (synCsn (.cv z)) (.cv b))
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))
      (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y)))) p0136 p0137
      p0139_e02_recanon
  have p0140 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCins3k (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
      (.classMem (synCopk (synCsn (.cv z)) (.cv b))
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))
      (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y)))) p0127 p0139
  have p0141 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCins2k (synCssetk)))
      (.objMem z x)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCins3k (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
      (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y)))) p0126 p0140
  have p0142 :=
    @gXchbinx
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      (synWb (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
          (synCins2k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
          (synCins3k (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))) p0123
      p0141
  have p0143 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv b) (.cv x)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))
      (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))))
      p0122 p0142
  have p0144 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))))))
      (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))))
      z p0143
  have p0145 :=
    @gN3bitri
      (.classMem (synCopk (.cv b) (.cv x)) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv b) (.cv x)))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))))))
      (synWex z (.neg
          (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y)))))))
      p0112 p0119 p0144
  have p0146 :=
    @gXchbinx
      (.classMem (synCopk (.cv b) (.cv x)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCopk (.cv b) (.cv x)) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex z (.neg
          (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y)))))))
      p0111 p0145
  have p0147_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) (.all z
          (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0109
  have p0147 :=
    @gN3bitr4ri
      (.all z (synWb (.objMem z x) (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))))
      (.neg (synWex z (.neg (synWb (.objMem z x)
              (.classMem (.cv z) (synCun (.cv b) (synCsn (.cv y))))))))
      (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))
      (.classMem (synCopk (.cv b) (.cv x)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0108 p0147_e01_recanon p0146
  have p0148 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv x)) (.cv l))) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (.cv b)) (synCsn (.cv x))) (synCsik (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (.cv b) (.cv x)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) p0106 p0107 p0147
  have p0149 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv x)) (.cv l))) (synCins2k (synCssetk)))
      (.objMem b l)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv x)) (.cv l))) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))) p0105 p0148
  have p0150 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv x)) (.cv l))) (synCin (synCins2k (synCssetk)) (synCins3k
            (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
            (synCopk (synCsn (.cv x)) (.cv l))) (synCins2k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                    (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.objMem b l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) p0099
      p0100 p0149
  have p0151 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWa (.objMem b l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) b
      p0150
  have p0152 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv x)) (.cv l)) (synCimak
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex b (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv l)))
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWex b (synWa (.objMem b l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      p0087 p0095 p0151
  have p0153 :=
    @gOtkelins2k (synCsn (.cv x)) (.cv z) (.cv l)
      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))
      p0019 p0066 p0005
  have p0154 :=
    (Nominal.biimpRefl
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
  have p0155_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))
        (synWex b (synWa (.objMem b l)
            (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCun, synCnin, synWnan,
          synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0154
  have p0155 :=
    @gN3bitr4i
      (.classMem (synCopk (synCsn (.cv x)) (.cv l)) (synCimak
          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
      (synWex b (synWa (.objMem b l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) p0152
      p0153 p0155_e02_recanon
  have p0156 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCins3k (synCssetk)))
      (.objMem x z)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))) p0085
      p0155
  have p0157 :=
    @gXchbinx
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWb (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
          (synCins3k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWb (.objMem x z)
        (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      p0082 p0156
  have p0158 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv z) (.cv l)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      (.neg (synWb (.objMem x z)
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0081 p0157
  have p0159 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.neg (synWb (.objMem x z)
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      x p0158
  have p0160 :=
    @gN3bitri
      (.classMem (synCopk (.cv z) (.cv l)) (synCimak (synCsymdif (synCins3k (synCssetk))
            (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv z) (.cv l)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                  (synCun (synCssetk)
                                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex x (.neg (synWb (.objMem x z)
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      p0069 p0077 p0159
  have p0161 :=
    @gNotbii
      (.classMem (synCopk (.cv z) (.cv l)) (synCimak (synCsymdif (synCins3k (synCssetk))
            (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.neg (synWb (.objMem x z)
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))))
      p0160
  have p0162 :=
    @gElcompl (synCopk (.cv z) (.cv l))
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0068
  have p0163 :=
    @gAlex
      (synWb (.objMem x z)
        (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
      x
  have p0164 :=
    @gN3bitr4i
      (.neg (.classMem (synCopk (.cv z) (.cv l)) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
      (.neg (synWex x (.neg (synWb (.objMem x z) (synWrex b (.cv l)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))))
      (.classMem (synCopk (.cv z) (.cv l)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
      (.all x (synWb (.objMem x z)
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0161 p0162 p0163
  have p0165 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv l)) (.cv n))) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                    (synCun (synCssetk)
                                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv l))) (synCsik (synCcompl (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                  (synCun (synCssetk)
                                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (.cv z) (.cv l)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
      (.all x (synWb (.objMem x z)
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      p0065 p0067 p0164
  have p0166 :=
    @gOtkelins2k (synCsn (.cv z)) (synCsn (.cv l)) (.cv n) (synCssetk) p0064 p0000
      p0006
  have p0167 := @gElssetk (.cv z) (.cv n) p0066 p0006
  have p0168_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv n)) (synCssetk)) (.objMem z n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0167
  have p0168 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv l)) (.cv n))) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv n)) (synCssetk)) (.objMem z n) p0166
      p0168_e01_recanon
  have p0169 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv l)) (.cv n))) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                    (synCun (synCssetk)
                                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))))
      (.all x (synWb (.objMem x z)
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv l)) (.cv n))) (synCins2k (synCssetk)))
      (.objMem z n) p0165 p0168
  have p0170 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k (synCsik (synCcompl
                (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (synCsn (.cv l)) (.cv n))) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))))
        (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (synCsn (.cv l)) (.cv n))) (synCins2k (synCssetk))))
      (synWa (.all x (synWb (.objMem x z)
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
        (.objMem z n))
      p0062 p0063 p0169
  have p0171 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
              (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk))))))
      (synWa (.all x (synWb (.objMem x z)
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))))
        (.objMem z n))
      z p0170
  have p0172 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCimak (synCin (synCins3k (synCsik
                (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                        (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin (synCins3k
              (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk)))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv l)) (.cv n))) (synCin
                (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))))))
      (synWex z (synWa (.all x (synWb (.objMem x z) (synWrex b (.cv l)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) (.objMem z n)))
      p0050 p0058 p0171
  have p0173_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)) (synWex z (synWa (.classEq (.cv z) (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) (.objMem z n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCun, synCnin, synWnan,
          synCcompl, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0173 :=
    @gN3bitr4ri
      (synWex z (synWa (.classEq (.cv z) (.cab x (synWrex b (.cv l)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) (.objMem z n)))
      (synWex z (synWa (.all x (synWb (.objMem x z) (synWrex b (.cv l)
                (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))) (.objMem z n)))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCimak (synCin (synCins3k (synCsik
                (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                        (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
      p0047 p0173_e01_recanon p0172
  have p0174 :=
    @gNotbii
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCimak (synCin (synCins3k (synCsik
                (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                        (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
      p0173
  have p0175 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCxpk (synCcompl (synCpw1 (synCimak
                (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                (synC1c)))) (synCvv)))
      (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
      (.neg (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCimak (synCin (synCins3k
                (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)))
      p0044 p0174
  have p0176 :=
    @gAnnim (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
      (.classMem (.cab x
          (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))
  have p0177 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCdif (synCxpk (synCcompl (synCpw1
                (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                    (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synWa (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCxpk (synCcompl (synCpw1
                (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                    (synCssetk)) (synC1c)))) (synCvv))) (.neg
          (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.neg (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      p0008 p0175 p0176
  have p0178_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCssetk)) (.objMem l n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0178 :=
    @gAnbi12i (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCssetk)) (.objMem l n)
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCdif (synCxpk (synCcompl (synCpw1
                (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                    (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
              (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      p0178_e00_recanon p0177
  have p0179 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv l)))
          (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                  (synCcompl (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
              (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCssetk))
        (.classMem (synCopk (synCsn (.cv l)) (.cv n)) (synCdif (synCxpk (synCcompl
                (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.objMem l n) (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n)))))
      p0003 p0004 p0178
  have p0180 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv l)))
          (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                  (synCcompl (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.objMem l n) (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n)))))
      l p0179
  have p0181 :=
    @gElimak t
      (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                  (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                  (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k (synCsik (synCcompl
                    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synC1c) (.cv n) dv_cache_0040 dv_cache_0004 dv_cache_0041 p0006
  have p0182 := @gEl1c l (.cv t) dv_cache_0042
  have p0183 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex l (.classEq (.cv t) (synCsn (.cv l))))
      (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
              (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0182
  have p0184 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv l)))
      (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
              (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      l dv_cache_0043
  have p0185 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv n))
          (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (synWex l (.classEq (.cv t) (synCsn (.cv l))))
        (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex l (synWa (.classEq (.cv t) (synCsn (.cv l)))
          (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                  (synCcompl (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0183 p0184
  have p0186 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv n))
          (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex l (synWa (.classEq (.cv t) (synCsn (.cv l)))
          (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                  (synCcompl (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      t p0185
  have p0187 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv n))
          (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))))
  have p0188 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv l))) (.classMem (synCopk (.cv t) (.cv n))
          (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      l t
  have p0189 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv n))
            (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex t (synWex l (synWa (.classEq (.cv t) (synCsn (.cv l)))
            (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                    (synCcompl (synCpw1 (synCimak
                          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                            (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin
                      (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk)
            (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex l (synWex t (synWa (.classEq (.cv t) (synCsn (.cv l)))
            (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                    (synCcompl (synCpw1 (synCimak
                          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                            (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin
                      (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0186 p0187 p0188
  have p0190 :=
    @gBitri
      (.classMem (.cv n) (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl
                  (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synC1c)))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk)
            (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex l (synWex t (synWa (.classEq (.cv t) (synCsn (.cv l)))
            (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                    (synCcompl (synCpw1 (synCimak
                          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                            (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin
                      (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0181 p0189
  have p0191 :=
    (Nominal.biimpRefl (synWrex l (.cv n) (.neg
          (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
              (.cv n))))))
  have p0192_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex l (.cv n) (.neg
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv n))))) (synWex l (synWa (.objMem l n) (.neg
              (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                    (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                  (.cv n))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCcompl, synCnin, synWnan,
          synCuni]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0191
  have p0192 :=
    @gN3bitr4i
      (synWex l (synWex t (synWa (.classEq (.cv t) (synCsn (.cv l)))
            (.classMem (synCopk (.cv t) (.cv n)) (synCin (synCssetk) (synCdif (synCxpk
                    (synCcompl (synCpw1 (synCimak
                          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                            (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin
                      (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex l (synWa (.objMem l n) (.neg
            (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
                  (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
                (.cv n))))))
      (.classMem (.cv n) (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl
                  (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synC1c)))
      (synWrex l (.cv n) (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n)))))
      p0180 p0190 p0192_e02_recanon
  have p0193 :=
    @gNotbii
      (.classMem (.cv n) (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl
                  (synCpw1 (synCimak
                      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synC1c)))
      (synWrex l (.cv n) (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n)))))
      p0192
  have p0194 :=
    @gElcompl (.cv n)
      (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synC1c))
      p0006
  have p0195 :=
    @gDfral2
      (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem (.cab x
            (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
          (.cv n)))
      l (.cv n)
  have p0196 :=
    @gN3bitr4i
      (.neg (.classMem (.cv n) (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl
                    (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synC1c))))
      (.neg (synWrex l (.cv n) (.neg (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
              (.classMem (.cab x (synWrex b (.cv l)
                    (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n))))))
      (.classMem (.cv n) (synCcompl (synCimak (synCin (synCssetk) (synCdif (synCxpk
                  (synCcompl (synCpw1 (synCimak
                        (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                          (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synC1c))))
      (synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      p0193 p0194 p0195
  have p0197 :=
    @gEqabi
      (synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l)))) (.classMem
            (.cab x (synWrex b (.cv l) (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y))))))
            (.cv n))))
      n
      (synCcompl (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1
                    (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synC1c)))
      dv_cache_0044 p0196
  have p0198 := @gSsetkex
  have p0199 := @gSetswithex z (.cv y) dv_cache_0045
  have p0200_e00_recanon : Nominal.NPrf (.classMem (.cab z (.objMem y z)) (synCvv)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classMem
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _)
      p0199
  have p0200 := @gPw1ex (.cab z (.objMem y z)) p0200_e00_recanon
  have p0201 := @gVvex
  have p0202 := @gXpkex (synCpw1 (.cab z (.objMem y z))) (synCvv) p0200 p0201
  have p0204 :=
    @gInex (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk) p0202
      p0198
  have p0205 := @gN1cex
  have p0206 :=
    @gImakex
      (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
      (synC1c) p0204 p0205
  have p0207 :=
    @gPw1ex
      (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
        (synC1c))
      p0206
  have p0208 :=
    @gComplex
      (synCpw1 (synCimak
          (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
          (synC1c)))
      p0207
  have p0210 :=
    @gXpkex
      (synCcompl (synCpw1 (synCimak
            (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
            (synC1c))))
      (synCvv) p0208 p0201
  have p0212 := @gIns3kex (synCssetk) p0198
  have p0214 := @gIns2kex (synCssetk) p0198
  have p0216 := @gSnex (synCsn (.cv y))
  have p0218 := @gXpkex (synCsn (synCsn (.cv y))) (synCvv) p0216 p0201
  have p0219 :=
    @gUnex (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)) p0198 p0218
  have p0220 :=
    @gIns3kex (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))
      p0219
  have p0221 :=
    @gSymdifex (synCins2k (synCssetk))
      (synCins3k (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))
      p0214 p0220
  have p0223 := @gPw1ex (synC1c) p0205
  have p0224 := @gPw1ex (synCpw1 (synC1c)) p0223
  have p0225 :=
    @gImakex
      (synCsymdif (synCins2k (synCssetk)) (synCins3k
          (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
      (synCpw1 (synCpw1 (synC1c))) p0221 p0224
  have p0226 :=
    @gComplex
      (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
            (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c))))
      p0225
  have p0227 :=
    @gSikex
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
              (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0226
  have p0228 :=
    @gIns3kex
      (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0227
  have p0229 :=
    @gInex (synCins2k (synCssetk))
      (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCssetk)
                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0214 p0228
  have p0230 :=
    @gImakex
      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synCpw1 (synCpw1 (synC1c))) p0229 p0224
  have p0231 :=
    @gIns2kex
      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))
      p0230
  have p0232 :=
    @gSymdifex (synCins3k (synCssetk))
      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCun (synCssetk)
                          (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
      p0212 p0231
  have p0233 :=
    @gImakex
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                            (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synC1c))) p0232 p0224
  have p0234 :=
    @gComplex
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
                              (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0233
  have p0235 :=
    @gSikex
      (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCssetk)
                                (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))
      p0234
  have p0236 :=
    @gIns3kex
      (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCssetk)
                                  (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
      p0235
  have p0237 :=
    @gInex
      (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCssetk)
                                    (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
      (synCins2k (synCssetk)) p0236 p0214
  have p0238 :=
    @gImakex
      (synCin (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                    (synCun (synCssetk)
                                      (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
        (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0237 p0224
  have p0239 :=
    @gDifex
      (synCxpk (synCcompl (synCpw1 (synCimak
              (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
              (synC1c)))) (synCvv))
      (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                        (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCssetk)
                                        (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))
      p0210 p0238
  have p0240 :=
    @gInex (synCssetk)
      (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k (synCsik (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                          (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))))
            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
      p0198 p0239
  have p0242 :=
    @gImakex
      (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                  (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv)) (synCssetk))
                  (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k (synCsik (synCcompl
                    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synC1c) p0240 p0205
  have p0243 :=
    @gComplex
      (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1 (synCimak
                    (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                      (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCssetk) (synCxpk (synCsn (synCsn (.cv y))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synC1c))
      p0242
  have p0244 :=
    @gEqeltrri
      (synCcompl (synCimak (synCin (synCssetk) (synCdif (synCxpk (synCcompl (synCpw1
                    (synCimak (synCin (synCxpk (synCpw1 (.cab z (.objMem y z))) (synCvv))
                        (synCssetk)) (synC1c)))) (synCvv)) (synCimak (synCin (synCins3k
                    (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCimak (synCin (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCssetk)
        (synCxpk (synCsn (synCsn (.cv y))) (synCvv))))) (synCpw1 (synCpw1 (synC1c))))))))
                                (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synC1c)))
      (.cab n (synWral l (.cv n) (.imp (.classMem (.cv y) (synCcompl (synCuni (.cv l))))
            (.classMem (.cab x (synWrex b (.cv l)
                  (.classEq (.cv x) (synCun (.cv b) (synCsn (.cv y)))))) (.cv n)))))
      (synCvv) p0197 p0243
  exact p0244


end NFChoice.DirectNominalPrf.WPPReplay
