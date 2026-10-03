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

@[expose]
noncomputable def g_nnadjoinlem1 (x : Var) (y : Var) (n : Var) (b : Var) (l : Var)
    (dv_b_l : b ≠ l) (_dv_b_n : b ≠ n) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_l_n : l ≠ n)
    (dv_l_x : l ≠ x) (dv_l_y : l ≠ y) (_dv_n_x : n ≠ x) (dv_n_y : n ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (.cab n (syn_wral l (.cv n)
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv n))))) (syn_cvv)) :=
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
  have dv_cache_0001 : t ∉ ((syn_csn (.cv l))).fv := by
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
      ((Wff.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif
              (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
      ((syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))).fv :=
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
  have dv_cache_0004 : t ∉ ((syn_c1c)).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))).fv :=
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
  have dv_cache_0008 : t ∉ ((syn_csn (.cv x))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))).fv :=
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
      ((Class.cab x (syn_wrex b (.cv l)
            (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))).fv :=
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
      ((syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk)))).fv :=
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
  have dv_cache_0018 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
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
  have dv_cache_0019 : t ∉ ((syn_copk (syn_csn (.cv l)) (.cv n))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))))).fv :=
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
  have dv_cache_0022 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv z))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
            (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))))).fv :=
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
      ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
  have dv_cache_0025 : t ∉ ((syn_copk (.cv z) (.cv l))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
  have dv_cache_0027 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
      ((syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
  have dv_cache_0030 : t ∉ ((syn_copk (syn_csn (.cv x)) (.cv l))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
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
  have dv_cache_0033 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
            (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
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
  have dv_cache_0035 : z ∉ ((syn_cun (.cv b) (syn_csn (.cv y)))).fv :=
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
      ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))).fv :=
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
  have dv_cache_0037 : t ∉ ((syn_copk (.cv b) (.cv x))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))).fv :=
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
      ((syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
      ((syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1
                      (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c)))).fv :=
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
  have p0000 := @g_snex (.cv l)
  have p0001 := @g_opkeq1 (.cv t) (syn_csn (.cv l)) (.cv n)
  have p0002 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv l))) (syn_copk (.cv t) (.cv n))
      (syn_copk (syn_csn (.cv l)) (.cv n))
      (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                  (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                  (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0001
  have p0003 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
              (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
              (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      t (syn_csn (.cv l)) dv_cache_0001 dv_cache_0002 p0000 p0002
  have p0004 :=
    @g_elin (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cssetk)
      (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0005 := @g_vex l
  have p0006 := @g_vex n
  have p0007 := @g_elssetk (.cv l) (.cv n) p0005 p0006
  have p0008 :=
    @g_eldif (syn_copk (syn_csn (.cv l)) (.cv n))
      (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
              (syn_c1c)))) (syn_cvv))
      (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0009 :=
    @g_elcompl (syn_csn (.cv l))
      (syn_cpw1 (syn_cimak
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
          (syn_c1c)))
      p0000
  have p0010 :=
    @g_elimak t
      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
      (syn_c1c) (.cv l) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0005
  have p0011 := @g_el1c x (.cv t) dv_cache_0006
  have p0012 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
      (.classMem (syn_copk (.cv t) (.cv l))
        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))
      p0011
  have p0013 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_copk (.cv t) (.cv l))
        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))
      x dv_cache_0007
  have p0014 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
        (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv l))
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))))
      p0012 p0013
  have p0015 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv l))
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))))
      t p0014
  have p0016 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))))
  have p0017 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))
      x t
  have p0018 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv l))
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv l))
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv l))
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))))
      p0015 p0016 p0017
  have p0019 := @g_snex (.cv x)
  have p0020 := @g_opkeq1 (.cv t) (syn_csn (.cv x)) (.cv l)
  have p0021 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) (.cv l))
      (syn_copk (syn_csn (.cv x)) (.cv l))
      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)) p0020
  have p0022 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv l))
        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))
      t (syn_csn (.cv x)) dv_cache_0008 dv_cache_0009 p0019 p0021
  have p0023 :=
    @g_elin (syn_copk (syn_csn (.cv x)) (.cv l))
      (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)
  have p0024 :=
    @g_opkelxpk (syn_csn (.cv x)) (.cv l) (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)
      p0019 p0005
  have p0025 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
        (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cab z (.objMem y z))))
      (.classMem (.cv l) (syn_cvv)) p0005 p0024
  have p0026 := @g_snelpw1 (.cv x) (.cab z (.objMem y z))
  have p0027 := @g_vex x
  have p0028 := @g_elequ2 z x y
  have p0029_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv z) (.cv x)) (syn_wb (.objMem y z) (.objMem y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0028
  have p0029 :=
    @g_elab (.objMem y z) (.objMem y x) z (.cv x) dv_cache_0010 dv_cache_0011 p0027
      p0029_e01_recanon
  have p0030 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
        (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cab z (.objMem y z))))
      (.classMem (.cv x) (.cab z (.objMem y z))) (.objMem y x) p0025 p0026 p0029
  have p0031 := @g_elssetk (.cv x) (.cv l) p0027 p0005
  have p0032_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv l)) (syn_cssetk)) (.objMem x l)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
        (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)))
      (.objMem y x) (.classMem (syn_copk (syn_csn (.cv x)) (.cv l)) (syn_cssetk))
      (.objMem x l) p0030 p0032_e01_recanon
  have p0033 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv l))
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv l))
          (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)))
        (.classMem (syn_copk (syn_csn (.cv x)) (.cv l)) (syn_cssetk)))
      (syn_wa (.objMem y x) (.objMem x l)) p0022 p0023 p0032
  have p0034 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv l))
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk)))))
      (syn_wa (.objMem y x) (.objMem x l)) x p0033
  have p0035 :=
    @g_n_3bitri
      (.classMem (.cv l) (syn_cimak
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
          (syn_c1c)))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv l))
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv l))
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))))))
      (syn_wex x (syn_wa (.objMem y x) (.objMem x l))) p0010 p0018 p0034
  have p0036 :=
    @g_snelpw1 (.cv l)
      (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
        (syn_c1c))
  have p0037 := @g_eluni x (.cv y) (.cv l) dv_cache_0012 dv_cache_0013
  have p0038_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv y) (syn_cuni (.cv l)))
        (syn_wex x (syn_wa (.objMem y x) (.objMem x l)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
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
    @g_n_3bitr4i
      (.classMem (.cv l) (syn_cimak
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
          (syn_c1c)))
      (syn_wex x (syn_wa (.objMem y x) (.objMem x l)))
      (.classMem (syn_csn (.cv l)) (syn_cpw1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
            (syn_c1c))))
      (.classMem (.cv y) (syn_cuni (.cv l))) p0035 p0036 p0038_e02_recanon
  have p0039 :=
    @g_xchbinx
      (.classMem (syn_csn (.cv l)) (syn_ccompl (syn_cpw1 (syn_cimak
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
              (syn_c1c)))))
      (.classMem (syn_csn (.cv l)) (syn_cpw1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
            (syn_c1c))))
      (.classMem (.cv y) (syn_cuni (.cv l))) p0009 p0038
  have p0040 :=
    @g_opkelxpk (syn_csn (.cv l)) (.cv n)
      (syn_ccompl (syn_cpw1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
            (syn_c1c))))
      (syn_cvv) p0000 p0006
  have p0041 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                (syn_c1c)))) (syn_cvv)))
      (.classMem (syn_csn (.cv l)) (syn_ccompl (syn_cpw1 (syn_cimak
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
              (syn_c1c)))))
      (.classMem (.cv n) (syn_cvv)) p0006 p0040
  have p0042 := @g_vex y
  have p0043 := @g_elcompl (.cv y) (syn_cuni (.cv l)) p0042
  have p0044 :=
    @g_n_3bitr4i
      (.classMem (syn_csn (.cv l)) (syn_ccompl (syn_cpw1 (syn_cimak
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
              (syn_c1c)))))
      (.neg (.classMem (.cv y) (syn_cuni (.cv l))))
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                (syn_c1c)))) (syn_cvv)))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) p0039 p0041 p0043
  have p0045 :=
    @g_eqabb (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) x
      (.cv z) dv_cache_0014
  have p0046_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv z) (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
        (.all x (syn_wb (.objMem x z) (syn_wrex b (.cv l)
              (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_csn]
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
    @g_anbi1i
      (.classEq (.cv z) (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (.all x (syn_wb (.objMem x z)
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (.objMem z n) p0046_e00_recanon
  have p0047 :=
    @g_exbii
      (syn_wa (.classEq (.cv z) (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
        (.objMem z n))
      (syn_wa (.all x (syn_wb (.objMem x z)
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
        (.objMem z n))
      z p0046
  have p0048 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV z
      (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.cv n) dv_cache_0015 dv_cache_0016)
  have p0049 := @g_opkex (syn_csn (.cv l)) (.cv n)
  have p0050 :=
    @g_elimak t
      (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                    (syn_cun (syn_cssetk)
                                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn (.cv l)) (.cv n)) dv_cache_0017
      dv_cache_0018 dv_cache_0019 p0049
  have p0051 := @g_elpw121c z (.cv t) dv_cache_0020
  have p0052 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
            (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))))
      p0051
  have p0053 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
            (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))))
      z dv_cache_0021
  have p0054 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk)))))
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk)))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))
      p0052 p0053
  have p0055 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk)))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))
      t p0054
  have p0056 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))))))
  have p0057 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk)))))
      z t
  have p0058 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))
      (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
                (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk)))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
                (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))))
      p0055 p0056 p0057
  have p0059 := @g_snex (syn_csn (syn_csn (.cv z)))
  have p0060 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))
      (syn_copk (syn_csn (.cv l)) (.cv n))
  have p0061 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn (.cv l)) (.cv n)))
      (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                    (syn_cun (syn_cssetk)
                                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cins2k (syn_cssetk)))
      p0060
  have p0062 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
            (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))))
      t (syn_csn (syn_csn (syn_csn (.cv z)))) dv_cache_0022 dv_cache_0023 p0059 p0061
  have p0063 :=
    @g_elin
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn (.cv l)) (.cv n)))
      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_cssetk)
                                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cins2k (syn_cssetk))
  have p0064 := @g_snex (.cv z)
  have p0065 :=
    @g_otkelins3k (syn_csn (.cv z)) (syn_csn (.cv l)) (.cv n)
      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0064 p0000 p0006
  have p0066 := @g_vex z
  have p0067 :=
    @g_opksnelsik (.cv z) (.cv l)
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0066 p0005
  have p0068 := @g_opkex (.cv z) (.cv l)
  have p0069 :=
    @g_elimak t
      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv z) (.cv l)) dv_cache_0024
      dv_cache_0018 dv_cache_0025 p0068
  have p0070 := @g_elpw121c x (.cv t) dv_cache_0006
  have p0071 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0070
  have p0072 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      x dv_cache_0026
  have p0073 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0071 p0072
  have p0074 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t p0073
  have p0075 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0076 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      x t
  have p0077 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_cun (syn_cssetk)
                                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_cun (syn_cssetk)
                                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0074 p0075 p0076
  have p0078 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0079 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l))
  have p0080 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0079
  have p0081 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      t (syn_csn (syn_csn (syn_csn (.cv x)))) dv_cache_0027 dv_cache_0028 p0078 p0080
  have p0082 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
      (syn_cins3k (syn_cssetk))
      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0083 :=
    @g_otkelins3k (syn_csn (.cv x)) (.cv z) (.cv l) (syn_cssetk) p0019 p0066 p0005
  have p0084 := @g_elssetk (.cv x) (.cv z) p0027 p0066
  have p0085_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_cssetk)) (.objMem x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_cssetk)) (.objMem x z) p0083
      p0085_e01_recanon
  have p0086 := @g_opkex (syn_csn (.cv x)) (.cv l)
  have p0087 :=
    @g_elimak t
      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn (.cv x)) (.cv l)) dv_cache_0029
      dv_cache_0018 dv_cache_0030 p0086
  have p0088 := @g_elpw121c b (.cv t) dv_cache_0031
  have p0089 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0088
  have p0090 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      b dv_cache_0032
  have p0091 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wa (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0089 p0090
  have p0092 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      t p0091
  have p0093 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
  have p0094 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      b t
  have p0095 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex t (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex b (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0092 p0093 p0094
  have p0096 := @g_snex (syn_csn (syn_csn (.cv b)))
  have p0097 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_copk (syn_csn (.cv x)) (.cv l))
  have p0098 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv x)) (.cv l)))
      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0097
  have p0099 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t (syn_csn (syn_csn (syn_csn (.cv b)))) dv_cache_0033 dv_cache_0034 p0096 p0098
  have p0100 :=
    @g_elin
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv x)) (.cv l)))
      (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_cun (syn_cssetk)
                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0101 := @g_snex (.cv b)
  have p0102 :=
    @g_otkelins2k (syn_csn (.cv b)) (syn_csn (.cv x)) (.cv l) (syn_cssetk) p0101 p0019
      p0005
  have p0103 := @g_vex b
  have p0104 := @g_elssetk (.cv b) (.cv l) p0103 p0005
  have p0105_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv l)) (syn_cssetk)) (.objMem b l)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv l)) (syn_cssetk)) (.objMem b l) p0102
      p0105_e01_recanon
  have p0106 :=
    @g_otkelins3k (syn_csn (.cv b)) (syn_csn (.cv x)) (.cv l)
      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0101 p0019 p0005
  have p0107 :=
    @g_opksnelsik (.cv b) (.cv x)
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0103 p0027
  have p0108 :=
    @g_alex (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y)))))
      z
  have p0109 :=
    @g_dfcleq z (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))) dv_cache_0010 dv_cache_0035
  have p0110 := @g_opkex (.cv b) (.cv x)
  have p0111 :=
    @g_elcompl (syn_copk (.cv b) (.cv x))
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0110
  have p0112 :=
    @g_elimak t
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
          (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv b) (.cv x)) dv_cache_0036
      dv_cache_0018 dv_cache_0037 p0110
  have p0113 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      p0051
  have p0114 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      z dv_cache_0038
  have p0115 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))))
      p0113 p0114
  have p0116 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))))
      t p0115
  have p0117 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))))
  have p0118 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))
      z t
  have p0119 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))))
      (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))))
      p0116 p0117 p0118
  have p0120 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x))
  have p0121 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
          (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
      p0120
  have p0122 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      t (syn_csn (syn_csn (syn_csn (.cv z)))) dv_cache_0022 dv_cache_0039 p0059 p0121
  have p0123 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
      (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))
  have p0124 :=
    @g_otkelins2k (syn_csn (.cv z)) (.cv b) (.cv x) (syn_cssetk) p0064 p0103 p0027
  have p0125 := @g_elssetk (.cv z) (.cv x) p0066 p0027
  have p0126_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_cssetk)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_cssetk)) (.objMem z x) p0124
      p0126_e01_recanon
  have p0127 :=
    @g_otkelins3k (syn_csn (.cv z)) (.cv b) (.cv x)
      (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))) p0064 p0103
      p0027
  have p0128 := @g_elssetk (.cv z) (.cv b) p0066 p0103
  have p0129 := @g_elsnc (syn_csn (.cv z)) (syn_csn (.cv y)) p0064
  have p0130 := @g_sneqb (.cv z) (.cv y) p0066
  have p0131_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv z)) (syn_csn (.cv y))) (.objEq z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_bitri (.classMem (syn_csn (.cv z)) (syn_csn (syn_csn (.cv y))))
      (.classEq (syn_csn (.cv z)) (syn_csn (.cv y))) (.objEq z y) p0129 p0131_e01_recanon
  have p0132 :=
    @g_opkelxpk (syn_csn (.cv z)) (.cv b) (syn_csn (syn_csn (.cv y))) (syn_cvv) p0064
      p0103
  have p0133 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv b))
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))
      (.classMem (syn_csn (.cv z)) (syn_csn (syn_csn (.cv y))))
      (.classMem (.cv b) (syn_cvv)) p0103 p0132
  have p0134 := @g_elsnc (.cv z) (.cv y) p0066
  have p0135_e02_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_csn (.cv y))) (.objEq z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_n_3bitr4i (.classMem (syn_csn (.cv z)) (syn_csn (syn_csn (.cv y)))) (.objEq z y)
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv b))
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))
      (.classMem (.cv z) (syn_csn (.cv y))) p0131 p0133 p0135_e02_recanon
  have p0136_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv b)) (syn_cssetk)) (.objMem z b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_orbi12i (.classMem (syn_copk (syn_csn (.cv z)) (.cv b)) (syn_cssetk)) (.objMem z b)
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv b))
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))
      (.classMem (.cv z) (syn_csn (.cv y))) p0136_e00_recanon p0135
  have p0137 :=
    @g_elun (syn_copk (syn_csn (.cv z)) (.cv b)) (syn_cssetk)
      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))
  have p0138 := @g_elun (.cv z) (.cv b) (syn_csn (.cv y))
  have p0139_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))
        (syn_wo (.objMem z b) (.classMem (.cv z) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_wo
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
    @g_n_3bitr4i
      (syn_wo (.classMem (syn_copk (syn_csn (.cv z)) (.cv b)) (syn_cssetk))
        (.classMem (syn_copk (syn_csn (.cv z)) (.cv b))
          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))
      (syn_wo (.objMem z b) (.classMem (.cv z) (syn_csn (.cv y))))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv b))
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))
      (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y)))) p0136 p0137
      p0139_e02_recanon
  have p0140 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_cins3k (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv b))
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))
      (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y)))) p0127 p0139
  have p0141 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_cins2k (syn_cssetk)))
      (.objMem z x)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_cins3k (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
      (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y)))) p0126 p0140
  have p0142 :=
    @g_xchbinx
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      (syn_wb (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
          (syn_cins2k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
          (syn_cins3k (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))) p0123
      p0141
  have p0143 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv b) (.cv x)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))
      (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))))
      p0122 p0142
  have p0144 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))))))
      (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))))
      z p0143
  have p0145 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv b) (.cv x)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv b) (.cv x)))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))))))
      (syn_wex z (.neg
          (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0112 p0119 p0144
  have p0146 :=
    @g_xchbinx
      (.classMem (syn_copk (.cv b) (.cv x)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_copk (.cv b) (.cv x)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex z (.neg
          (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0111 p0145
  have p0147_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) (.all z
          (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
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
    @g_n_3bitr4ri
      (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.neg (syn_wex z (.neg (syn_wb (.objMem z x)
              (.classMem (.cv z) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.classMem (syn_copk (.cv b) (.cv x)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0108 p0147_e01_recanon p0146
  have p0148 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (.cv b)) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (.cv b) (.cv x)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) p0106 p0107 p0147
  have p0149 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cins2k (syn_cssetk)))
      (.objMem b l)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))) p0105 p0148
  have p0150 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
            (syn_copk (syn_csn (.cv x)) (.cv l))) (syn_cins2k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.objMem b l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) p0099
      p0100 p0149
  have p0151 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wa (.objMem b l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) b
      p0150
  have p0152 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l)) (syn_cimak
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex b (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv l)))
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wex b (syn_wa (.objMem b l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      p0087 p0095 p0151
  have p0153 :=
    @g_otkelins2k (syn_csn (.cv x)) (.cv z) (.cv l)
      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0019 p0066 p0005
  have p0154 :=
    (Nominal.biimpRefl
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
  have p0155_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))
        (syn_wex b (syn_wa (.objMem b l)
            (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_csn]
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
    @g_n_3bitr4i
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv l)) (syn_cimak
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex b (syn_wa (.objMem b l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) p0152
      p0153 p0155_e02_recanon
  have p0156 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_cins3k (syn_cssetk)))
      (.objMem x z)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))) p0085
      p0155
  have p0157 :=
    @g_xchbinx
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wb (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
          (syn_cins3k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wb (.objMem x z)
        (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      p0082 p0156
  have p0158 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv z) (.cv l)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.neg (syn_wb (.objMem x z)
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0081 p0157
  have p0159 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.neg (syn_wb (.objMem x z)
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      x p0158
  have p0160 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv z) (.cv l)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (.cv l)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_cun (syn_cssetk)
                                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (.neg (syn_wb (.objMem x z)
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      p0069 p0077 p0159
  have p0161 :=
    @g_notbii
      (.classMem (syn_copk (.cv z) (.cv l)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.neg (syn_wb (.objMem x z)
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))))
      p0160
  have p0162 :=
    @g_elcompl (syn_copk (.cv z) (.cv l))
      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0068
  have p0163 :=
    @g_alex
      (syn_wb (.objMem x z)
        (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
      x
  have p0164 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_copk (.cv z) (.cv l)) (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (syn_wex x (.neg (syn_wb (.objMem x z) (syn_wrex b (.cv l)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))))
      (.classMem (syn_copk (.cv z) (.cv l)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.all x (syn_wb (.objMem x z)
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0161 p0162 p0163
  have p0165 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                    (syn_cun (syn_cssetk)
                                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv l))) (syn_csik (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_cun (syn_cssetk)
                                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (.cv z) (.cv l)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.all x (syn_wb (.objMem x z)
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      p0065 p0067 p0164
  have p0166 :=
    @g_otkelins2k (syn_csn (.cv z)) (syn_csn (.cv l)) (.cv n) (syn_cssetk) p0064 p0000
      p0006
  have p0167 := @g_elssetk (.cv z) (.cv n) p0066 p0006
  have p0168_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv n)) (syn_cssetk)) (.objMem z n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv n)) (syn_cssetk)) (.objMem z n) p0166
      p0168_e01_recanon
  have p0169 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                    (syn_cun (syn_cssetk)
                                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.all x (syn_wb (.objMem x z)
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cins2k (syn_cssetk)))
      (.objMem z n) p0165 p0168
  have p0170 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
            (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
            (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cins2k (syn_cssetk))))
      (syn_wa (.all x (syn_wb (.objMem x z)
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
        (.objMem z n))
      p0062 p0063 p0169
  have p0171 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))
      (syn_wa (.all x (syn_wb (.objMem x z)
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))))
        (.objMem z n))
      z p0170
  have p0172 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cimak (syn_cin (syn_cins3k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                        (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin (syn_cins3k
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk)))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv l)) (.cv n))) (syn_cin
                (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))))
      (syn_wex z (syn_wa (.all x (syn_wb (.objMem x z) (syn_wrex b (.cv l)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) (.objMem z n)))
      p0050 p0058 p0171
  have p0173_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)) (syn_wex z (syn_wa (.classEq (.cv z) (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) (.objMem z n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cun, syn_cnin, syn_wnan,
          syn_ccompl, syn_csn]
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
    @g_n_3bitr4ri
      (syn_wex z (syn_wa (.classEq (.cv z) (.cab x (syn_wrex b (.cv l)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) (.objMem z n)))
      (syn_wex z (syn_wa (.all x (syn_wb (.objMem x z) (syn_wrex b (.cv l)
                (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))) (.objMem z n)))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cimak (syn_cin (syn_cins3k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                        (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0047 p0173_e01_recanon p0172
  have p0174 :=
    @g_notbii
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cimak (syn_cin (syn_cins3k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                        (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
      p0173
  have p0175 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                (syn_c1c)))) (syn_cvv)))
      (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
      (.neg (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cimak (syn_cin (syn_cins3k
                (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)))
      p0044 p0174
  have p0176 :=
    @g_annim (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
      (.classMem (.cab x
          (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))
  have p0177 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1
                (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                    (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cxpk (syn_ccompl (syn_cpw1
                (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                    (syn_cssetk)) (syn_c1c)))) (syn_cvv))) (.neg
          (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.neg (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      p0008 p0175 p0176
  have p0178_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cssetk)) (.objMem l n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cssetk)) (.objMem l n)
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1
                (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                    (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
              (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      p0178_e00_recanon p0177
  have p0179 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
          (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                  (syn_ccompl (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
              (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cssetk))
        (.classMem (syn_copk (syn_csn (.cv l)) (.cv n)) (syn_cdif (syn_cxpk (syn_ccompl
                (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.objMem l n) (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n)))))
      p0003 p0004 p0178
  have p0180 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
          (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                  (syn_ccompl (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.objMem l n) (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n)))))
      l p0179
  have p0181 :=
    @g_elimak t
      (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                  (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                  (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_c1c) (.cv n) dv_cache_0040 dv_cache_0004 dv_cache_0041 p0006
  have p0182 := @g_el1c l (.cv t) dv_cache_0042
  have p0183 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex l (.classEq (.cv t) (syn_csn (.cv l))))
      (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
              (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0182
  have p0184 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv l)))
      (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
              (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      l dv_cache_0043
  have p0185 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv n))
          (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (syn_wex l (.classEq (.cv t) (syn_csn (.cv l))))
        (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex l (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
          (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                  (syn_ccompl (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0183 p0184
  have p0186 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv n))
          (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex l (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
          (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                  (syn_ccompl (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t p0185
  have p0187 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv n))
          (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0188 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv l))) (.classMem (syn_copk (.cv t) (.cv n))
          (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      l t
  have p0189 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv n))
            (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex t (syn_wex l (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
            (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                    (syn_ccompl (syn_cpw1 (syn_cimak
                          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                            (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk)
            (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex l (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
            (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                    (syn_ccompl (syn_cpw1 (syn_cimak
                          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                            (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0186 p0187 p0188
  have p0190 :=
    @g_bitri
      (.classMem (.cv n) (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl
                  (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c)))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk)
            (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex l (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
            (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                    (syn_ccompl (syn_cpw1 (syn_cimak
                          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                            (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0181 p0189
  have p0191 :=
    (Nominal.biimpRefl (syn_wrex l (.cv n) (.neg
          (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
              (.cv n))))))
  have p0192_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex l (.cv n) (.neg
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv n))))) (syn_wex l (syn_wa (.objMem l n) (.neg
              (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                    (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                  (.cv n))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ccompl, syn_cnin, syn_wnan,
          syn_cuni]
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
    @g_n_3bitr4i
      (syn_wex l (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv l)))
            (.classMem (syn_copk (.cv t) (.cv n)) (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                    (syn_ccompl (syn_cpw1 (syn_cimak
                          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                            (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex l (syn_wa (.objMem l n) (.neg
            (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
                  (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
                (.cv n))))))
      (.classMem (.cv n) (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl
                  (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c)))
      (syn_wrex l (.cv n) (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n)))))
      p0180 p0190 p0192_e02_recanon
  have p0193 :=
    @g_notbii
      (.classMem (.cv n) (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl
                  (syn_cpw1 (syn_cimak
                      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c)))
      (syn_wrex l (.cv n) (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n)))))
      p0192
  have p0194 :=
    @g_elcompl (.cv n)
      (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c))
      p0006
  have p0195 :=
    @g_dfral2
      (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem (.cab x
            (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
          (.cv n)))
      l (.cv n)
  have p0196 :=
    @g_n_3bitr4i
      (.neg (.classMem (.cv n) (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl
                    (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c))))
      (.neg (syn_wrex l (.cv n) (.neg (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
              (.classMem (.cab x (syn_wrex b (.cv l)
                    (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n))))))
      (.classMem (.cv n) (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk
                  (syn_ccompl (syn_cpw1 (syn_cimak
                        (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                          (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c))))
      (syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      p0193 p0194 p0195
  have p0197 :=
    @g_eqabi
      (syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l)))) (.classMem
            (.cab x (syn_wrex b (.cv l) (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y))))))
            (.cv n))))
      n
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1
                    (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c)))
      dv_cache_0044 p0196
  have p0198 := @g_ssetkex
  have p0199 := @g_setswithex z (.cv y) dv_cache_0045
  have p0200_e00_recanon : Nominal.NPrf (.classMem (.cab z (.objMem y z)) (syn_cvv)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classMem
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _)
      p0199
  have p0200 := @g_pw1ex (.cab z (.objMem y z)) p0200_e00_recanon
  have p0201 := @g_vvex
  have p0202 := @g_xpkex (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv) p0200 p0201
  have p0204 :=
    @g_inex (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk) p0202
      p0198
  have p0205 := @g_n_1cex
  have p0206 :=
    @g_imakex
      (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
      (syn_c1c) p0204 p0205
  have p0207 :=
    @g_pw1ex
      (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
        (syn_c1c))
      p0206
  have p0208 :=
    @g_complex
      (syn_cpw1 (syn_cimak
          (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
          (syn_c1c)))
      p0207
  have p0210 :=
    @g_xpkex
      (syn_ccompl (syn_cpw1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
            (syn_c1c))))
      (syn_cvv) p0208 p0201
  have p0212 := @g_ins3kex (syn_cssetk) p0198
  have p0214 := @g_ins2kex (syn_cssetk) p0198
  have p0216 := @g_snex (syn_csn (.cv y))
  have p0218 := @g_xpkex (syn_csn (syn_csn (.cv y))) (syn_cvv) p0216 p0201
  have p0219 :=
    @g_unex (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)) p0198 p0218
  have p0220 :=
    @g_ins3kex (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))
      p0219
  have p0221 :=
    @g_symdifex (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))
      p0214 p0220
  have p0223 := @g_pw1ex (syn_c1c) p0205
  have p0224 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0223
  have p0225 :=
    @g_imakex
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
          (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0221 p0224
  have p0226 :=
    @g_complex
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
            (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0225
  have p0227 :=
    @g_sikex
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
              (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0226
  have p0228 :=
    @g_ins3kex
      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0227
  have p0229 :=
    @g_inex (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_cun (syn_cssetk)
                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0214 p0228
  have p0230 :=
    @g_imakex
      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0229 p0224
  have p0231 :=
    @g_ins2kex
      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0230
  have p0232 :=
    @g_symdifex (syn_cins3k (syn_cssetk))
      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cun (syn_cssetk)
                          (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0212 p0231
  have p0233 :=
    @g_imakex
      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                            (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0232 p0224
  have p0234 :=
    @g_complex
      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
                              (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0233
  have p0235 :=
    @g_sikex
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_cssetk)
                                (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0234
  have p0236 :=
    @g_ins3kex
      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cssetk)
                                  (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0235
  have p0237 :=
    @g_inex
      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_cssetk)
                                    (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cins2k (syn_cssetk)) p0236 p0214
  have p0238 :=
    @g_imakex
      (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                    (syn_cun (syn_cssetk)
                                      (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0237 p0224
  have p0239 :=
    @g_difex
      (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
              (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
              (syn_c1c)))) (syn_cvv))
      (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cssetk)
                                        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0210 p0238
  have p0240 :=
    @g_inex (syn_cssetk)
      (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0198 p0239
  have p0242 :=
    @g_imakex
      (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                  (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv)) (syn_cssetk))
                  (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_c1c) p0240 p0205
  have p0243 :=
    @g_complex
      (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1 (syn_cimak
                    (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                      (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cssetk) (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c))
      p0242
  have p0244 :=
    @g_eqeltrri
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cdif (syn_cxpk (syn_ccompl (syn_cpw1
                    (syn_cimak (syn_cin (syn_cxpk (syn_cpw1 (.cab z (.objMem y z))) (syn_cvv))
                        (syn_cssetk)) (syn_c1c)))) (syn_cvv)) (syn_cimak (syn_cin (syn_cins3k
                    (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_cssetk)
        (syn_cxpk (syn_csn (syn_csn (.cv y))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_c1c)))
      (.cab n (syn_wral l (.cv n) (.imp (.classMem (.cv y) (syn_ccompl (syn_cuni (.cv l))))
            (.classMem (.cab x (syn_wrex b (.cv l)
                  (.classEq (.cv x) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.cv n)))))
      (syn_cvv) p0197 p0243
  exact p0244


end NFChoice.DirectNominalPrf.WPPReplay
