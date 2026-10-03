/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block016

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part071`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit

@[expose]
noncomputable def g_hnwcutcodecmpbrndv (x : Var) (y : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
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
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ y } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show y ≠ u from (by exact Ne.symm dv_u_y)))))))),
                  (show Disjoint (({ y } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [fv_syn_c1st];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
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
  have dv_cache_0003 :
    Disjoint ((Class.cv z)).fv
      ((syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var))
                ((((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                      (syn_cfv (syn_c2nd) (.cv u)) (.cv x))).fv) ∪
                  (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show
                    Disjoint (({ z } : Finset Var))
                      (((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                          (syn_cfv (syn_c2nd) (.cv u)) (.cv x))).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode];
                      exact
                        (show
                          Disjoint (({ z } : Finset Var))
                            ((((Class.cv x)).fv) ∪ (((syn_cfv (syn_c2nd) (.cv u))).fv) ∪
                              (((syn_cfv (syn_c1st) (.cv u))).fv))
                          from
                          (Finset.disjoint_union_right.mpr
                            ⟨(Finset.disjoint_union_right.mpr
                                ⟨(show Disjoint (({ z } : Finset Var)) (((Class.cv x)).fv)
                                    from
                                    (by
                                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                      exact
                                        (show
                                          Disjoint (({ z } : Finset Var))
                                            (({ x } : Finset Var))
                                          from
                                          (Finset.disjoint_singleton_left.mpr
                                            (show z ∉ ({ x } : Finset Var) from
                                              (by
                                                simpa only [Finset.mem_singleton] using
                                                  (show z ≠ x from
                                                    (by exact fresh_z_ne_x)))))))),
                                  (show
                                    Disjoint (({ z } : Finset Var))
                                      (((syn_cfv (syn_c2nd) (.cv u))).fv)
                                    from
                                    (by
                                      rw [fv_syn_cfv];
                                      exact
                                        (show
                                          Disjoint (({ z } : Finset Var))
                                            ((((Class.cv u)).fv) ∪ (((syn_c2nd)).fv))
                                          from
                                          (Finset.disjoint_union_right.mpr
                                            ⟨(show
                                                Disjoint (({ z } : Finset Var))
                                                  (((Class.cv u)).fv)
                                                from
                                                (by
                                                  rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                                  exact
                                                    (show
                                                      Disjoint (({ z } : Finset Var))
                                                        (({ u } : Finset Var))
                                                      from
                                                      (Finset.disjoint_singleton_left.mpr
                                                        (show z ∉ ({ u } : Finset Var)
                                                          from
                                                          (by
                                                            simpa only [Finset.mem_singleton] using
                                                              (show z ≠ u from
                                                                (by
                                                                  exact
                                                                    fresh_z_ne_u)))))))),
                                              (show
                                                Disjoint (({ z } : Finset Var))
                                                  (((syn_c2nd)).fv)
                                                from
                                                (by
                                                  rw [fv_syn_c2nd];
                                                  exact
                                                    (show
                                                      Disjoint (({ z } : Finset Var))
                                                        ((∅ : Finset Var))
                                                      from (by simp))))⟩))))⟩),
                              (show
                                Disjoint (({ z } : Finset Var))
                                  (((syn_cfv (syn_c1st) (.cv u))).fv)
                                from
                                (by
                                  rw [fv_syn_cfv];
                                  exact
                                    (show
                                      Disjoint (({ z } : Finset Var))
                                        ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
                                      from
                                      (Finset.disjoint_union_right.mpr
                                        ⟨(show
                                            Disjoint (({ z } : Finset Var))
                                              (((Class.cv u)).fv)
                                            from
                                            (by
                                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                              exact
                                                (show
                                                  Disjoint (({ z } : Finset Var))
                                                    (({ u } : Finset Var))
                                                  from
                                                  (Finset.disjoint_singleton_left.mpr
                                                    (show z ∉ ({ u } : Finset Var) from
                                                      (by
                                                        simpa only [Finset.mem_singleton] using
                                                          (show z ≠ u from
                                                            (by
                                                              exact fresh_z_ne_u)))))))),
                                          (show
                                            Disjoint (({ z } : Finset Var))
                                              (((syn_c1st)).fv)
                                            from
                                            (by
                                              rw [fv_syn_c1st];
                                              exact
                                                (show
                                                  Disjoint (({ z } : Finset Var))
                                                    ((∅ : Finset Var))
                                                  from (by simp))))⟩))))⟩)))),
                  (show Disjoint (({ z } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [fv_syn_c1st];
                      exact
                        (show Disjoint (({ z } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_cfv, fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, fv_syn_cfv,
          fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_u, fresh_z_ne_x, fresh_z_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    z ∉
      ((syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
            (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
          (syn_wne (.cv y) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fv_syn_cfv,
          fv_syn_c2nd, fv_syn_wbr, fv_syn_c1st, fv_syn_wne, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_u, fresh_z_ne_x, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          fv_syn_cfv, fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_c2nd,
          Finset.mem_union, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          fv_syn_cfv, fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_c2nd,
          Finset.mem_union, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ u from (by exact Ne.symm dv_u_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0012 :
    Disjoint ((Class.cv z)).fv
      ((syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint ((Class.cv z)).fv ((syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var))
                ((((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                      (syn_cfv (syn_c2nd) (.cv u)) (.cv y))).fv) ∪
                  (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show
                    Disjoint (({ z } : Finset Var))
                      (((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                          (syn_cfv (syn_c2nd) (.cv u)) (.cv y))).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode];
                      exact
                        (show
                          Disjoint (({ z } : Finset Var))
                            ((((Class.cv y)).fv) ∪ (((syn_cfv (syn_c2nd) (.cv u))).fv) ∪
                              (((syn_cfv (syn_c1st) (.cv u))).fv))
                          from
                          (Finset.disjoint_union_right.mpr
                            ⟨(Finset.disjoint_union_right.mpr
                                ⟨(show Disjoint (({ z } : Finset Var)) (((Class.cv y)).fv)
                                    from
                                    (by
                                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                      exact
                                        (show
                                          Disjoint (({ z } : Finset Var))
                                            (({ y } : Finset Var))
                                          from
                                          (Finset.disjoint_singleton_left.mpr
                                            (show z ∉ ({ y } : Finset Var) from
                                              (by
                                                simpa only [Finset.mem_singleton] using
                                                  (show z ≠ y from
                                                    (by exact fresh_z_ne_y)))))))),
                                  (show
                                    Disjoint (({ z } : Finset Var))
                                      (((syn_cfv (syn_c2nd) (.cv u))).fv)
                                    from
                                    (by
                                      rw [fv_syn_cfv];
                                      exact
                                        (show
                                          Disjoint (({ z } : Finset Var))
                                            ((((Class.cv u)).fv) ∪ (((syn_c2nd)).fv))
                                          from
                                          (Finset.disjoint_union_right.mpr
                                            ⟨(show
                                                Disjoint (({ z } : Finset Var))
                                                  (((Class.cv u)).fv)
                                                from
                                                (by
                                                  rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                                  exact
                                                    (show
                                                      Disjoint (({ z } : Finset Var))
                                                        (({ u } : Finset Var))
                                                      from
                                                      (Finset.disjoint_singleton_left.mpr
                                                        (show z ∉ ({ u } : Finset Var)
                                                          from
                                                          (by
                                                            simpa only [Finset.mem_singleton] using
                                                              (show z ≠ u from
                                                                (by
                                                                  exact
                                                                    fresh_z_ne_u)))))))),
                                              (show
                                                Disjoint (({ z } : Finset Var))
                                                  (((syn_c2nd)).fv)
                                                from
                                                (by
                                                  rw [fv_syn_c2nd];
                                                  exact
                                                    (show
                                                      Disjoint (({ z } : Finset Var))
                                                        ((∅ : Finset Var))
                                                      from (by simp))))⟩))))⟩),
                              (show
                                Disjoint (({ z } : Finset Var))
                                  (((syn_cfv (syn_c1st) (.cv u))).fv)
                                from
                                (by
                                  rw [fv_syn_cfv];
                                  exact
                                    (show
                                      Disjoint (({ z } : Finset Var))
                                        ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
                                      from
                                      (Finset.disjoint_union_right.mpr
                                        ⟨(show
                                            Disjoint (({ z } : Finset Var))
                                              (((Class.cv u)).fv)
                                            from
                                            (by
                                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                              exact
                                                (show
                                                  Disjoint (({ z } : Finset Var))
                                                    (({ u } : Finset Var))
                                                  from
                                                  (Finset.disjoint_singleton_left.mpr
                                                    (show z ∉ ({ u } : Finset Var) from
                                                      (by
                                                        simpa only [Finset.mem_singleton] using
                                                          (show z ≠ u from
                                                            (by
                                                              exact fresh_z_ne_u)))))))),
                                          (show
                                            Disjoint (({ z } : Finset Var))
                                              (((syn_c1st)).fv)
                                            from
                                            (by
                                              rw [fv_syn_c1st];
                                              exact
                                                (show
                                                  Disjoint (({ z } : Finset Var))
                                                    ((∅ : Finset Var))
                                                  from (by simp))))⟩))))⟩)))),
                  (show Disjoint (({ z } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [fv_syn_c1st];
                      exact
                        (show Disjoint (({ z } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0013 : z ∉ ((Class.cv x)).fv :=
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
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)))).fv :=
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
        simp only [fv_syn_cfv, fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    z ∉
      ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (.cv x)))).fv :=
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
        simp only [fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, fv_syn_cfv,
          fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_u, fresh_z_ne_y, fresh_z_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
            (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
          (syn_wne (.cv x) (.cv y)))).fv :=
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
        simp only [fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fv_syn_cfv,
          fv_syn_c2nd, fv_syn_wbr, fv_syn_c1st, fv_syn_wne, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_u, fresh_z_ne_x, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
  have p0001 :=
    @g_a1i
      (.imp (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classEq (.cv x) (.cv y))
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
  have p0004 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      p0003 p0004
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (.classEq (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      p0002 p0005
  have p0007 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0008 :=
    @g_simpld
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      p0007
  have p0009 := @g_hwcnweclndv A (.cv u)
  have p0010 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0008
      p0009
  have p0011 := @g_wppweref (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0012 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cref) (syn_cfv (syn_c2nd) (.cv u))) p0010
      p0011
  have p0014 :=
    @g_simprd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      p0007
  have p0015 :=
    @g_simpld
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0014
  have p0016 :=
    @g_refd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (.cv x) p0012 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (.classEq (.cv x) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) p0006 p0016
  have p0018 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classEq (.cv x) (.cv y))
  have p0019 :=
    @g_breqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (.classEq (.cv x) (.cv y)))
      (.cv x) (.cv x) (.cv y) (syn_cfv (syn_c1st) (.cv u)) p0017 p0018
  have p0020 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classEq (.cv x) (.cv y)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
      p0019
  have p0021 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv x) (.cv y))
  have p0023 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0003 p0023
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0021 p0024
  have p0027 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) p0021 p0027
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      p0021 p0005
  have p0034 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classEq (.cv y) (.cv x))
  have p0035 :=
    @g_hnwcutcodeeq3 (.cv y) (.cv x) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (.classEq (.cv y) (.cv x))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)))
      p0034 p0035
  have p0037 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classEq (.cv y) (.cv x))
  have p0038 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
  have p0039 :=
    @g_simpl (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem A (syn_cvv)) p0038 p0039
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem A (syn_cvv)) p0037 p0040
  have p0042 := @g_hncodecmpsetrefndv A
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      p0041 p0042
  have p0051 :=
    @g_jca
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      p0008 p0015
  have p0052 := @g_hnwcutcodeambientndv x u A dv_cache_0002
  have p0053 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0051 p0052
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0038 p0053
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0037 p0054
  have p0056 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (syn_chwcn A) (syn_chncodecmpset A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      p0043 p0055
  have p0057 :=
    @g_eqbrtrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chncodecmpset A) p0036 p0056
  have p0058 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classEq (.cv y) (.cv x))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0057
  have p0059 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv y) (.cv x))
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem A (syn_cvv)) p0059 p0040
  have p0064 := @g_hwnisoerv A
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv)) p0063 p0064
  have p0066 := @g_hwnisodm A
  have p0067 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      p0066
  have p0074 :=
    @g_simprd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0014
  have p0075 :=
    @g_jca
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      p0008 p0074
  have p0076 := @g_hnwcutcodeambientndv y u A dv_cache_0002
  have p0077 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0075 p0076
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0038 p0077
  have p0079 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0059 p0078
  have p0080 :=
    @g_erref
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_chwcn A) (syn_chwniso A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      p0065 p0067 p0079
  have p0085 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A)) p0038 p0008
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem (.cv u) (syn_chwcn A)) p0059 p0085
  have p0092 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0038 p0015
  have p0093 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0059 p0092
  have p0094 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      p0086 p0093
  have p0095 := @g_hnwcutcodepartsndv x u A dv_cache_0002
  have p0096 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      p0094 p0095
  have p0097 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0096
  have p0114 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0096
  have p0115 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0097 p0114
  have p0116 :=
    @g_hnwcutcodeeq12ndv y
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
  have p0117 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)) (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (.cv y)))
      p0115 p0116
  have p0124 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0038
      p0010
  have p0125 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0059
      p0124
  have p0133 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0125 p0093
  have p0139 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0038 p0074
  have p0140 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0059 p0139
  have p0142 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
  have p0143 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) p0059 p0142
  have p0144 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv y) (.cv x))
  have p0145 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) (syn_wne (.cv y) (.cv x))
      p0143 p0144
  have p0146 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wa (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0140 p0145
  have p0147 :=
    @g_elstrictseg x y (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0148 :=
    @g_a1i
      (syn_wb (.classMem (.cv y) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wa (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
            (syn_wne (.cv y) (.cv x)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      p0147
  have p0149 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem (.cv y) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wa (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
          (syn_wne (.cv y) (.cv x))))
      p0146 p0148
  have p0150 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv y) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0133 p0149
  have p0151 :=
    @g_hnwcutcodenestndv y x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0152 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa
          (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv y)
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv x)))) (.cv y))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0150 p0151
  have p0153 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.cv y))
      (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      p0117 p0152
  have p0154 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chwniso A) p0153
  have p0155 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0080 p0154
  have p0189 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv x))))
      (.cv y) p0114
  have p0190 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem (.cv y) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0149 p0189
  have p0191 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classEq (.cv z) (.cv y))
  have p0192 :=
    @g_hnwcutcodeeq3 (.cv z) (.cv y)
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      dv_cache_0003
  have p0193 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
            (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
        (.classEq (.cv z) (.cv y)))
      (.classEq (.cv z) (.cv y))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv z)) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)))
      p0191 p0192
  have p0194 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
            (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
        (.classEq (.cv z) (.cv y)))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chwniso A) p0193
  have p0195 :=
    @g_rspcedv
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv z)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)))
      z (.cv y)
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0190 p0194
  have p0196 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.cv z))))
      p0155 p0195
  have p0197 :=
    @g_olc
      (syn_wrex z (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.cv z))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0198 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wrex z (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.cv z))))
      (syn_wo (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wrex z (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x))) (.cv z)))))
      p0196 p0197
  have p0222 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0059 p0054
  have p0223 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0079 p0222
  have p0224 :=
    @g_hncodecmpsetstrictcutsemclndv z A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0225 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wa (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
          (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wo (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_wrex z (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (syn_cfv (syn_c2nd)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u)) (.cv x))) (.cv z))))))
      p0223 p0224
  have p0226 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wo (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_wrex z (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x))) (.cv z)))))
      p0198 p0225
  have p0227 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv y) (.cv x))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0226
  have p0228 :=
    @g_pm2_61dne
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (.cv y) (.cv x) p0058 p0227
  have p0229 :=
    @g_ex
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0228
  have p0230 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0033 p0229
  have p0231 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0028 p0230
  have p0232 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0025 p0231
  have p0233 :=
    @g_brlnker (syn_chncodecmpset A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
  have p0234 :=
    @g_biimpri
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_clnker (syn_chncodecmpset A))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wa (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)) (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0233
  have p0235 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv y)) (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_clnker (syn_chncodecmpset A))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0232 p0234
  have p0242 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem A (syn_cvv)) p0033 p0039
  have p0243 := @g_hncodecmplnkerndv A
  have p0244 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (.classMem A (syn_cvv))
      (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0242 p0243
  have p0245 :=
    @g_breqd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      p0244
  have p0246 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_clnker (syn_chncodecmpset A))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0245
  have p0247 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_clnker (syn_chncodecmpset A))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0235 p0246
  have p0256 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) p0033 p0028
  have p0257 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv x) (.cv y))
  have p0258 :=
    @g_necomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0257
  have p0259 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv y) (.cv x)) p0256 p0258
  have p0333 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)))
      p0259 p0153
  have p0334 :=
    @g_breqtrrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.cv y))
      (syn_chwniso A) p0247 p0333
  have p0348 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0033 p0053
  have p0396 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))) (syn_wne (.cv y) (.cv x)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0259 p0190
  have p0397 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (.cv y) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0348 p0396
  have p0398 :=
    @g_hnwcutcodeselfnoisoclndv y A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
  have p0399 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)) (.classMem (.cv y) (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      (.neg (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.cv y))))
      p0397 p0398
  have p0400 :=
    @g_pm2_21dd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
        (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.cv y)))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) p0334 p0399
  have p0401 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wne (.cv x) (.cv y)) (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
      p0400
  have p0402 :=
    @g_pm2_61dne
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))) (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) (.cv x) (.cv y) p0020 p0401
  have p0403 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) p0402
  have p0409 := @g_wppweconnex (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0410 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cconnex) (syn_cfv (syn_c2nd) (.cv u)))
      p0010 p0409
  have p0417 :=
    @g_connexd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (.cv x) (.cv y) p0410
      p0015 p0074
  have p0418 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wo (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
        (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)))
      p0004 p0417
  have p0419 :=
    @g_mpjaod
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
      (syn_wbr (.cv y) (syn_cfv (syn_c1st) (.cv u)) (.cv x)) p0001 p0403 p0418
  have p0420 :=
    @g_ex
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) p0419
  have p0421 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classEq (.cv x) (.cv y))
  have p0422 :=
    @g_hnwcutcodeeq3 (.cv x) (.cv y) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0011
  have p0423 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (.classEq (.cv x) (.cv y))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)))
      p0421 p0422
  have p0424 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classEq (.cv x) (.cv y))
  have p0425 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
  have p0427 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem A (syn_cvv)) p0425 p0039
  have p0428 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem A (syn_cvv)) p0424 p0427
  have p0430 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      p0428 p0042
  have p0441 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0425 p0077
  have p0442 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0424 p0441
  have p0443 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (syn_chwcn A) (syn_chncodecmpset A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      p0430 p0442
  have p0444 :=
    @g_eqbrtrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chncodecmpset A) p0423 p0443
  have p0445 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classEq (.cv x) (.cv y))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0444
  have p0446 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wne (.cv x) (.cv y))
  have p0450 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem A (syn_cvv)) p0446 p0427
  have p0452 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv)) p0450 p0064
  have p0454 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      p0066
  have p0465 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0425 p0053
  have p0466 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0446 p0465
  have p0467 :=
    @g_erref
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_chwcn A) (syn_chwniso A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      p0452 p0454 p0466
  have p0472 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A)) p0425 p0008
  have p0473 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem (.cv u) (syn_chwcn A)) p0446 p0472
  have p0479 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0425 p0074
  have p0480 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0446 p0479
  have p0481 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      p0473 p0480
  have p0482 := @g_hnwcutcodepartsndv y u A dv_cache_0002
  have p0483 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y))))))
      p0481 p0482
  have p0484 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0483
  have p0501 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0483
  have p0502 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classEq (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0484 p0501
  have p0503 :=
    @g_hnwcutcodeeq12ndv x
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv y))))
  have p0504 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classEq (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y))))))) (.classEq (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y))))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv x)) (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y)))) (.cv x)))
      p0502 p0503
  have p0511 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0425
      p0010
  have p0512 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0446
      p0511
  have p0520 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))) p0512 p0480
  have p0526 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0425 p0015
  have p0527 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0446 p0526
  have p0529 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
  have p0530 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) p0446 p0529
  have p0531 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wne (.cv x) (.cv y))
  have p0532 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) (syn_wne (.cv x) (.cv y))
      p0530 p0531
  have p0533 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wa (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) (syn_wne (.cv x) (.cv y)))
      p0527 p0532
  have p0534 :=
    @g_elstrictseg y x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0535 :=
    @g_a1i
      (syn_wb (.classMem (.cv x) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wa (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
            (syn_wne (.cv x) (.cv y)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      p0534
  have p0536 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wa (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
          (syn_wne (.cv x) (.cv y))))
      p0533 p0535
  have p0537 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0520 p0536
  have p0538 :=
    @g_hnwcutcodenestndv x y (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0539 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa
          (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv x)
          (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y))))))
      (.classEq (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                  (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
              (syn_csn (.cv y)))) (.cv x))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0537 p0538
  have p0540 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (.cv x))
      (syn_chnwcutcode (syn_cin (syn_cfv (syn_c1st) (.cv u)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
                (syn_csn (.cv y)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      p0504 p0539
  have p0541 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0540
  have p0542 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0467 p0541
  have p0576 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_cin (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
          (syn_csn (.cv y))))
      (.cv x) p0501
  have p0577 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      (.classMem (.cv x) (syn_cin (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv u)) (syn_cid)))
            (syn_csn (.cv y)))))
      p0536 p0576
  have p0578 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classEq (.cv z) (.cv x))
  have p0579 :=
    @g_hnwcutcodeeq3 (.cv z) (.cv x)
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_cfv (syn_c1st)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      dv_cache_0012
  have p0580 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
            (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
        (.classEq (.cv z) (.cv x)))
      (.classEq (.cv z) (.cv x))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv z)) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv x)))
      p0578 p0579
  have p0581 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
            (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
        (.classEq (.cv z) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A) p0580
  have p0582 :=
    @g_rspcedv
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv z)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv x)))
      z (.cv x)
      (syn_cfv (syn_c2nd)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0577 p0581
  have p0583 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (.cv x)))
      (syn_wrex z (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (.cv z))))
      p0542 p0582
  have p0584 :=
    @g_olc
      (syn_wrex z (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (.cv z))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
  have p0585 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wrex z (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (.cv z))))
      (syn_wo (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wrex z (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv y))) (.cv z)))))
      p0583 p0584
  have p0609 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0446 p0441
  have p0610 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chwcn A))
      p0466 p0609
  have p0611 :=
    @g_hncodecmpsetstrictcutsemclndv z A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      dv_cache_0008 dv_cache_0010 dv_cache_0009
  have p0612 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
          (syn_chwcn A)))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wo (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_wrex z (syn_cfv (syn_c2nd)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv y))) (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (syn_cfv (syn_c2nd)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u)) (.cv y))) (.cv z))))))
      p0610 p0611
  have p0613 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wo (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wrex z (syn_cfv (syn_c2nd)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv y))) (syn_cfv (syn_c2nd)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv y))) (.cv z)))))
      p0585 p0612
  have p0614 :=
    @g_ex
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wne (.cv x) (.cv y))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0613
  have p0615 :=
    @g_pm2_61dne
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (.cv x) (.cv y) p0445 p0614
  have p0616 :=
    @g_ex
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      p0615
  have p0617 :=
    @g_impbid
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)) p0420 p0616
  exact p0617


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part072`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutcodecmpbrclndv (u : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
          (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
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
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ u from (by exact fresh_x_ne_u)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ y } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show y ≠ u from (by exact fresh_y_ne_u)))))))),
                  (show Disjoint (({ y } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
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
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
            (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          Finset.mem_union, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_u,
          fresh_y_ne_x, fresh_y_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0009 :
    x ∉
      ((Wff.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv))
              (syn_wa (.classMem (.cv u) (syn_chwcn A))
                (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
                  (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
                (syn_chncodecmpset A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
              (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_C, fresh_x_ne_u,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_id
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
  have p0001 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))
  have p0002 :=
    @g_simprd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem C (syn_cfv (syn_c2nd) (.cv u))))
      p0001
  have p0003 :=
    @g_simprd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0002
  have p0006 :=
    @g_simpld
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0002
  have p0007 := @g_elex B (syn_cfv (syn_c2nd) (.cv u))
  have p0008 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem B (syn_cfv (syn_c2nd) (.cv u))) (.classMem B (syn_cvv)) p0006 p0007
  have p0009 := @g_biid (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
  have p0010 :=
    @g_a1i
      (syn_wb (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem C (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv x) B) p0009
  have p0011 := @g_biid (.classMem A (syn_cvv))
  have p0012 :=
    @g_a1i (syn_wb (.classMem A (syn_cvv)) (.classMem A (syn_cvv))) (.classEq (.cv x) B)
      p0011
  have p0013 := @g_biid (.classMem (.cv u) (syn_chwcn A))
  have p0014 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv x) B) p0013
  have p0015 := @g_id (.classEq (.cv x) B)
  have p0016 :=
    @g_eleq1d (.classEq (.cv x) B) (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) p0015
  have p0019 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0016 p0010
  have p0020 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem C (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem C (syn_cfv (syn_c2nd) (.cv u))))
      p0014 p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem A (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))
      p0012 p0020
  have p0022 :=
    @g_hnwcutcodeeq3 (.cv x) B (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      dv_cache_0001
  have p0023 :=
    @g_breq1d (.classEq (.cv x) B)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)
      (syn_chncodecmpset A) p0022
  have p0025 :=
    @g_breq1d (.classEq (.cv x) B) (.cv x) B C (syn_cfv (syn_c1st) (.cv u)) p0015
  have p0026 :=
    @g_bibi12d (.classEq (.cv x) B)
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
        (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)
      (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C) p0023 p0025
  have p0027 :=
    @g_imbi12d (.classEq (.cv x) B)
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
        (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))
      p0021 p0026
  have p0028 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)))
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
          (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C)))
      p0010 p0027
  have p0029 := @g_elex C (syn_cfv (syn_c2nd) (.cv u))
  have p0031 :=
    @g_a1i (syn_wb (.classMem A (syn_cvv)) (.classMem A (syn_cvv))) (.classEq (.cv y) C)
      p0011
  have p0033 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv y) C) p0013
  have p0034 := @g_biid (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0035 :=
    @g_a1i
      (syn_wb (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv y) C) p0034
  have p0036 := @g_id (.classEq (.cv y) C)
  have p0037 :=
    @g_eleq1d (.classEq (.cv y) C) (.cv y) C (syn_cfv (syn_c2nd) (.cv u)) p0036
  have p0038 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u))) p0035 p0037
  have p0039 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem C (syn_cfv (syn_c2nd) (.cv u))))
      p0033 p0038
  have p0040 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem A (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))
      p0031 p0039
  have p0041 :=
    @g_hnwcutcodeeq3 (.cv y) C (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      dv_cache_0002
  have p0042 :=
    @g_breq2d (.classEq (.cv y) C)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chncodecmpset A) p0041
  have p0044 :=
    @g_breq2d (.classEq (.cv y) C) (.cv y) C (.cv x) (syn_cfv (syn_c1st) (.cv u)) p0036
  have p0045 :=
    @g_bibi12d (.classEq (.cv y) C)
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))
      (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C) p0042 p0044
  have p0046 :=
    @g_imbi12d (.classEq (.cv y) C)
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y)))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
        (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C))
      p0040 p0045
  have p0047 := @g_hnwcutcodecmpbrndv x y u A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0048 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem (.cv y) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) (.cv y))))
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)))
      y C (syn_cvv) dv_cache_0006 dv_cache_0007 p0046 p0047
  have p0049 :=
    @g_syl (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.classMem C (syn_cvv))
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
          (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C)))
      p0029 p0048
  have p0050 :=
    @g_vtoclg
      (.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
            (syn_wbr (.cv x) (syn_cfv (syn_c1st) (.cv u)) C))))
      (.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
              (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
            (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))))
      x B (syn_cvv) dv_cache_0008 dv_cache_0009 p0028 p0049
  have p0051 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem B (syn_cvv))
      (.imp (.classMem C (syn_cfv (syn_c2nd) (.cv u))) (.imp (syn_wa (.classMem A (syn_cvv))
            (syn_wa (.classMem (.cv u) (syn_chwcn A))
              (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
                (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
              (syn_chncodecmpset A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
            (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))))
      p0008 p0050
  have p0052 :=
    @g_mpd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem C (syn_cfv (syn_c2nd) (.cv u)))
      (.imp (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
              (.classMem C (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wb (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
            (syn_chncodecmpset A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
          (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C)))
      p0003 p0051
  have p0053 :=
    @g_mpd
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem B (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem C (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) B)
          (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) C))
        (syn_wbr B (syn_cfv (syn_c1st) (.cv u)) C))
      p0000 p0052
  exact p0053

@[expose]
noncomputable def g_pw12si2brndv (D : Class) (R : Class) (q : Var) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
        (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi R)) (.cv q))
          (syn_wbr (syn_cuni (syn_cuni (.cv p))) R (syn_cuni (syn_cuni (.cv q)))))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv := by
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv p)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((syn_cuni (.cv p))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv p)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ (R).fv from (by exact dv_R_p))))))))))
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0001 := @g_pw12argcl (.cv p) D
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) D)
        (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))))
      p0000 p0001
  have p0003 :=
    @g_simprd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv p))) D)
      (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0002
  have p0004 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0005 := @g_pw12argcl (.cv q) D
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @g_simprd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_breq12d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))) (.cv q)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csi (syn_csi R)) p0003 p0007
  have p0009 := @g_snex (syn_cuni (syn_cuni (.cv p)))
  have p0010 := @g_snex (syn_cuni (syn_cuni (.cv q)))
  have p0011 :=
    @g_brsnsi (syn_csn (syn_cuni (syn_cuni (.cv p))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csi R) p0009 p0010
  have p0012 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))) (syn_csi (syn_csi R))
          (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
        (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csi R)
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      p0011
  have p0014 := @g_elex (.cv p) (syn_cpw1 (syn_cpw1 D))
  have p0015 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv p) (syn_cvv)) p0000
      p0014
  have p0016 := @g_uniexg (.cv p) (syn_cvv)
  have p0017 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv p) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0015 p0016
  have p0018 := @g_uniexg (syn_cuni (.cv p)) (syn_cvv)
  have p0019 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (.cv p)) (syn_cvv))
      (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cvv)) p0017 p0018
  have p0021 := @g_elex (.cv q) (syn_cpw1 (syn_cpw1 D))
  have p0022 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv q) (syn_cvv)) p0004
      p0021
  have p0023 := @g_uniexg (.cv q) (syn_cvv)
  have p0024 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv q) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0022 p0023
  have p0025 := @g_uniexg (syn_cuni (.cv q)) (syn_cvv)
  have p0026 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) p0024 p0025
  have p0027 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cvv))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)) p0019 p0026
  have p0028 :=
    @g_brsnsiandv (syn_cuni (syn_cuni (.cv p))) (syn_cuni (syn_cuni (.cv q))) R
      dv_cache_0001
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cvv))
        (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv)))
      (syn_wb (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csi R)
          (syn_csn (syn_cuni (syn_cuni (.cv q)))))
        (syn_wbr (syn_cuni (syn_cuni (.cv p))) R (syn_cuni (syn_cuni (.cv q)))))
      p0027 p0028
  have p0030 :=
    @g_n_3bitrd
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv p) (syn_csi (syn_csi R)) (.cv q))
      (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p))))) (syn_csi (syn_csi R))
        (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv p)))) (syn_csi R)
        (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_wbr (syn_cuni (syn_cuni (.cv p))) R (syn_cuni (syn_cuni (.cv q)))) p0008 p0012
      p0029
  exact p0030


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part073`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isostrictsegresclndv (B : Class) (D : Class) (R : Class) (S : Class)
    (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
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
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((Wff.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
              (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
            (syn_cin S (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
                (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_E, fresh_x_not_H, fresh_x_not_R, fresh_x_not_S,
          fresh_x_not_B, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (syn_wa (syn_wiso H R S D E) (.classMem B D))
  have p0001 := @g_simpr (syn_wiso H R S D E) (.classMem B D)
  have p0002 := @g_elex B D
  have p0003 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem B D)) (.classMem B D)
      (.classMem B (syn_cvv)) p0001 p0002
  have p0004 := @g_biid (syn_wiso H R S D E)
  have p0005 :=
    @g_a1i (syn_wb (syn_wiso H R S D E) (syn_wiso H R S D E)) (.classEq (.cv x) B) p0004
  have p0006 := @g_id (.classEq (.cv x) B)
  have p0007 := @g_eleq1d (.classEq (.cv x) B) (.cv x) B D p0006
  have p0008 :=
    @g_anbi12d (.classEq (.cv x) B) (syn_wiso H R S D E) (syn_wiso H R S D E)
      (.classMem (.cv x) D) (.classMem B D) p0005 p0007
  have p0010 := @g_sneqd (.classEq (.cv x) B) (.cv x) B p0006
  have p0011 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B)
      (syn_ccnv (syn_cdif R (syn_cid))) p0010
  have p0012 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0011
  have p0013 :=
    @g_reseq2d (.classEq (.cv x) B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) H p0012
  have p0014 :=
    @g_isoeq1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0015 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
        (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0013 p0014
  have p0024 :=
    @g_xpeq12d (.classEq (.cv x) B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0012 p0012
  have p0025 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      R p0024
  have p0026 :=
    @g_isoeq2 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0027 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
        (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0025 p0026
  have p0028 :=
    @g_bitrd (.classEq (.cv x) B)
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0015 p0027
  have p0030 := @g_fveq2d (.classEq (.cv x) B) (.cv x) B H p0006
  have p0031 := @g_sneqd (.classEq (.cv x) B) (syn_cfv H (.cv x)) (syn_cfv H B) p0030
  have p0032 :=
    @g_imaeq2d (.classEq (.cv x) B) (syn_csn (syn_cfv H (.cv x))) (syn_csn (syn_cfv H B))
      (syn_ccnv (syn_cdif S (syn_cid))) p0031
  have p0033 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))) E p0032
  have p0039 :=
    @g_xpeq12d (.classEq (.cv x) B)
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
      p0033 p0033
  have p0040 :=
    @g_ineq2d (.classEq (.cv x) B)
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))
      S p0039
  have p0041 :=
    @g_isoeq3 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin S (syn_cxp (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
          (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0042 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
        (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0040 p0041
  have p0043 :=
    @g_bitrd (.classEq (.cv x) B)
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0028 p0042
  have p0048 :=
    @g_isoeq4 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0049 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
        (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      p0012 p0048
  have p0050 :=
    @g_bitrd (.classEq (.cv x) B)
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      p0043 p0049
  have p0056 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
      (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
      (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
  have p0057 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))
      (syn_wb (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
        (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
      p0033 p0056
  have p0058 :=
    @g_bitrd (.classEq (.cv x) B)
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))
      p0050 p0057
  have p0059 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D))
      (syn_wa (syn_wiso H R S D E) (.classMem B D))
      (syn_wiso (syn_cres H
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                (syn_csn (syn_cfv H (.cv x)))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x))))))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))
      p0008 p0058
  have p0060 := @g_isostrictsegresndv x D R S E H
  have p0061 :=
    @g_vtoclg
      (.imp (syn_wa (syn_wiso H R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                  (syn_csn (syn_cfv H (.cv x))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H (.cv x)))))))
      (.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
      x B (syn_cvv) dv_cache_0001 dv_cache_0002 p0059 p0060
  have p0062 :=
    @g_syl (syn_wa (syn_wiso H R S D E) (.classMem B D)) (.classMem B (syn_cvv))
      (.imp (syn_wa (syn_wiso H R S D E) (.classMem B D)) (syn_wiso (syn_cres H
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))) (syn_cin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
            (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
      p0003 p0061
  have p0063 :=
    @g_mpd (syn_wa (syn_wiso H R S D E) (.classMem B D))
      (syn_wa (syn_wiso H R S D E) (.classMem B D))
      (syn_wiso
        (syn_cres H (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
        (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S
          (syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv H B)))))
      p0000 p0062
  exact p0063

@[expose]
noncomputable def g_hnsiquomappreexclndv (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_hnsiquomappreexclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chnord (syn_cpw1 A))) (syn_wrex x (syn_cpw1 (syn_chnord A))
          (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
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
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0006 : y ∉ ((syn_chnord (syn_cpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((syn_wrex x (syn_cpw1 (syn_chnord A))
          (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv y) B)
  have p0001 :=
    @g_eqeq1d (.classEq (.cv y) B) (.cv y) B (syn_cfv (syn_chnsiquomap A) (.cv x)) p0000
  have p0002 :=
    @g_rexbidv (.classEq (.cv y) B)
      (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x)))
      (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))) x (syn_cpw1 (syn_chnord A))
      dv_cache_0001 p0001
  have p0003 :=
    @g_hnsiquomappreexndv x y A dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_hnsiquomappreexclndv_1
  have p0004 :=
    @g_vtoclga
      (syn_wrex x (syn_cpw1 (syn_chnord A))
        (.classEq (.cv y) (syn_cfv (syn_chnsiquomap A) (.cv x))))
      (syn_wrex x (syn_cpw1 (syn_chnord A)) (.classEq B (syn_cfv (syn_chnsiquomap A) (.cv x))))
      y B (syn_chnord (syn_cpw1 A)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_hnsiquomaprepvalcl2ndv (A : Class) (C : Class) (q : Var)
    (dv_A_q : q ∉ A.fv)
    (hyp_hnsiquomaprepvalcl2ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ ({ q } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_u : q ≠ u := Ne.symm fresh_u_ne_q
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0004 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0005 :
    u ∉
      ((Wff.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (syn_wa (.classMem C (syn_chwcn A))
              (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
          (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
            (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C))
              (syn_chwniso (syn_cpw1 A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, fresh_u_not_C, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem C (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))
  have p0001 :=
    @g_simpl (.classMem C (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
      (syn_wa (.classMem C (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))
      (.classMem C (syn_chwcn A)) p0000 p0001
  have p0003 := @g_elex C (syn_chwcn A)
  have p0004 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
      (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_biidd (.classEq (.cv u) C) (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
  have p0006 := @g_id (.classEq (.cv u) C)
  have p0007 := @g_eleq1d (.classEq (.cv u) C) (.cv u) C (syn_chwcn A) p0006
  have p0008 := @g_eceq1 (.cv u) C (syn_chwniso A)
  have p0009 :=
    @g_eqeq2d (.classEq (.cv u) C) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec C (syn_chwniso A)) (syn_cuni (.cv q)) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv u) C) (.classMem (.cv u) (syn_chwcn A))
      (.classMem C (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
      (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))) p0007 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv u) C) (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wa (.classMem C (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))
      p0005 p0010
  have p0013 := @g_sneqd (.classEq (.cv u) C) (.cv u) C p0006
  have p0014 :=
    @g_fveq2d (.classEq (.cv u) C) (syn_csn (.cv u)) (syn_csn C) (syn_chnsicodemap A)
      p0013
  have p0015 :=
    @g_eceq1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))
  have p0016 :=
    @g_syl (.classEq (.cv u) C)
      (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
        (syn_cfv (syn_chnsicodemap A) (syn_csn C)))
      (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
          (syn_chwniso (syn_cpw1 A)))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))
      p0014 p0015
  have p0017 :=
    @g_eqeq2d (.classEq (.cv u) C)
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))
      (syn_cfv (syn_chnsiquomap A) (.cv q)) p0016
  have p0018 :=
    @g_imbi12d (.classEq (.cv u) C)
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))
      p0011 p0017
  have p0019 :=
    @g_hnsiquomaprepvalndv u A q dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnsiquomaprepvalcl2ndv_1
  have p0020 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u)))
            (syn_chwniso (syn_cpw1 A)))))
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))
      u C (syn_cvv) dv_cache_0004 dv_cache_0005 p0018 p0019
  have p0021 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
      (.classMem C (syn_cvv))
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))
      p0004 p0020
  have p0022 :=
    @g_pm2_43i
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))
      p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
