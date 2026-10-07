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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodecmpbrndv`. -/
@[expose]
noncomputable def gHnwcutcodecmpbrndv (x : Var) (y : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))) :=
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
  have dv_cache_0001 : Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                  (show Disjoint (({ y } : Finset Var)) (((synC1st)).fv) from
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
      ((synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((Class.cv z)).fv ((synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var))
                ((((synChnwcutcode (synCfv (synC1st) (.cv u))
                      (synCfv (synC2nd) (.cv u)) (.cv x))).fv) ∪
                  (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show
                    Disjoint (({ z } : Finset Var))
                      (((synChnwcutcode (synCfv (synC1st) (.cv u))
                          (synCfv (synC2nd) (.cv u)) (.cv x))).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode];
                      exact
                        (show
                          Disjoint (({ z } : Finset Var))
                            ((((Class.cv x)).fv) ∪ (((synCfv (synC2nd) (.cv u))).fv) ∪
                              (((synCfv (synC1st) (.cv u))).fv))
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
                                      (((synCfv (synC2nd) (.cv u))).fv)
                                    from
                                    (by
                                      rw [fv_syn_cfv];
                                      exact
                                        (show
                                          Disjoint (({ z } : Finset Var))
                                            ((((Class.cv u)).fv) ∪ (((synC2nd)).fv))
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
                                                  (((synC2nd)).fv)
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
                                  (((synCfv (synC1st) (.cv u))).fv)
                                from
                                (by
                                  rw [fv_syn_cfv];
                                  exact
                                    (show
                                      Disjoint (({ z } : Finset Var))
                                        ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                                              (((synC1st)).fv)
                                            from
                                            (by
                                              rw [fv_syn_c1st];
                                              exact
                                                (show
                                                  Disjoint (({ z } : Finset Var))
                                                    ((∅ : Finset Var))
                                                  from (by simp))))⟩))))⟩)))),
                  (show Disjoint (({ z } : Finset Var)) (((synC1st)).fv) from
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
      ((synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
            (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
          (synWne (.cv y) (.cv x)))).fv :=
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
      ((synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
  have dv_cache_0011 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0012 :
    Disjoint ((Class.cv z)).fv
      ((synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint ((Class.cv z)).fv ((synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv, fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var))
                ((((synChnwcutcode (synCfv (synC1st) (.cv u))
                      (synCfv (synC2nd) (.cv u)) (.cv y))).fv) ∪
                  (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show
                    Disjoint (({ z } : Finset Var))
                      (((synChnwcutcode (synCfv (synC1st) (.cv u))
                          (synCfv (synC2nd) (.cv u)) (.cv y))).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode];
                      exact
                        (show
                          Disjoint (({ z } : Finset Var))
                            ((((Class.cv y)).fv) ∪ (((synCfv (synC2nd) (.cv u))).fv) ∪
                              (((synCfv (synC1st) (.cv u))).fv))
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
                                      (((synCfv (synC2nd) (.cv u))).fv)
                                    from
                                    (by
                                      rw [fv_syn_cfv];
                                      exact
                                        (show
                                          Disjoint (({ z } : Finset Var))
                                            ((((Class.cv u)).fv) ∪ (((synC2nd)).fv))
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
                                                  (((synC2nd)).fv)
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
                                  (((synCfv (synC1st) (.cv u))).fv)
                                from
                                (by
                                  rw [fv_syn_cfv];
                                  exact
                                    (show
                                      Disjoint (({ z } : Finset Var))
                                        ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                                              (((synC1st)).fv)
                                            from
                                            (by
                                              rw [fv_syn_c1st];
                                              exact
                                                (show
                                                  Disjoint (({ z } : Finset Var))
                                                    ((∅ : Finset Var))
                                                  from (by simp))))⟩))))⟩)))),
                  (show Disjoint (({ z } : Finset Var)) (((synC1st)).fv) from
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
      ((synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
            (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
          (synWne (.cv x) (.cv y)))).fv :=
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
  have p0000 := @gId (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
  have p0001 :=
    @gA1i
      (.imp (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classEq (.cv x) (.cv y))
  have p0003 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
  have p0004 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      p0003 p0004
  have p0006 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (.classEq (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      p0002 p0005
  have p0007 :=
    @gSimpr (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))
  have p0008 :=
    @gSimpld
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      p0007
  have p0009 := @gHwcnweclndv A (.cv u)
  have p0010 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0008
      p0009
  have p0011 := @gWppweref (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0012 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCref) (synCfv (synC2nd) (.cv u))) p0010
      p0011
  have p0014 :=
    @gSimprd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      p0007
  have p0015 :=
    @gSimpld
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0014
  have p0016 :=
    @gRefd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) (.cv x) p0012 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (.classEq (.cv x) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv x)) p0006 p0016
  have p0018 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classEq (.cv x) (.cv y))
  have p0019 :=
    @gBreqtrd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (.classEq (.cv x) (.cv y)))
      (.cv x) (.cv x) (.cv y) (synCfv (synC1st) (.cv u)) p0017 p0018
  have p0020 :=
    @gEx
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classEq (.cv x) (.cv y)) (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
      p0019
  have p0021 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv x) (.cv y))
  have p0023 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0003 p0023
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0021 p0024
  have p0027 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) p0021 p0027
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      p0021 p0005
  have p0034 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classEq (.cv y) (.cv x))
  have p0035 :=
    @gHnwcutcodeeq3 (.cv y) (.cv x) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) dv_cache_0001
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (.classEq (.cv y) (.cv x))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)))
      p0034 p0035
  have p0037 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classEq (.cv y) (.cv x))
  have p0038 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
  have p0039 :=
    @gSimpl (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))
  have p0040 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem A (synCvv)) p0038 p0039
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem A (synCvv)) p0037 p0040
  have p0042 := @gHncodecmpsetrefndv A
  have p0043 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      p0041 p0042
  have p0051 :=
    @gJca
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      p0008 p0015
  have p0052 := @gHnwcutcodeambientndv x u A dv_cache_0002
  have p0053 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0051 p0052
  have p0054 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0038 p0053
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0037 p0054
  have p0056 :=
    @gRefd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (synChwcn A) (synChncodecmpset A)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      p0043 p0055
  have p0057 :=
    @gEqbrtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (.classEq (.cv y) (.cv x)))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChncodecmpset A) p0036 p0056
  have p0058 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classEq (.cv y) (.cv x))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0057
  have p0059 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv y) (.cv x))
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem A (synCvv)) p0059 p0040
  have p0064 := @gHwnisoerv A
  have p0065 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synCvv)) p0063 p0064
  have p0066 := @gHwnisodm A
  have p0067 :=
    @gA1i (.classEq (synCdm (synChwniso A)) (synChwcn A))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      p0066
  have p0074 :=
    @gSimprd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0014
  have p0075 :=
    @gJca
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      p0008 p0074
  have p0076 := @gHnwcutcodeambientndv y u A dv_cache_0002
  have p0077 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0075 p0076
  have p0078 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0038 p0077
  have p0079 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0059 p0078
  have p0080 :=
    @gErref
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synChwcn A) (synChwniso A)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      p0065 p0067 p0079
  have p0085 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A)) p0038 p0008
  have p0086 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem (.cv u) (synChwcn A)) p0059 p0085
  have p0092 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0038 p0015
  have p0093 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0059 p0092
  have p0094 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      p0086 p0093
  have p0095 := @gHnwcutcodepartsndv x u A dv_cache_0002
  have p0096 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      p0094 p0095
  have p0097 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0096
  have p0114 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0096
  have p0115 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0097 p0114
  have p0116 :=
    @gHnwcutcodeeq12ndv y
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
  have p0117 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)) (synChnwcutcode (synCin (synCfv (synC1st) (.cv u)) (synCxp
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (.cv y)))
      p0115 p0116
  have p0124 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0038
      p0010
  have p0125 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0059
      p0124
  have p0133 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0125 p0093
  have p0139 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0038 p0074
  have p0140 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0059 p0139
  have p0142 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
  have p0143 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) p0059 p0142
  have p0144 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv y) (.cv x))
  have p0145 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) (synWne (.cv y) (.cv x))
      p0143 p0144
  have p0146 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      (synWa (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) (synWne (.cv y) (.cv x)))
      p0140 p0145
  have p0147 :=
    @gElstrictseg x y (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0148 :=
    @gA1i
      (synWb (.classMem (.cv y) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))) (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
          (synWa (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
            (synWne (.cv y) (.cv x)))))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      p0147
  have p0149 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem (.cv y) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWa (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
          (synWne (.cv y) (.cv x))))
      p0146 p0148
  have p0150 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv y) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0133 p0149
  have p0151 :=
    @gHnwcutcodenestndv y x (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0152 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa
          (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classMem (.cv y)
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (synChnwcutcode (synCin (synCfv (synC1st) (.cv u)) (synCxp
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv x)))) (.cv y))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0150 p0151
  have p0153 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.cv y))
      (synChnwcutcode (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      p0117 p0152
  have p0154 :=
    @gBreq2d
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChwniso A) p0153
  have p0155 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0080 p0154
  have p0189 :=
    @gEleq2d
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv x))))
      (.cv y) p0114
  have p0190 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem (.cv y) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem (.cv y) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv x)))))
      p0149 p0189
  have p0191 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classEq (.cv z) (.cv y))
  have p0192 :=
    @gHnwcutcodeeq3 (.cv z) (.cv y)
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      dv_cache_0003
  have p0193 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
            (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
        (.classEq (.cv z) (.cv y)))
      (.classEq (.cv z) (.cv y))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv z)) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)))
      p0191 p0192
  have p0194 :=
    @gBreq2d
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
            (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
        (.classEq (.cv z) (.cv y)))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.cv z))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChwniso A) p0193
  have p0195 :=
    @gRspcedv
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv z)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)))
      z (.cv y)
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0190 p0194
  have p0196 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)))
      (synWrex z (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.cv z))))
      p0155 p0195
  have p0197 :=
    @gOlc
      (synWrex z (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.cv z))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
  have p0198 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWrex z (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.cv z))))
      (synWo (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWrex z (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x))) (.cv z)))))
      p0196 p0197
  have p0222 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0059 p0054
  have p0223 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0079 p0222
  have p0224 :=
    @gHncodecmpsetstrictcutsemclndv z A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0225 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWa (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
          (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWo (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synWrex z (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                  (synChnwcutcode (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u)) (.cv x))) (synCfv (synC2nd)
                  (synChnwcutcode (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u)) (.cv x))) (.cv z))))))
      p0223 p0224
  have p0226 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWo (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synWrex z (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x))) (.cv z)))))
      p0198 p0225
  have p0227 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv y) (.cv x))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0226
  have p0228 :=
    @gPm261dne
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (.cv y) (.cv x) p0058 p0227
  have p0229 :=
    @gEx
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0228
  have p0230 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.imp (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0033 p0229
  have p0231 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0028 p0230
  have p0232 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0025 p0231
  have p0233 :=
    @gBrlnker (synChncodecmpset A)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
  have p0234 :=
    @gBiimpri
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synClnker (synChncodecmpset A))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWa (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)) (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0233
  have p0235 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv y)) (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synClnker (synChncodecmpset A))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0232 p0234
  have p0242 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem A (synCvv)) p0033 p0039
  have p0243 := @gHncodecmplnkerndv A
  have p0244 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (.classMem A (synCvv))
      (.classEq (synClnker (synChncodecmpset A)) (synChwniso A)) p0242 p0243
  have p0245 :=
    @gBreqd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synClnker (synChncodecmpset A)) (synChwniso A)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      p0244
  have p0246 :=
    @gBiimpd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synClnker (synChncodecmpset A))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0245
  have p0247 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synClnker (synChncodecmpset A))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0235 p0246
  have p0256 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) p0033 p0028
  have p0257 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv x) (.cv y))
  have p0258 :=
    @gNecomd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0257
  have p0259 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv y) (.cv x)) p0256 p0258
  have p0333 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)) (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)))
      p0259 p0153
  have p0334 :=
    @gBreqtrrd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.cv y))
      (synChwniso A) p0247 p0333
  have p0348 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0033 p0053
  have p0396 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))) (synWne (.cv y) (.cv x)))
      (.classMem (.cv y) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0259 p0190
  have p0397 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (.cv y) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0348 p0396
  have p0398 :=
    @gHnwcutcodeselfnoisoclndv y A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
  have p0399 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWa (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)) (.classMem (.cv y) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      (.neg (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.cv y))))
      p0397 p0398
  have p0400 :=
    @gPm221dd
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
        (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.cv y)))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) p0334 p0399
  have p0401 :=
    @gEx
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWne (.cv x) (.cv y)) (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
      p0400
  have p0402 :=
    @gPm261dne
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))) (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) (.cv x) (.cv y) p0020 p0401
  have p0403 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) p0402
  have p0409 := @gWppweconnex (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0410 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCconnex) (synCfv (synC2nd) (.cv u)))
      p0010 p0409
  have p0417 :=
    @gConnexd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) (.cv x) (.cv y) p0410
      p0015 p0074
  have p0418 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWo (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
        (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)))
      p0004 p0417
  have p0419 :=
    @gMpjaod
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
      (synWbr (.cv y) (synCfv (synC1st) (.cv u)) (.cv x)) p0001 p0403 p0418
  have p0420 :=
    @gEx
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) p0419
  have p0421 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classEq (.cv x) (.cv y))
  have p0422 :=
    @gHnwcutcodeeq3 (.cv x) (.cv y) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) dv_cache_0011
  have p0423 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (.classEq (.cv x) (.cv y))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)))
      p0421 p0422
  have p0424 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classEq (.cv x) (.cv y))
  have p0425 :=
    @gSimpl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
  have p0427 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem A (synCvv)) p0425 p0039
  have p0428 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem A (synCvv)) p0424 p0427
  have p0430 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      p0428 p0042
  have p0441 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0425 p0077
  have p0442 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0424 p0441
  have p0443 :=
    @gRefd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (synChwcn A) (synChncodecmpset A)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      p0430 p0442
  have p0444 :=
    @gEqbrtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (.classEq (.cv x) (.cv y)))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChncodecmpset A) p0423 p0443
  have p0445 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classEq (.cv x) (.cv y))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0444
  have p0446 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWne (.cv x) (.cv y))
  have p0450 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem A (synCvv)) p0446 p0427
  have p0452 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synCvv)) p0450 p0064
  have p0454 :=
    @gA1i (.classEq (synCdm (synChwniso A)) (synChwcn A))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      p0066
  have p0465 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0425 p0053
  have p0466 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0446 p0465
  have p0467 :=
    @gErref
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synChwcn A) (synChwniso A)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      p0452 p0454 p0466
  have p0472 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A)) p0425 p0008
  have p0473 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem (.cv u) (synChwcn A)) p0446 p0472
  have p0479 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0425 p0074
  have p0480 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0446 p0479
  have p0481 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      p0473 p0480
  have p0482 := @gHnwcutcodepartsndv y u A dv_cache_0002
  have p0483 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y))))))
      p0481 p0482
  have p0484 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))))
      p0483
  have p0501 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))))
      p0483
  have p0502 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))))
      p0484 p0501
  have p0503 :=
    @gHnwcutcodeeq12ndv x
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y))))))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv y))))
  have p0504 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCin (synCfv (synC1st) (.cv u)) (synCxp (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y))))))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv x)) (synChnwcutcode (synCin (synCfv (synC1st) (.cv u)) (synCxp
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y)))) (.cv x)))
      p0502 p0503
  have p0511 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0425
      p0010
  have p0512 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0446
      p0511
  have p0520 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0512 p0480
  have p0526 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0425 p0015
  have p0527 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0446 p0526
  have p0529 :=
    @gSimpr
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
  have p0530 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) p0446 p0529
  have p0531 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWne (.cv x) (.cv y))
  have p0532 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) (synWne (.cv x) (.cv y))
      p0530 p0531
  have p0533 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (synWa (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) (synWne (.cv x) (.cv y)))
      p0527 p0532
  have p0534 :=
    @gElstrictseg y x (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0535 :=
    @gA1i
      (synWb (.classMem (.cv x) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y))))) (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
          (synWa (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
            (synWne (.cv x) (.cv y)))))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      p0534
  have p0536 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (synWa (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
          (synWne (.cv x) (.cv y))))
      p0533 p0535
  have p0537 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))))
      p0520 p0536
  have p0538 :=
    @gHnwcutcodenestndv x y (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
  have p0539 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa
          (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))) (.classMem (.cv x)
          (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y))))))
      (.classEq (synChnwcutcode (synCin (synCfv (synC1st) (.cv u)) (synCxp
              (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                  (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv u))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
              (synCsn (.cv y)))) (.cv x))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0537 p0538
  have p0540 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (.cv x))
      (synChnwcutcode (synCin (synCfv (synC1st) (.cv u)) (synCxp
            (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv u))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
                (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      p0504 p0539
  have p0541 :=
    @gBreq2d
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0540
  have p0542 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0467 p0541
  have p0576 :=
    @gEleq2d
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synCin (synCfv (synC2nd) (.cv u))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
          (synCsn (.cv y))))
      (.cv x) p0501
  have p0577 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (.classMem (.cv x) (synCin (synCfv (synC2nd) (.cv u))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv u)) (synCid)))
            (synCsn (.cv y)))))
      p0536 p0576
  have p0578 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classEq (.cv z) (.cv x))
  have p0579 :=
    @gHnwcutcodeeq3 (.cv z) (.cv x)
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      dv_cache_0012
  have p0580 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
            (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
        (.classEq (.cv z) (.cv x)))
      (.classEq (.cv z) (.cv x))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv z)) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv x)))
      p0578 p0579
  have p0581 :=
    @gBreq2d
      (synWa (synWa (synWa (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                  (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
            (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
        (.classEq (.cv z) (.cv x)))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (.cv z))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0580
  have p0582 :=
    @gRspcedv
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv z)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv x)))
      z (.cv x)
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0577 p0581
  have p0583 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.cv x)))
      (synWrex z (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (.cv z))))
      p0542 p0582
  have p0584 :=
    @gOlc
      (synWrex z (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (.cv z))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
  have p0585 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWrex z (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (.cv z))))
      (synWo (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWrex z (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv y))) (.cv z)))))
      p0583 p0584
  have p0609 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0446 p0441
  have p0610 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChwcn A))
      p0466 p0609
  have p0611 :=
    @gHncodecmpsetstrictcutsemclndv z A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      dv_cache_0008 dv_cache_0010 dv_cache_0009
  have p0612 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWa (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
          (synChwcn A)))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWo (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synWrex z (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))) (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                  (synChnwcutcode (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u)) (.cv y))) (synCfv (synC2nd)
                  (synChnwcutcode (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u)) (.cv y))) (.cv z))))))
      p0610 p0611
  have p0613 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))) (synWne (.cv x) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWo (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWrex z (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv y))) (.cv z)))))
      p0585 p0612
  have p0614 :=
    @gEx
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWne (.cv x) (.cv y))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0613
  have p0615 :=
    @gPm261dne
      (synWa (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (.cv x) (.cv y) p0445 p0614
  have p0616 :=
    @gEx
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      p0615
  have p0617 :=
    @gImpbid
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)) p0420 p0616
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodecmpbrclndv`. -/
@[expose]
noncomputable def gHnwcutcodecmpbrclndv (u : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
              (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
          (synWbr B (synCfv (synC1st) (.cv u)) C))) :=
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
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                  (show Disjoint (({ y } : Finset Var)) (((synC1st)).fv) from
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
      ((Wff.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
            (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C)))).fv :=
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
      ((Wff.imp (.classMem C (synCfv (synC2nd) (.cv u))) (.imp (synWa (.classMem A (synCvv))
              (synWa (.classMem (.cv u) (synChwcn A))
                (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
                  (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
                (synChncodecmpset A)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
              (synWbr B (synCfv (synC1st) (.cv u)) C))))).fv :=
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
    @gId
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
  have p0001 :=
    @gSimpr (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
          (.classMem C (synCfv (synC2nd) (.cv u)))))
  have p0002 :=
    @gSimprd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
        (.classMem C (synCfv (synC2nd) (.cv u))))
      p0001
  have p0003 :=
    @gSimprd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (.classMem B (synCfv (synC2nd) (.cv u)))
      (.classMem C (synCfv (synC2nd) (.cv u))) p0002
  have p0006 :=
    @gSimpld
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (.classMem B (synCfv (synC2nd) (.cv u)))
      (.classMem C (synCfv (synC2nd) (.cv u))) p0002
  have p0007 := @gElex B (synCfv (synC2nd) (.cv u))
  have p0008 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (.classMem B (synCfv (synC2nd) (.cv u))) (.classMem B (synCvv)) p0006 p0007
  have p0009 := @gBiid (.classMem C (synCfv (synC2nd) (.cv u)))
  have p0010 :=
    @gA1i
      (synWb (.classMem C (synCfv (synC2nd) (.cv u)))
        (.classMem C (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv x) B) p0009
  have p0011 := @gBiid (.classMem A (synCvv))
  have p0012 :=
    @gA1i (synWb (.classMem A (synCvv)) (.classMem A (synCvv))) (.classEq (.cv x) B)
      p0011
  have p0013 := @gBiid (.classMem (.cv u) (synChwcn A))
  have p0014 :=
    @gA1i (synWb (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv x) B) p0013
  have p0015 := @gId (.classEq (.cv x) B)
  have p0016 :=
    @gEleq1d (.classEq (.cv x) B) (.cv x) B (synCfv (synC2nd) (.cv u)) p0015
  have p0019 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem B (synCfv (synC2nd) (.cv u)))
      (.classMem C (synCfv (synC2nd) (.cv u)))
      (.classMem C (synCfv (synC2nd) (.cv u))) p0016 p0010
  have p0020 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (.classMem C (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
        (.classMem C (synCfv (synC2nd) (.cv u))))
      p0014 p0019
  have p0021 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem A (synCvv)) (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
          (.classMem C (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
          (.classMem C (synCfv (synC2nd) (.cv u)))))
      p0012 p0020
  have p0022 :=
    @gHnwcutcodeeq3 (.cv x) B (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      dv_cache_0001
  have p0023 :=
    @gBreq1d (.classEq (.cv x) B)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C)
      (synChncodecmpset A) p0022
  have p0025 :=
    @gBreq1d (.classEq (.cv x) B) (.cv x) B C (synCfv (synC1st) (.cv u)) p0015
  have p0026 :=
    @gBibi12d (.classEq (.cv x) B)
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
        (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C)
      (synWbr B (synCfv (synC1st) (.cv u)) C) p0023 p0025
  have p0027 :=
    @gImbi12d (.classEq (.cv x) B)
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
        (synWbr B (synCfv (synC1st) (.cv u)) C))
      p0021 p0026
  have p0028 :=
    @gImbi12d (.classEq (.cv x) B) (.classMem C (synCfv (synC2nd) (.cv u)))
      (.classMem C (synCfv (synC2nd) (.cv u)))
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C)))
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
              (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
          (synWbr B (synCfv (synC1st) (.cv u)) C)))
      p0010 p0027
  have p0029 := @gElex C (synCfv (synC2nd) (.cv u))
  have p0031 :=
    @gA1i (synWb (.classMem A (synCvv)) (.classMem A (synCvv))) (.classEq (.cv y) C)
      p0011
  have p0033 :=
    @gA1i (synWb (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv y) C) p0013
  have p0034 := @gBiid (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0035 :=
    @gA1i
      (synWb (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv y) C) p0034
  have p0036 := @gId (.classEq (.cv y) C)
  have p0037 :=
    @gEleq1d (.classEq (.cv y) C) (.cv y) C (synCfv (synC2nd) (.cv u)) p0036
  have p0038 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      (.classMem C (synCfv (synC2nd) (.cv u))) p0035 p0037
  have p0039 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
        (.classMem C (synCfv (synC2nd) (.cv u))))
      p0033 p0038
  have p0040 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem A (synCvv)) (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
          (.classMem C (synCfv (synC2nd) (.cv u)))))
      p0031 p0039
  have p0041 :=
    @gHnwcutcodeeq3 (.cv y) C (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      dv_cache_0002
  have p0042 :=
    @gBreq2d (.classEq (.cv y) C)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChncodecmpset A) p0041
  have p0044 :=
    @gBreq2d (.classEq (.cv y) C) (.cv y) C (.cv x) (synCfv (synC1st) (.cv u)) p0036
  have p0045 :=
    @gBibi12d (.classEq (.cv y) C)
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))
      (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C) p0042 p0044
  have p0046 :=
    @gImbi12d (.classEq (.cv y) C)
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y)))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
        (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C))
      p0040 p0045
  have p0047 := @gHnwcutcodecmpbrndv x y u A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0048 :=
    @gVtoclg
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) (.cv y))))
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C)))
      y C (synCvv) dv_cache_0006 dv_cache_0007 p0046 p0047
  have p0049 :=
    @gSyl (.classMem C (synCfv (synC2nd) (.cv u))) (.classMem C (synCvv))
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
              (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
          (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C)))
      p0029 p0048
  have p0050 :=
    @gVtoclg
      (.imp (.classMem C (synCfv (synC2nd) (.cv u))) (.imp (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
                (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
            (synWbr (.cv x) (synCfv (synC1st) (.cv u)) C))))
      (.imp (.classMem C (synCfv (synC2nd) (.cv u))) (.imp (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
                (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
              (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
            (synWbr B (synCfv (synC1st) (.cv u)) C))))
      x B (synCvv) dv_cache_0008 dv_cache_0009 p0028 p0049
  have p0051 :=
    @gSyl
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (.classMem B (synCvv))
      (.imp (.classMem C (synCfv (synC2nd) (.cv u))) (.imp (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A))
              (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
                (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
              (synChncodecmpset A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
            (synWbr B (synCfv (synC1st) (.cv u)) C))))
      p0008 p0050
  have p0052 :=
    @gMpd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (.classMem C (synCfv (synC2nd) (.cv u)))
      (.imp (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
              (.classMem C (synCfv (synC2nd) (.cv u)))))) (synWb (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
            (synChncodecmpset A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
          (synWbr B (synCfv (synC1st) (.cv u)) C)))
      p0003 p0051
  have p0053 :=
    @gMpd
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem B (synCfv (synC2nd) (.cv u)))
            (.classMem C (synCfv (synC2nd) (.cv u))))))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) B)
          (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) C))
        (synWbr B (synCfv (synC1st) (.cv u)) C))
      p0000 p0052
  exact p0053

/-- Checked nominal proof certificate identified upstream as `g_pw12si2brndv`. -/
@[expose]
noncomputable def gPw12si2brndv (D : Class) (R : Class) (q : Var) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
          (.classMem (.cv q) (synCpw1 (synCpw1 D))))
        (synWb (synWbr (.cv p) (synCsi (synCsi R)) (.cv q))
          (synWbr (synCuni (synCuni (.cv p))) R (synCuni (synCuni (.cv q)))))) :=
  by
  have dv_cache_0001 : Disjoint ((synCuni (synCuni (.cv p)))).fv (R).fv := by
    exact
      (show Disjoint ((synCuni (synCuni (.cv p)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((synCuni (.cv p))).fv) ((R).fv) from
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
    @gSimpl (.classMem (.cv p) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0001 := @gPw12argcl (.cv p) D
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (.cv p) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv p))) D)
        (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))))
      p0000 p0001
  have p0003 :=
    @gSimprd
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv p))) D)
      (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))) p0002
  have p0004 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0005 := @gPw12argcl (.cv q) D
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv q))) D)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @gSimprd
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0008 :=
    @gBreq12d
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p))))) (.cv q)
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) (synCsi (synCsi R)) p0003 p0007
  have p0009 := @gSnex (synCuni (synCuni (.cv p)))
  have p0010 := @gSnex (synCuni (synCuni (.cv q)))
  have p0011 :=
    @gBrsnsi (synCsn (synCuni (synCuni (.cv p))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCsi R) p0009 p0010
  have p0012 :=
    @gA1i
      (synWb (synWbr (synCsn (synCsn (synCuni (synCuni (.cv p))))) (synCsi (synCsi R))
          (synCsn (synCsn (synCuni (synCuni (.cv q))))))
        (synWbr (synCsn (synCuni (synCuni (.cv p)))) (synCsi R)
          (synCsn (synCuni (synCuni (.cv q))))))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      p0011
  have p0014 := @gElex (.cv p) (synCpw1 (synCpw1 D))
  have p0015 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (.cv p) (synCpw1 (synCpw1 D))) (.classMem (.cv p) (synCvv)) p0000
      p0014
  have p0016 := @gUniexg (.cv p) (synCvv)
  have p0017 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (.cv p) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv)) p0015 p0016
  have p0018 := @gUniexg (synCuni (.cv p)) (synCvv)
  have p0019 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (.cv p)) (synCvv))
      (.classMem (synCuni (synCuni (.cv p))) (synCvv)) p0017 p0018
  have p0021 := @gElex (.cv q) (synCpw1 (synCpw1 D))
  have p0022 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classMem (.cv q) (synCvv)) p0004
      p0021
  have p0023 := @gUniexg (.cv q) (synCvv)
  have p0024 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (.cv q) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv)) p0022 p0023
  have p0025 := @gUniexg (synCuni (.cv q)) (synCvv)
  have p0026 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (.cv q)) (synCvv))
      (.classMem (synCuni (synCuni (.cv q))) (synCvv)) p0024 p0025
  have p0027 :=
    @gJca
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv p))) (synCvv))
      (.classMem (synCuni (synCuni (.cv q))) (synCvv)) p0019 p0026
  have p0028 :=
    @gBrsnsiandv (synCuni (synCuni (.cv p))) (synCuni (synCuni (.cv q))) R
      dv_cache_0001
  have p0029 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (synWa (.classMem (synCuni (synCuni (.cv p))) (synCvv))
        (.classMem (synCuni (synCuni (.cv q))) (synCvv)))
      (synWb (synWbr (synCsn (synCuni (synCuni (.cv p)))) (synCsi R)
          (synCsn (synCuni (synCuni (.cv q)))))
        (synWbr (synCuni (synCuni (.cv p))) R (synCuni (synCuni (.cv q)))))
      p0027 p0028
  have p0030 :=
    @gN3bitrd
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 D)))
        (.classMem (.cv q) (synCpw1 (synCpw1 D))))
      (synWbr (.cv p) (synCsi (synCsi R)) (.cv q))
      (synWbr (synCsn (synCsn (synCuni (synCuni (.cv p))))) (synCsi (synCsi R))
        (synCsn (synCsn (synCuni (synCuni (.cv q))))))
      (synWbr (synCsn (synCuni (synCuni (.cv p)))) (synCsi R)
        (synCsn (synCuni (synCuni (.cv q)))))
      (synWbr (synCuni (synCuni (.cv p))) R (synCuni (synCuni (.cv q)))) p0008 p0012
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

/-- Checked nominal proof certificate identified upstream as `g_isostrictsegresclndv`. -/
@[expose]
noncomputable def gIsostrictsegresclndv (B : Class) (D : Class) (R : Class) (S : Class)
    (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWiso H R S D E) (.classMem B D)) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))) :=
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
      ((Wff.imp (synWa (synWiso H R S D E) (.classMem B D)) (synWiso (synCres H
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
              (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
            (synCin S (synCxp (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
                (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))).fv :=
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
  have p0000 := @gId (synWa (synWiso H R S D E) (.classMem B D))
  have p0001 := @gSimpr (synWiso H R S D E) (.classMem B D)
  have p0002 := @gElex B D
  have p0003 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem B D)) (.classMem B D)
      (.classMem B (synCvv)) p0001 p0002
  have p0004 := @gBiid (synWiso H R S D E)
  have p0005 :=
    @gA1i (synWb (synWiso H R S D E) (synWiso H R S D E)) (.classEq (.cv x) B) p0004
  have p0006 := @gId (.classEq (.cv x) B)
  have p0007 := @gEleq1d (.classEq (.cv x) B) (.cv x) B D p0006
  have p0008 :=
    @gAnbi12d (.classEq (.cv x) B) (synWiso H R S D E) (synWiso H R S D E)
      (.classMem (.cv x) D) (.classMem B D) p0005 p0007
  have p0010 := @gSneqd (.classEq (.cv x) B) (.cv x) B p0006
  have p0011 :=
    @gImaeq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B)
      (synCcnv (synCdif R (synCid))) p0010
  have p0012 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn B)) D p0011
  have p0013 :=
    @gReseq2d (.classEq (.cv x) B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) H p0012
  have p0014 :=
    @gIsoeq1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0015 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
        (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0013 p0014
  have p0024 :=
    @gXpeq12d (.classEq (.cv x) B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) p0012 p0012
  have p0025 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      R p0024
  have p0026 :=
    @gIsoeq2 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
  have p0027 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
        (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0025 p0026
  have p0028 :=
    @gBitrd (.classEq (.cv x) B)
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      p0015 p0027
  have p0030 := @gFveq2d (.classEq (.cv x) B) (.cv x) B H p0006
  have p0031 := @gSneqd (.classEq (.cv x) B) (synCfv H (.cv x)) (synCfv H B) p0030
  have p0032 :=
    @gImaeq2d (.classEq (.cv x) B) (synCsn (synCfv H (.cv x))) (synCsn (synCfv H B))
      (synCcnv (synCdif S (synCid))) p0031
  have p0033 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))) E p0032
  have p0039 :=
    @gXpeq12d (.classEq (.cv x) B)
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
      p0033 p0033
  have p0040 :=
    @gIneq2d (.classEq (.cv x) B)
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))
      S p0039
  have p0041 :=
    @gIsoeq3 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin S (synCxp (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
          (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
  have p0042 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x))))))) (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
        (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0040 p0041
  have p0043 :=
    @gBitrd (.classEq (.cv x) B)
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      p0028 p0042
  have p0048 :=
    @gIsoeq4 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
  have p0049 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
        (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      p0012 p0048
  have p0050 :=
    @gBitrd (.classEq (.cv x) B)
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      p0043 p0049
  have p0056 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
      (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
      (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
  have p0057 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))
      (synWb (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
        (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
      p0033 p0056
  have p0058 :=
    @gBitrd (.classEq (.cv x) B)
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))
      p0050 p0057
  have p0059 :=
    @gImbi12d (.classEq (.cv x) B) (synWa (synWiso H R S D E) (.classMem (.cv x) D))
      (synWa (synWiso H R S D E) (.classMem B D))
      (synWiso (synCres H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCin R
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))
            (synCin E (synCima (synCcnv (synCdif S (synCid)))
                (synCsn (synCfv H (.cv x)))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
          (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x))))))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))
      p0008 p0058
  have p0060 := @gIsostrictsegresndv x D R S E H
  have p0061 :=
    @gVtoclg
      (.imp (synWa (synWiso H R S D E) (.classMem (.cv x) D)) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid)))
                  (synCsn (synCfv H (.cv x))))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H (.cv x)))))))
      (.imp (synWa (synWiso H R S D E) (.classMem B D)) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
      x B (synCvv) dv_cache_0001 dv_cache_0002 p0059 p0060
  have p0062 :=
    @gSyl (synWa (synWiso H R S D E) (.classMem B D)) (.classMem B (synCvv))
      (.imp (synWa (synWiso H R S D E) (.classMem B D)) (synWiso (synCres H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
            (synCxp (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
      p0003 p0061
  have p0063 :=
    @gMpd (synWa (synWiso H R S D E) (.classMem B D))
      (synWa (synWiso H R S D E) (.classMem B D))
      (synWiso
        (synCres H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
        (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))) (synCin S
          (synCxp (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))) (synCin E
              (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (synCfv H B)))))
      p0000 p0062
  exact p0063

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomappreexclndv`. -/
@[expose]
noncomputable def gHnsiquomappreexclndv (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_hnsiquomappreexclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synChnord (synCpw1 A))) (synWrex x (synCpw1 (synChnord A))
          (.classEq B (synCfv (synChnsiquomap A) (.cv x))))) :=
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
  have dv_cache_0006 : y ∉ ((synChnord (synCpw1 A))).fv :=
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
      ((synWrex x (synCpw1 (synChnord A))
          (.classEq B (synCfv (synChnsiquomap A) (.cv x))))).fv :=
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
  have p0000 := @gId (.classEq (.cv y) B)
  have p0001 :=
    @gEqeq1d (.classEq (.cv y) B) (.cv y) B (synCfv (synChnsiquomap A) (.cv x)) p0000
  have p0002 :=
    @gRexbidv (.classEq (.cv y) B)
      (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x)))
      (.classEq B (synCfv (synChnsiquomap A) (.cv x))) x (synCpw1 (synChnord A))
      dv_cache_0001 p0001
  have p0003 :=
    @gHnsiquomappreexndv x y A dv_cache_0002 dv_cache_0003 dv_cache_0004
      hyp_hnsiquomappreexclndv_1
  have p0004 :=
    @gVtoclga
      (synWrex x (synCpw1 (synChnord A))
        (.classEq (.cv y) (synCfv (synChnsiquomap A) (.cv x))))
      (synWrex x (synCpw1 (synChnord A)) (.classEq B (synCfv (synChnsiquomap A) (.cv x))))
      y B (synChnord (synCpw1 A)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomaprepvalcl2ndv`. -/
@[expose]
noncomputable def gHnsiquomaprepvalcl2ndv (A : Class) (C : Class) (q : Var)
    (dv_A_q : q ∉ A.fv)
    (hyp_hnsiquomaprepvalcl2ndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))) :=
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
      ((Wff.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (synWa (.classMem C (synChwcn A))
              (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
          (.classEq (synCfv (synChnsiquomap A) (.cv q))
            (synCec (synCfv (synChnsicodemap A) (synCsn C))
              (synChwniso (synCpw1 A)))))).fv :=
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
    @gSimpr (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem C (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec C (synChwniso A))))
  have p0001 :=
    @gSimpl (.classMem C (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
      (synWa (.classMem C (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec C (synChwniso A))))
      (.classMem C (synChwcn A)) p0000 p0001
  have p0003 := @gElex C (synChwcn A)
  have p0004 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
      (.classMem C (synChwcn A)) (.classMem C (synCvv)) p0002 p0003
  have p0005 :=
    @gBiidd (.classEq (.cv u) C) (.classMem (.cv q) (synCpw1 (synChnord A)))
  have p0006 := @gId (.classEq (.cv u) C)
  have p0007 := @gEleq1d (.classEq (.cv u) C) (.cv u) C (synChwcn A) p0006
  have p0008 := @gEceq1 (.cv u) C (synChwniso A)
  have p0009 :=
    @gEqeq2d (.classEq (.cv u) C) (synCec (.cv u) (synChwniso A))
      (synCec C (synChwniso A)) (synCuni (.cv q)) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv u) C) (.classMem (.cv u) (synChwcn A))
      (.classMem C (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))
      (.classEq (synCuni (.cv q)) (synCec C (synChwniso A))) p0007 p0009
  have p0011 :=
    @gAnbi12d (.classEq (.cv u) C) (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A))))
      (synWa (.classMem C (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec C (synChwniso A))))
      p0005 p0010
  have p0013 := @gSneqd (.classEq (.cv u) C) (.cv u) C p0006
  have p0014 :=
    @gFveq2d (.classEq (.cv u) C) (synCsn (.cv u)) (synCsn C) (synChnsicodemap A)
      p0013
  have p0015 :=
    @gEceq1 (synCfv (synChnsicodemap A) (synCsn (.cv u)))
      (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))
  have p0016 :=
    @gSyl (.classEq (.cv u) C)
      (.classEq (synCfv (synChnsicodemap A) (synCsn (.cv u)))
        (synCfv (synChnsicodemap A) (synCsn C)))
      (.classEq (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u)))
          (synChwniso (synCpw1 A)))
        (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))
      p0014 p0015
  have p0017 :=
    @gEqeq2d (.classEq (.cv u) C)
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A)))
      (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))
      (synCfv (synChnsiquomap A) (.cv q)) p0016
  have p0018 :=
    @gImbi12d (.classEq (.cv u) C)
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv u) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u))) (synChwniso (synCpw1 A))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))
      p0011 p0017
  have p0019 :=
    @gHnsiquomaprepvalndv u A q dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnsiquomaprepvalcl2ndv_1
  have p0020 :=
    @gVtoclg
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem (.cv u) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv u) (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCec (synCfv (synChnsicodemap A) (synCsn (.cv u)))
            (synChwniso (synCpw1 A)))))
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))))
      u C (synCvv) dv_cache_0004 dv_cache_0005 p0018 p0019
  have p0021 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
      (.classMem C (synCvv))
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))))
      p0004 p0020
  have p0022 :=
    @gPm243i
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))
      p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end
