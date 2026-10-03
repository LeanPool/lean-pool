/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block007

/-! NF weak partition development: NominalWPPReplayChunk016Compact001Part033. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisobranchcwknfdv (x : Var) (y : Var) (z : Var) (u : Var)
    (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv)
    (_dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (_dv_D_z : z ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv)
    (_dv_E_z : z ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (_dv_R_y : y ∉ R.fv) (_dv_R_z : z ∉ R.fv) (dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (_dv_S_z : z ∉ S.fv) (dv_h_u : h ≠ u)
    (dv_h_x : h ≠ x) (dv_h_y : h ≠ y) (dv_h_z : h ≠ z) (_dv_u_x : u ≠ x) (_dv_u_y : u ≠ y)
    (_dv_u_z : u ≠ z) (_dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (_dv_y_z : y ≠ z)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (.imp
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
              (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                          (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid)))
                            (syn_csn (.cv x)))))) D (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
              (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv x)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u)))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_E_h, dv_R_h, dv_S_h, dv_h_y, dv_h_u, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    h ∉
      ((syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, dv_E_h, dv_D_h, dv_R_h, dv_h_z, dv_S_h, dv_h_y, dv_h_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ ((Wff.classEq (.cv x) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_h_x, dv_h_z, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_E_x, dv_D_x, dv_R_x, dv_x_z,
          (Ne.symm dv_h_x), dv_S_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @g_id
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
  have p0001 :=
    @g_a1i
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
  have p0003 :=
    @g_simpl (.classMem (.cv z) D)
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classMem (.cv z) D) p0002 p0003
  have p0005 :=
    @g_a1i
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.classMem (.cv z) D))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0004
  have p0006 := @g_id (.classMem (.cv z) D)
  have p0007 :=
    @g_a1d (.classMem (.cv z) D) (.classMem (.cv z) D)
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0006
  have p0008 :=
    @g_a1i
      (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.classMem (.cv z) D)))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0007
  have p0009 :=
    @g_id
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
  have p0010 :=
    Nominal.ax1
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
  have p0011 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0010
  have p0012 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0009 p0011
  have p0014 :=
    @g_simpr (.classMem (.cv z) D)
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      p0002 p0014
  have p0016 :=
    @g_isoeq4
      (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_csn (.cv y)))
      (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_csn (.cv u)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_wb (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0015 p0016
  have p0018 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0017
  have p0019 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0018
  have p0020 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))
            R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0019
  have p0021 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0012 p0020
  have p0022 :=
    @g_simpr
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
  have p0023 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
      (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_csn (.cv u)))
      E R S
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
      (syn_wb (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E))
      p0022 p0023
  have p0025 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E)
      p0024
  have p0026 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E)
      p0025
  have p0027 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))
            R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))
            R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E)))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0026
  have p0028 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cun (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E))
      p0021 p0027
  have p0029 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E
      R S (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
  have p0030 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E)
        (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))) S R E
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0029
  have p0031 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R
        S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E)
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u)))))
        S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      p0030
  have p0032 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))
            R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E))
        (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
              (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
            S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0031
  have p0033 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
          R S (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) E))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
            (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
          S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      p0028 p0032
  have p0034 :=
    @g_isores2 E
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) S R
      (syn_ccnv
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
  have p0035 :=
    @g_biimpi
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u)))))
        S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      p0034
  have p0036 :=
    @g_a1i
      (.imp (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))) S R E
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))) (syn_wiso
          (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0035
  have p0037 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u)))))
        S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      p0036
  have p0038 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
              (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
            S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
              (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
            S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0037
  have p0039 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
            (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
          S R E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
            (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))) S
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      p0033 p0038
  have p0040 := @g_snex (syn_cop (.cv y) (.cv u))
  have p0041 :=
    @g_unex (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0040
  have p0042 :=
    @g_cnvex
      (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
      p0041
  have p0043 :=
    @g_isoeq1 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
      S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (syn_ccnv
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
      (.cv h)
  have p0044 :=
    @g_spcev
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      h
      (syn_ccnv
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
      dv_cache_0001 dv_cache_0002 p0042 p0043
  have p0045 :=
    @g_a1i
      (.imp (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
        (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0044
  have p0046 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wiso (syn_ccnv (syn_cun (syn_cuni (syn_cwecutiso R D S E))
            (syn_csn (syn_cop (.cv y) (.cv u))))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      p0045
  have p0047 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
              (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))))
            S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
            E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.imp
          (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0046
  have p0048 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wiso (syn_ccnv
            (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))) S
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      p0039 p0047
  have p0049 :=
    Nominal.ax1
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classMem (.cv z) D)
  have p0050 :=
    @g_a1i
      (.imp (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
            E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.imp (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0049
  have p0051 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.imp (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      p0050
  have p0052 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
        (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0051
  have p0053 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      p0048 p0052
  have p0054 :=
    @g_pm3_2 (.classMem (.cv z) D)
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
  have p0055 :=
    @g_a2i (.classMem (.cv z) D)
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      p0054
  have p0056 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
        (.imp (.classMem (.cv z) D) (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S
                (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0055
  have p0057 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.imp (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (.imp (.classMem (.cv z) D) (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      p0056
  have p0058 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
        (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wa (.classMem (.cv z) D)
              (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0057
  have p0059 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wa (.classMem (.cv z) D)
            (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      p0053 p0058
  have p0060 :=
    Nominal.ax2
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.classMem (.cv z) D)
      (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
  have p0061 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wa (.classMem (.cv z) D)
              (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))) (.imp
          (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0060
  have p0062 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (syn_wa (.classMem (.cv z) D)
            (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
            (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      p0059 p0061
  have p0063 :=
    Nominal.ax1
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
            (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (.classMem (.cv z) D)
  have p0064 :=
    @g_a1i
      (.imp (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
        (.imp (.classMem (.cv z) D) (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                    (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
                (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                  (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv z)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0063
  have p0065 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
            (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (.imp (.classMem (.cv z) D) (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      p0062 p0064
  have p0066 :=
    Nominal.ax2 (.classMem (.cv z) D)
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.classMem (.cv z) D))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
            (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
  have p0067 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv z) D) (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D)
                  (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
                (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                  (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv z)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
        (.imp (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                    (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (.classMem (.cv z) D))) (.imp (.classMem (.cv z) D)
            (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                  (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv z)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0066
  have p0068 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.classMem (.cv z) D) (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      (.imp (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.classMem (.cv z) D))) (.imp (.classMem (.cv z) D)
          (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      p0065 p0067
  have p0069 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.classMem (.cv z) D)))
      (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      p0008 p0068
  have p0070 :=
    Nominal.ax1
      (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
  have p0071 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))) (.imp
          (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (syn_wa
                (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                  (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv z)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0070
  have p0072 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (.classMem (.cv z) D) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      p0069 p0071
  have p0073 :=
    Nominal.ax2
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (.classMem (.cv z) D)
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
            (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
  have p0074 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (syn_wa
                (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                  (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv z)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
        (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                    (syn_cun (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_csn (.cv y))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
                (.classEq (syn_cun (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                    (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                  (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv z)))))) E (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0073
  have p0075 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (syn_wa
              (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (syn_wa
            (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      p0072 p0074
  have p0076 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.classMem (.cv z) D))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      p0005 p0075
  have p0077 :=
    Nominal.ax2
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
  have p0078 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))) (.imp
          (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
                (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
                (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0077
  have p0079 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))))
      p0076 p0078
  have p0080 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
            (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      p0001 p0079
  have p0081 := @g_sneq (.cv x) (.cv z)
  have p0082 :=
    @g_imaeq2d (.classEq (.cv x) (.cv z)) (syn_csn (.cv x)) (syn_csn (.cv z))
      (syn_ccnv (syn_cdif R (syn_cid))) p0081
  have p0083 :=
    @g_ineq2d (.classEq (.cv x) (.cv z))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))) D p0082
  have p0087 :=
    @g_xpeq12d (.classEq (.cv x) (.cv z))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) p0083
      p0083
  have p0088 :=
    @g_ineq2d (.classEq (.cv x) (.cv z))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      R p0087
  have p0089 :=
    @g_isoeq3 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.cv h)
  have p0090 :=
    @g_syl (.classEq (.cv x) (.cv z))
      (.classEq (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (syn_wb (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0088 p0089
  have p0094 :=
    @g_isoeq5 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.cv h)
  have p0095 :=
    @g_syl (.classEq (.cv x) (.cv z))
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_wb (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      p0083 p0094
  have p0096 :=
    @g_bitrd (.classEq (.cv x) (.cv z))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      p0090 p0095
  have p0097 :=
    @g_exbidv (.classEq (.cv x) (.cv z))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      h dv_cache_0003 p0096
  have p0098 :=
    @g_rspcev
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      x (.cv z) D dv_cache_0004 dv_cache_0005 dv_cache_0006 p0097
  have p0099 :=
    @g_a1i
      (.imp (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0098
  have p0100 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wa (.classMem (.cv z) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0099
  have p0101 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
              (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
        (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R
                  (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0100
  have p0102 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wa (.classMem (.cv z) D) (syn_wex h
            (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0080 p0101
  have p0103 :=
    @g_n_3mix3
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
  have p0104 :=
    @g_a1i
      (.imp (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      p0103
  have p0105 :=
    @g_a2i
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0104
  have p0106 :=
    @g_a1i
      (.imp (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R
                  (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
        (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
            (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0105
  have p0107 :=
    @g_mpd
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R
                (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0102 p0106
  have p0108 :=
    @g_a1i
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
            (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) p0107
  exact p0108


end NFChoice.DirectNominalPrf.WPPReplay
