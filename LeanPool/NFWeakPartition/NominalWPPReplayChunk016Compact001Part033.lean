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

/-- Checked nominal proof certificate identified upstream as `g_wecutisobranchcwknfdv`. -/
@[expose]
noncomputable def gWecutisobranchcwknfdv (x : Var) (y : Var) (z : Var) (u : Var)
    (D : Class) (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv)
    (_dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (_dv_D_z : z ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv) (dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv)
    (_dv_E_z : z ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (_dv_R_y : y ∉ R.fv) (_dv_R_z : z ∉ R.fv) (dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (_dv_S_z : z ∉ S.fv) (dv_h_u : h ≠ u)
    (dv_h_x : h ≠ x) (dv_h_y : h ≠ y) (dv_h_z : h ≠ z) (_dv_u_x : u ≠ x) (_dv_u_y : u ≠ y)
    (_dv_u_z : u ≠ z) (_dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (_dv_y_z : y ≠ z)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
              (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u)))))).fv :=
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
      ((synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))).fv :=
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
      ((synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))).fv :=
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
    @gId
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
  have p0001 :=
    @gA1i
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
  have p0003 :=
    @gSimpl (.classMem (.cv z) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classMem (.cv z) D) p0002 p0003
  have p0005 :=
    @gA1i
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.classMem (.cv z) D))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0004
  have p0006 := @gId (.classMem (.cv z) D)
  have p0007 :=
    @gA1d (.classMem (.cv z) D) (.classMem (.cv z) D)
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0006
  have p0008 :=
    @gA1i
      (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.classMem (.cv z) D)))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0007
  have p0009 :=
    @gId
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0010 :=
    Nominal.ax1
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
  have p0011 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0010
  have p0012 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0009 p0011
  have p0014 :=
    @gSimpr (.classMem (.cv z) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      p0002 p0014
  have p0016 :=
    @gIsoeq4
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCsn (.cv y)))
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0015 p0016
  have p0018 :=
    @gBiimpd
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0017
  have p0019 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0018
  have p0020 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0019
  have p0021 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0012 p0020
  have p0022 :=
    @gSimpr
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
  have p0023 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      E R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0024 :=
    @gSyl
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E))
      p0022 p0023
  have p0025 :=
    @gBiimpd
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E)
      p0024
  have p0026 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E)
      p0025
  have p0027 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E)))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0026
  have p0028 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E))
      p0021 p0027
  have p0029 :=
    @gIsocnv (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E
      R S (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0030 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E)
        (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))) S R E
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0029
  have p0031 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E)
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u)))))
        S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      p0030
  have p0032 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E))
        (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCcnv
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
            S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0031
  have p0033 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) E))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso (synCcnv
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
          S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0028 p0032
  have p0034 :=
    @gIsores2 E
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) S R
      (synCcnv
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
  have p0035 :=
    @gBiimpi
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u)))))
        S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      p0034
  have p0036 :=
    @gA1i
      (.imp (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))) S R E
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))) (synWiso
          (synCcnv (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0035
  have p0037 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u)))))
        S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      p0036
  have p0038 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCcnv
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
            S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCcnv
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
            S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0037
  have p0039 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso (synCcnv
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
          S R E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso (synCcnv
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))) S
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0033 p0038
  have p0040 := @gSnex (synCop (.cv y) (.cv u))
  have p0041 :=
    @gUnex (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0040
  have p0042 :=
    @gCnvex
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      p0041
  have p0043 :=
    @gIsoeq1 E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synCcnv
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
      (.cv h)
  have p0044 :=
    @gSpcev
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      h
      (synCcnv
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
      dv_cache_0001 dv_cache_0002 p0042 p0043
  have p0045 :=
    @gA1i
      (.imp (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
        (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0044
  have p0046 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWiso (synCcnv (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u))))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0045
  have p0047 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWiso (synCcnv
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
            S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.imp
          (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0046
  have p0048 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWiso (synCcnv
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))) S
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      p0039 p0047
  have p0049 :=
    Nominal.ax1
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classMem (.cv z) D)
  have p0050 :=
    @gA1i
      (.imp (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.imp (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0049
  have p0051 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.imp (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      p0050
  have p0052 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
        (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0051
  have p0053 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      p0048 p0052
  have p0054 :=
    @g_pm3_2 (.classMem (.cv z) D)
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
  have p0055 :=
    @gA2i (.classMem (.cv z) D)
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      p0054
  have p0056 :=
    @gA1i
      (.imp (.imp (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
        (.imp (.classMem (.cv z) D) (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0055
  have p0057 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.imp (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (.imp (.classMem (.cv z) D) (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      p0056
  have p0058 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
        (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWa (.classMem (.cv z) D)
              (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0057
  have p0059 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWa (.classMem (.cv z) D)
            (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      p0053 p0058
  have p0060 :=
    Nominal.ax2
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.classMem (.cv z) D)
      (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
  have p0061 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWa (.classMem (.cv z) D)
              (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))) (.imp
          (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0060
  have p0062 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (synWa (.classMem (.cv z) D)
            (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
            (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      p0059 p0061
  have p0063 :=
    Nominal.ax1
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
            (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (.classMem (.cv z) D)
  have p0064 :=
    @gA1i
      (.imp (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
        (.imp (.classMem (.cv z) D) (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                    (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                  (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv z)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0063
  have p0065 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
            (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (.imp (.classMem (.cv z) D) (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      p0062 p0064
  have p0066 :=
    Nominal.ax2 (.classMem (.cv z) D)
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.classMem (.cv z) D))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
            (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
  have p0067 :=
    @gA1i
      (.imp (.imp (.classMem (.cv z) D) (.imp (.imp (synWa (synWa (.classMem (.cv z) D)
                  (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                  (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv z)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
        (.imp (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                    (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (.classMem (.cv z) D))) (.imp (.classMem (.cv z) D)
            (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                  (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv z)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0066
  have p0068 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.classMem (.cv z) D) (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      (.imp (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.classMem (.cv z) D))) (.imp (.classMem (.cv z) D)
          (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      p0065 p0067
  have p0069 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.classMem (.cv z) D)))
      (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      p0008 p0068
  have p0070 :=
    Nominal.ax1
      (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
  have p0071 :=
    @gA1i
      (.imp (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))) (.imp
          (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                  (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv z)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0070
  have p0072 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.classMem (.cv z) D) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      p0069 p0071
  have p0073 :=
    Nominal.ax2
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (.classMem (.cv z) D)
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
            (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
  have p0074 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                  (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv z)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
        (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                    (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                  (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv z)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0073
  have p0075 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (.classMem (.cv z) D) (.imp (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.classMem (.cv z) D)) (.imp (synWa
            (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      p0072 p0074
  have p0076 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.classMem (.cv z) D))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      p0005 p0075
  have p0077 :=
    Nominal.ax2
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
  have p0078 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))) (.imp
          (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
                (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
                (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0077
  have p0079 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq
                (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))))
      p0076 p0078
  have p0080 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
            (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      p0001 p0079
  have p0081 := @gSneq (.cv x) (.cv z)
  have p0082 :=
    @gImaeq2d (.classEq (.cv x) (.cv z)) (synCsn (.cv x)) (synCsn (.cv z))
      (synCcnv (synCdif R (synCid))) p0081
  have p0083 :=
    @gIneq2d (.classEq (.cv x) (.cv z))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))) D p0082
  have p0087 :=
    @gXpeq12d (.classEq (.cv x) (.cv z))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) p0083
      p0083
  have p0088 :=
    @gIneq2d (.classEq (.cv x) (.cv z))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      R p0087
  have p0089 :=
    @gIsoeq3 E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.cv h)
  have p0090 :=
    @gSyl (.classEq (.cv x) (.cv z))
      (.classEq (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synWb (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0088 p0089
  have p0094 :=
    @gIsoeq5 E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.cv h)
  have p0095 :=
    @gSyl (.classEq (.cv x) (.cv z))
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWb (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0083 p0094
  have p0096 :=
    @gBitrd (.classEq (.cv x) (.cv z))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      p0090 p0095
  have p0097 :=
    @gExbidv (.classEq (.cv x) (.cv z))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      h dv_cache_0003 p0096
  have p0098 :=
    @gRspcev
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      x (.cv z) D dv_cache_0004 dv_cache_0005 dv_cache_0006 p0097
  have p0099 :=
    @gA1i
      (.imp (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0098
  have p0100 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWa (.classMem (.cv z) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0099
  have p0101 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
              (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
        (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWrex x D (synWex h (synWiso (.cv h) S (synCin R
                  (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0100
  have p0102 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWa (.classMem (.cv z) D) (synWex h
            (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWrex x D (synWex h (synWiso (.cv h) S (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0080 p0101
  have p0103 :=
    @gN3mix3
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) R S D E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
  have p0104 :=
    @gA1i
      (.imp (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      p0103
  have p0105 :=
    @gA2i
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0104
  have p0106 :=
    @gA1i
      (.imp (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synWrex x D (synWex h (synWiso (.cv h) S (synCin R
                  (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
        (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
            (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0105
  have p0107 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synWrex x D (synWex h (synWiso (.cv h) S (synCin R
                (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0102 p0106
  have p0108 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
            (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0107
  exact p0108


end NFChoice.DirectNominalPrf.WPPReplay
