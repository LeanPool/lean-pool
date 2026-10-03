/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecomparisoncutreplttargetdfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_R_x : x ∉ R.fv)
    (dv_S_x : x ∉ S.fv)
    (hyp_wecomparisoncutreplttargetdfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
        (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) :=
  by
  have dv_cache_0001 :
    x ∉
      ((Wff.classEq R (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin))
              (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_R_x,
          dv_S_x, dv_E_x, dv_D_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0003 :
    x ∉
      ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_D_x,
          dv_S_x, dv_E_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.classEq D (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_D_x,
          dv_S_x, dv_E_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.classEq E (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_E_x,
          dv_S_x, dv_D_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_E_x,
          dv_S_x, dv_D_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    x ∉
      ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_R_x,
          dv_S_x, dv_E_x, dv_D_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_S_x,
          dv_E_x, dv_D_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_id
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
  have p0001 :=
    @g_difeq1d
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      R
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
      (syn_cid) p0000
  have p0002 :=
    @g_cnveqd
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      (syn_cdif R (syn_cid))
      (syn_cdif (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
        (syn_cid))
      p0001
  have p0003 :=
    @g_imaeq1d
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_ccnv (syn_cdif (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin))
              (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
      (syn_csn (.cv x)) p0002
  have p0004 :=
    @g_ineq2d
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
              (syn_cin (syn_ckqrel (syn_clefin))
                (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
        (syn_csn (.cv x)))
      D p0003
  have p0005 :=
    @g_nceqd
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                  (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                (syn_cin (syn_ckqrel (syn_clefin))
                  (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
          (syn_csn (.cv x))))
      p0004
  have p0006 :=
    @g_eqeq2d
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                    (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                  (syn_cin (syn_ckqrel (syn_clefin))
                    (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cnc E) p0005
  have p0007 :=
    @g_rexbidv
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif
                    (syn_wa (syn_wbr S (syn_cwe) E)
                      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                    (syn_cin (syn_ckqrel (syn_clefin))
                      (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
              (syn_csn (.cv x))))))
      x D dv_cache_0001 p0006
  have p0008 :=
    @g_biid
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif
                    (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
  have p0009 :=
    @g_a1i
      (syn_wb (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv
                    (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                          (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                        (syn_cin (syn_ckqrel (syn_clefin))
                          (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                  (syn_csn (.cv x))))))) (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                          (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                        (syn_cin (syn_ckqrel (syn_clefin))
                          (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                  (syn_csn (.cv x))))))))
      (.classEq S (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      p0008
  have p0010 :=
    @g_rexeq
      (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif
                    (syn_wa (syn_wbr S (syn_cwe) E)
                      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                    (syn_cin (syn_ckqrel (syn_clefin))
                      (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
              (syn_csn (.cv x))))))
      x D
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      dv_cache_0002 dv_cache_0003
  have p0011 :=
    @g_id
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
  have p0012 :=
    @g_ineq1d
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      D
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
              (syn_cin (syn_ckqrel (syn_clefin))
                (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
        (syn_csn (.cv x)))
      p0011
  have p0013 :=
    @g_nceqd
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                  (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                (syn_cin (syn_ckqrel (syn_clefin))
                  (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif
                (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                (syn_cin (syn_ckqrel (syn_clefin))
                  (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
          (syn_csn (.cv x))))
      p0012
  have p0014 :=
    @g_eqeq2d
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                    (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                  (syn_cin (syn_ckqrel (syn_clefin))
                    (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cnc (syn_cin (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif
                  (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
                  R (syn_cin (syn_ckqrel (syn_clefin))
                    (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cnc E) p0013
  have p0015 :=
    @g_rexbidv
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif (syn_cif
                    (syn_wa (syn_wbr S (syn_cwe) E)
                      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                    (syn_cin (syn_ckqrel (syn_clefin))
                      (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                    (syn_cin (syn_ckqrel (syn_clefin))
                      (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
              (syn_csn (.cv x))))))
      x
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      dv_cache_0004 p0014
  have p0016 :=
    @g_bitrd
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif
                    (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))) (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv
                  (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))) (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif
                (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
                D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif
                      (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      p0010 p0015
  have p0017 :=
    @g_id
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
  have p0018 :=
    @g_nceqd
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      E
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
        (syn_c0))
      p0017
  have p0019 :=
    @g_eqeq1d
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_cnc E)
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_cnc (syn_cin (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif
                  (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
                  R (syn_cin (syn_ckqrel (syn_clefin))
                    (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
            (syn_csn (.cv x)))))
      p0018
  have p0020 :=
    @g_rexbidv
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                    (syn_cin (syn_ckqrel (syn_clefin))
                      (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0))) (syn_cnc (syn_cin (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                    (syn_cin (syn_ckqrel (syn_clefin))
                      (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
              (syn_csn (.cv x))))))
      x
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      dv_cache_0005 p0019
  have p0021 :=
    @g_breq1 R
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
      D (syn_cwe)
  have p0022 :=
    @g_breq2 D
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
      (syn_cwe)
  have p0023 :=
    @g_breq1
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
      (syn_csn (syn_c0c)) (syn_cwe)
  have p0024 :=
    @g_breq2 (syn_csn (syn_c0c))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
      (syn_cwe)
  have p0025 := @g_finlewe
  have p0026 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) syn_wtru p0025
  have p0027 := @g_peano1
  have p0028 := @g_snssi (syn_c0c) (syn_cnnc)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @g_a1i (syn_wss (syn_csn (syn_c0c)) (syn_cnnc)) syn_wtru p0029
  have p0031 := @g_snex (syn_c0c)
  have p0032 := @g_a1i (.classMem (syn_csn (syn_c0c)) (syn_cvv)) syn_wtru p0031
  have p0033 :=
    @g_werestrndv syn_wtru (syn_csn (syn_c0c)) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0026
      p0030 p0032
  have p0034 :=
    @g_trud
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin))
          (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cwe) (syn_csn (syn_c0c)))
      p0033
  have p0035 :=
    @g_keephyp2v
      (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (syn_wbr R (syn_cwe) D)
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
        (syn_cwe) D)
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
        (syn_cwe) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin))
          (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cwe) (syn_csn (syn_c0c)))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
        (syn_cwe) (syn_csn (syn_c0c)))
      R D
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))
      (syn_csn (syn_c0c)) p0021 p0022 p0023 p0024 hyp_wecomparisoncutreplttargetdfdv_1
      p0034
  have p0036 :=
    @g_biid (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
  have p0037 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
        (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))))
      (.classEq R (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      p0036
  have p0038 :=
    @g_id
      (.classEq S (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0039 :=
    @g_breq1d
      (.classEq S (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      S
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      E (syn_cwe) p0038
  have p0040 := @g_biid (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
  have p0041 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (.classEq S (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      p0040
  have p0042 :=
    @g_anbi12d
      (.classEq S (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_wbr S (syn_cwe) E)
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)) p0039 p0041
  have p0043 :=
    @g_biid
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
  have p0044 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
        (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E))
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      p0043
  have p0046 :=
    @g_nceqd
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      D
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      p0011
  have p0047 :=
    @g_breq2d
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cnc D)
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cnc E) (syn_cltc) p0046
  have p0048 :=
    @g_anbi12d
      (.classEq D (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      p0044 p0047
  have p0050 :=
    @g_breq2d
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      E
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
        (syn_c0))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cwe) p0017
  have p0053 :=
    @g_breq1d
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_cnc E)
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cltc) p0018
  have p0054 :=
    @g_anbi12d
      (.classEq E (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      (syn_wbr (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      p0050 p0053
  have p0055 :=
    @g_biid
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
  have p0056 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_cwe) (syn_c0))
          (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))) (syn_wa
          (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_cwe) (syn_c0))
          (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))))
      (.classEq (syn_cin (syn_ckqrel (syn_clefin))
          (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin))
            (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))))
      p0055
  have p0057 :=
    @g_id
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0058 :=
    @g_breq1d
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_c0) (syn_cwe) p0057
  have p0059 :=
    @g_biid (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))
  have p0060 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))
        (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      p0059
  have p0061 :=
    @g_anbi12d
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
      (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))
      (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) p0058 p0060
  have p0062 :=
    @g_biid
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
  have p0063 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
          (syn_cwe) (syn_c0)) (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
          (syn_cwe) (syn_c0)))
      (.classEq (syn_csn (syn_c0c)) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      p0062
  have p0064 :=
    @g_id
      (.classEq (syn_csn (syn_c0c)) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
  have p0065 :=
    @g_nceqd
      (.classEq (syn_csn (syn_c0c)) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_csn (syn_c0c))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      p0064
  have p0066 :=
    @g_breq2d
      (.classEq (syn_csn (syn_c0c)) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cnc (syn_csn (syn_c0c)))
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cnc (syn_c0)) (syn_cltc) p0065
  have p0067 :=
    @g_anbi12d
      (.classEq (syn_csn (syn_c0c)) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
      (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c))))
      (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      p0063 p0066
  have p0068 :=
    @g_id
      (.classEq (syn_c0) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
  have p0069 :=
    @g_breq2d
      (.classEq (syn_c0) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_c0)
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
        (syn_c0))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cwe) p0068
  have p0071 :=
    @g_nceqd
      (.classEq (syn_c0) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_c0)
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
        (syn_c0))
      p0068
  have p0072 :=
    @g_breq1d
      (.classEq (syn_c0) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_cnc (syn_c0))
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_cnc (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))))
      (syn_cltc) p0071
  have p0073 :=
    @g_anbi12d
      (.classEq (syn_c0) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      (syn_wbr (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      p0069 p0072
  have p0076 := @g_n_0ss (syn_cnnc)
  have p0077 := @g_a1i (syn_wss (syn_c0) (syn_cnnc)) syn_wtru p0076
  have p0078 := @g_n_0ex
  have p0079 := @g_a1i (.classMem (syn_c0) (syn_cvv)) syn_wtru p0078
  have p0080 :=
    @g_werestrndv syn_wtru (syn_c0) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0026 p0077 p0079
  have p0081 :=
    @g_trud
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      p0080
  have p0082 := @g_n_0lt1c
  have p0083 := @g_df0c2
  have p0084 := @g_n_0cex
  have p0085 := @g_df1c3 (syn_c0c) p0084
  have p0086 :=
    @g_n_3brtr3i (syn_c0c) (syn_c1c) (syn_cnc (syn_c0)) (syn_cnc (syn_csn (syn_c0c)))
      (syn_cltc) p0082 p0083 p0085
  have p0087 :=
    @g_pm3_2i
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))) p0081 p0086
  have p0088 :=
    @g_elimhyp4v
      (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (syn_wa (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
          (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0))) (syn_wbr (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cltc) (syn_cnc
            (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))))
      (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (syn_wa (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (syn_wa (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) E)
        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))))))
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
      (syn_wa (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
          (syn_cwe) (syn_c0))
        (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_csn (syn_c0c)))))
      (syn_wa (syn_wbr (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            S (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
          (syn_cwe) (syn_c0)) (syn_wbr (syn_cnc (syn_c0)) (syn_cltc) (syn_cnc (syn_cif
              (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
              D (syn_csn (syn_c0c))))))
      R S D
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_csn (syn_c0c))
      E (syn_c0) p0037 p0042 p0048 p0054 p0056 p0061 p0067 p0073 p0087
  have p0089 :=
    @g_simpli
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_wbr (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      p0088
  have p0143 :=
    @g_simpri
      (syn_wbr (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
          (syn_c0)))
      (syn_wbr (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            E (syn_c0))) (syn_cltc) (syn_cnc (syn_cif
            (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
            D (syn_csn (syn_c0c)))))
      p0088
  have p0144 :=
    @g_wecomparisoncutrepltfdv x
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
        (syn_csn (syn_c0c)))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) S
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E
        (syn_c0))
      dv_cache_0003 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0035 p0089 p0143
  have p0145 :=
    @g_dedth4v
      (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif
                    (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif
                    (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))) (.classEq (syn_cnc E) (syn_cnc (syn_cin (syn_cif
                (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
                D (syn_csn (syn_c0c))) (syn_cima (syn_ccnv (syn_cdif (syn_cif
                      (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cif
          (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D
          (syn_csn (syn_c0c))) (.classEq (syn_cnc (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) E (syn_c0))) (syn_cnc (syn_cin
              (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                  (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) D (syn_csn (syn_c0c))) (syn_cima
                (syn_ccnv (syn_cdif (syn_cif (syn_wa (syn_wbr S (syn_cwe) E)
                        (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) R
                      (syn_cin (syn_ckqrel (syn_clefin))
                        (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))) (syn_cid)))
                (syn_csn (.cv x)))))))
      R S D E
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_csn (syn_c0c)) (syn_csn (syn_c0c))))
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_csn (syn_c0c))
      (syn_c0) p0007 p0009 p0016 p0020 p0144
  exact p0145


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecomparisoncutreptypedliftdndv (x : Var) (D : Class) (R : Class)
    (E : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_q : q ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_q_x : q ≠ x) :
    Nominal.NPrf
      (.imp (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) :=
  by
  have dv_cache_0001 : q ∉ ((syn_csn (syn_csn (.cv x)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_q_x,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_D_q,
          not_false_eq_true])
  have dv_cache_0003 :
    q ∉
      ((Wff.classEq (syn_cnc E) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_E_q, dv_D_q, dv_R_q, dv_q_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_x, dv_E_x, dv_R_x, (Ne.symm dv_q_x),
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv x) D)
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0001 := @g_snelpw1 (syn_csn (.cv x)) (syn_cpw1 D)
  have p0002 := @g_snelpw1 (.cv x) D
  have p0003 :=
    @g_bitri (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0001 p0002
  have p0004 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv x) D) p0003
  have p0005 :=
    @g_syl
      (syn_wa (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (.cv x) D)
      (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D))) p0000 p0004
  have p0006 :=
    @g_simpr (.classMem (.cv x) D)
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0007 :=
    @g_jca
      (syn_wa (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0005 p0006
  have p0008 := @g_id (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0009 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (.cv q)
      (syn_csn (syn_csn (.cv x))) p0008
  have p0010 :=
    @g_unieqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cuni (.cv q))
      (syn_cuni (syn_csn (syn_csn (.cv x)))) p0009
  have p0011 := @g_snex (.cv x)
  have p0012 := @g_unisn (syn_csn (.cv x)) p0011
  have p0013 := @g_unieqi (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0012
  have p0014 := @g_vex x
  have p0015 := @g_unisn (.cv x) p0014
  have p0016 :=
    @g_eqtri (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x)))))
      (syn_cuni (syn_csn (.cv x))) (.cv x) p0013 p0015
  have p0017 :=
    @g_a1i (.classEq (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x))
      (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) p0016
  have p0018 :=
    @g_eqtrd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cuni (syn_cuni (.cv q)))
      (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x) p0010 p0017
  have p0019 :=
    @g_sneqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))) (syn_cuni (syn_cuni (.cv q)))
      (.cv x) p0018
  have p0020 :=
    @g_imaeq2d (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (.cv x))
      (syn_ccnv (syn_cdif R (syn_cid))) p0019
  have p0021 :=
    @g_ineq2d (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) D p0020
  have p0022 :=
    @g_nceqd (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0021
  have p0023 :=
    @g_eqeq2d (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cnc E) p0022
  have p0024 :=
    @g_rspcev
      (.classEq (syn_cnc E) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      q (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0023
  have p0025 :=
    @g_syl
      (syn_wa (.classMem (.cv x) D) (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wa (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 D)))
        (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0007 p0024
  have p0026 :=
    @g_rexlimiva
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      x D dv_cache_0004 p0025
  have p0027 :=
    @g_id
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0028 :=
    @g_a1ii
      (.imp (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.imp (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x D
          (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0026 p0027
  exact p0028

@[expose]
noncomputable def g_wecomparisoncutreptypedtargetdfdv (D : Class) (R : Class) (S : Class)
    (E : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_E_q : q ∉ E.fv) (dv_R_q : q ∉ R.fv)
    (hyp_wecomparisoncutreptypedtargetdfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
        (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ ({ q } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
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
  have fresh_x_ne_q : x ≠ q := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (E).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0005 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0006 : q ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_q, not_false_eq_true])
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
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0008 : q ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have p0000 :=
    @g_wecomparisoncutreplttargetdfdv x D R S E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_wecomparisoncutreptypedtargetdfdv_1
  have p0001 :=
    @g_wecomparisoncutreptypedliftdndv x D R E q dv_cache_0005 dv_cache_0001 dv_cache_0006
      dv_cache_0002 dv_cache_0007 dv_cache_0003 dv_cache_0008
  have p0002 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) E) (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D)))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc E) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wppcandstrictslicecutrepfixdrfdv (C : Class) (D : Class) (R : Class)
    (k : Var) (F : Class) (q : Var) (_dv_C_k : k ∉ C.fv) (dv_C_q : q ∉ C.fv)
    (_dv_D_k : k ∉ D.fv) (dv_D_q : q ∉ D.fv) (_dv_F_k : k ∉ F.fv) (dv_F_q : q ∉ F.fv)
    (_dv_R_k : k ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_k_q : k ≠ q)
    (hyp_wppcandstrictslicecutrepfixdrfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wppcandstrictslicecutrepfixdrfdv_2 : Nominal.NPrf (.classEq C (syn_cnc D))) :
    Nominal.NPrf
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))) :=
  by
  let proofSupport : Finset Var :=
    C.fv ∪ D.fv ∪ R.fv ∪ ({ k } : Finset Var) ∪ F.fv ∪ ({ q } : Finset Var)
  let s : Var := freshVar proofSupport 0
  let e : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s_ne_k : s ≠ k := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_s : k ≠ s := Ne.symm fresh_s_ne_k
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_q : s ≠ q := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_s : q ≠ s := Ne.symm fresh_s_ne_q
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_e_not_D : e ∉ D.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_e_not_R : e ∉ R.fv := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_e_ne_k : e ≠ k := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_ne_q : e ≠ q := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_e : q ≠ e := Ne.symm fresh_e_ne_q
  have fresh_s_ne_e : s ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_e_ne_s : e ≠ s := Ne.symm fresh_s_ne_e
  have dv_cache_0001 : e ≠ k := by exact (show e ≠ k from (by exact fresh_e_ne_k))
  have dv_cache_0002 : e ≠ s := by
    clear dv_cache_0001
    exact (show e ≠ s from (by exact fresh_e_ne_s))
  have dv_cache_0003 : k ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show k ≠ s from (by exact fresh_k_ne_s))
  have dv_cache_0004 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((Class.cv e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_e, not_false_eq_true])
  have dv_cache_0006 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0007 :
    q ∉
      ((syn_wa (.classMem (.cv k)
            (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e))
            (.classEq (.cv k) (syn_cnc (.cv e)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_q), dv_C_q, dv_F_q, fresh_q_ne_s,
          fresh_q_ne_e, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    e ∉
      ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_e_not_D, fresh_e_ne_k,
          fresh_e_not_R, fresh_e_ne_q, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 :
    s ∉
      ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_s_not_D, fresh_s_ne_k,
          fresh_s_not_R, fresh_s_ne_q, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 :
    e ∉
      ((Wff.classMem (.cv k) (syn_cin (syn_cwppcand F C)
            (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_e_ne_k, fresh_e_not_C, fresh_e_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    s ∉
      ((Wff.classMem (.cv k) (syn_cin (syn_cwppcand F C)
            (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_k, fresh_s_not_C, fresh_s_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_elwppcandstrictslice C k F
  have p0001 :=
    @g_biimpi
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0000
  have p0002 :=
    @g_simpld
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C) p0001
  have p0003 := @g_elwppcand C (.cv k) F
  have p0004 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C)))
      p0003
  have p0005 :=
    @g_syl
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C)))
      p0002 p0004
  have p0006 :=
    @g_simpld
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C))
      (.classMem (.cv k) (syn_cwppreach F C)) p0005
  have p0007 :=
    @g_simpld
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C) p0006
  have p0008 := @g_elhwcardswev k s e dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_biimpi (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e))
            (.classEq (.cv k) (syn_cnc (.cv e))))))
      p0008
  have p0010 :=
    @g_syl
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e))
            (.classEq (.cv k) (syn_cnc (.cv e))))))
      p0007 p0009
  have p0011 :=
    @g_simpr
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
  have p0012 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
      (syn_wbr (.cv s) (syn_cwe) (.cv e)) p0011 p0012
  have p0014 :=
    @g_simpl
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
  have p0017 :=
    @g_simprd
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C) p0001
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wbr (.cv k) (syn_cltc) C) p0014 p0017
  have p0020 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))
  have p0021 :=
    @g_syl
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
      (.classEq (.cv k) (syn_cnc (.cv e))) p0011 p0020
  have p0022 :=
    @g_a1i (.classEq C (syn_cnc D))
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      hyp_wppcandstrictslicecutrepfixdrfdv_2
  have p0023 :=
    @g_breq12d
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (.cv k) (syn_cnc (.cv e)) C (syn_cnc D) (syn_cltc) p0021 p0022
  have p0024 :=
    @g_mpbid
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (syn_wbr (.cv k) (syn_cltc) C) (syn_wbr (syn_cnc (.cv e)) (syn_cltc) (syn_cnc D))
      p0018 p0023
  have p0025 :=
    @g_jca
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (syn_wbr (.cv s) (syn_cwe) (.cv e))
      (syn_wbr (syn_cnc (.cv e)) (syn_cltc) (syn_cnc D)) p0013 p0024
  have p0026 :=
    @g_wecomparisoncutreptypedtargetdfdv D R (.cv s) (.cv e) q dv_cache_0004 dv_cache_0005
      dv_cache_0006 hyp_wppcandstrictslicecutrepfixdrfdv_1
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e))
        (syn_wbr (syn_cnc (.cv e)) (syn_cltc) (syn_cnc D)))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc (.cv e)) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0025 p0026
  have p0031 :=
    @g_eqeq1d
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (.cv k) (syn_cnc (.cv e))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0021
  have p0032 :=
    @g_rexbidv
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (.classEq (syn_cnc (.cv e)) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      q (syn_cpw1 (syn_cpw1 D)) dv_cache_0007 p0031
  have p0033 :=
    @g_mpbird
      (syn_wa (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e)))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (syn_cnc (.cv e)) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0027 p0032
  have p0034 :=
    @g_ex
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0033
  have p0035 :=
    @g_exlimdvv
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq (.cv k) (syn_cnc (.cv e))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      e s dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0034
  have p0036 :=
    @g_mpd
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e))
            (.classEq (.cv k) (syn_cnc (.cv e))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0010 p0035
  have p0037 :=
    @g_rgen
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) p0036
  exact p0037

@[expose]
noncomputable def g_wppcandstrictslicenonemptyminndv (z : Var) (C : Class) (D : Class)
    (R : Class) (k : Var) (n : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv)
    (dv_C_n : n ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_D_k : k ∉ D.fv)
    (_dv_D_n : n ∉ D.fv) (dv_D_q : q ∉ D.fv) (_dv_D_z : z ∉ D.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_R_k : k ∉ R.fv)
    (_dv_R_n : n ∉ R.fv) (dv_R_q : q ∉ R.fv) (_dv_R_z : z ∉ R.fv) (_dv_k_n : k ≠ n)
    (dv_k_q : k ≠ q) (dv_k_z : k ≠ z) (_dv_n_q : n ≠ q) (dv_n_z : n ≠ z) (_dv_q_z : q ≠ z)
    (hyp_wppcandstrictslicenonemptyminndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wppcandstrictslicenonemptyminndv_2 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppcandstrictslicenonemptyminndv_3 : Nominal.NPrf (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))) :
    Nominal.NPrf
      (.imp (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_c0)) (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ z } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({ k } : Finset Var) ∪
          ({ n } : Finset Var) ∪
        F.fv ∪
      ({ q } : Finset Var)
  let m : Var := freshVar proofSupport 0
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_ne_z : m ≠ z := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_m : z ≠ m := Ne.symm fresh_m_ne_z
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_m_not_D : m ∉ D.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_m_not_R : m ∉ R.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_m_ne_k : m ≠ k := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_ne_q : m ≠ q := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_k, not_false_eq_true])
  have dv_cache_0002 : m ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_C, not_false_eq_true])
  have dv_cache_0003 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_q, not_false_eq_true])
  have dv_cache_0004 : k ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_k, not_false_eq_true])
  have dv_cache_0005 : m ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_D, not_false_eq_true])
  have dv_cache_0006 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0007 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_k, not_false_eq_true])
  have dv_cache_0008 : m ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_F, not_false_eq_true])
  have dv_cache_0009 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_q, not_false_eq_true])
  have dv_cache_0010 : k ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_k, not_false_eq_true])
  have dv_cache_0011 : m ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_R, not_false_eq_true])
  have dv_cache_0012 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0013 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0014 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0015 : m ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show m ≠ q from (by exact fresh_m_ne_q))
  have dv_cache_0016 : z ∉ (C).fv :=
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
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0017 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_z, not_false_eq_true])
  have dv_cache_0018 : k ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show k ≠ z from (by exact dv_k_z))
  have dv_cache_0019 : m ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show m ≠ z from (by exact fresh_m_ne_z))
  have dv_cache_0020 : z ∉ ((Wff.classEq (.cv n) (.cv m))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_n_z), fresh_z_ne_m, or_false,
          not_false_eq_true])
  have dv_cache_0021 : n ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_m, not_false_eq_true])
  have dv_cache_0022 : n ∉ ((syn_cwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0023 :
    n ∉ ((syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_n, dv_F_n, fresh_n_ne_m, dv_n_z,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0024 :
    m ∉
      ((syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_not_C, fresh_m_not_F,
          fresh_m_ne_n, fresh_m_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @g_wppcandstrictsliceleastdndvv C D R k m F q dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 hyp_wppcandstrictslicenonemptyminndv_1
      hyp_wppcandstrictslicenonemptyminndv_2 hyp_wppcandstrictslicenonemptyminndv_3
  have p0001 :=
    @g_wppcandstrictsliceleastextenddv z C k m F dv_cache_0001 dv_cache_0002 dv_cache_0016
      dv_cache_0007 dv_cache_0008 dv_cache_0017 dv_cache_0013 dv_cache_0018 dv_cache_0019
  have p0002 :=
    @g_id
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))
  have p0003 := @g_id (.classEq (.cv n) (.cv m))
  have p0004 :=
    @g_breq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (.cv z) (syn_clec) p0003
  have p0005 :=
    @g_ralbidv (.classEq (.cv n) (.cv m)) (syn_wbr (.cv n) (syn_clec) (.cv z))
      (syn_wbr (.cv m) (syn_clec) (.cv z)) z (syn_cwppcand F C) dv_cache_0020 p0004
  have p0006 :=
    @g_rspcev (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))
      (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))) n (.cv m)
      (syn_cwppcand F C) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0005
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0002 p0006
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv m)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wral k
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0001 p0007
  have p0009 :=
    @g_rexlimiva
      (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
      dv_cache_0024 p0008
  have p0010 :=
    @g_syl
      (syn_wne (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (syn_wrex m (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_wral k (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0000 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppcandselfndv (C : Class) (F : Class)
    (hyp_wppcandselfndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cwppcand F C))) :=
  by
  have p0000 := @g_id (.classMem C (syn_chwcards (syn_cvv)))
  have p0001 := @g_hwcardssnc (syn_cvv)
  have p0002 := @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) C
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_nclecid C
  have p0005 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cncs))
      (syn_wbr C (syn_clec) C) p0003 p0004
  have p0006 :=
    @g_jca (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wbr C (syn_clec) C) p0000 p0005
  have p0012 := @g_elimasn (syn_clec) C C
  have p0013 := (Nominal.biimpRefl (syn_wbr C (syn_clec) C))
  have p0014 :=
    @g_bitr4i (.classMem C (syn_cima (syn_clec) (syn_csn C)))
      (.classMem (syn_cop C C) (syn_clec)) (syn_wbr C (syn_clec) C) p0012 p0013
  have p0015 :=
    @g_sylibr (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C)
      (.classMem C (syn_cima (syn_clec) (syn_csn C))) p0005 p0014
  have p0016 := @g_cnvex F hyp_wppcandselfndv_1
  have p0017 := @g_wppimagefn (syn_ccnv F) p0016
  have p0018 := @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0019 := Nominal.mp p0017 p0018
  have p0021 := @g_imageex (syn_ccnv F) p0016
  have p0022 := @g_elfuns (syn_cimage (syn_ccnv F)) p0021
  have p0023 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (syn_wfun (syn_cimage (syn_ccnv F))) p0019 p0022
  have p0024 := @g_lecex
  have p0025 := @g_snex C
  have p0026 := @g_imaex (syn_clec) (syn_csn C) p0024 p0025
  have p0029 := @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0030 := Nominal.mp p0017 p0029
  have p0031 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0026 p0030
  have p0032 := @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0037 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0032 p0030
  have p0038 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
      (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))
      p0023 p0031 p0037
  have p0039 :=
    @g_wpporbit0ndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0040 := Nominal.mp p0038 p0039
  have p0064 :=
    @g_wpporbitfnndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0065 := Nominal.mp p0038 p0064
  have p0066 := @g_peano1
  have p0067 :=
    @g_fnfvelrn (syn_cnnc) (syn_c0c)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0068 :=
    @g_mp2an
      (syn_wfn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cnnc))
      (.classMem (syn_c0c) (syn_cnnc))
      (.classMem
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_c0c))
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      p0065 p0066 p0067
  have p0069 :=
    @g_eqeltrri
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_c0c))
      (syn_cima (syn_clec) (syn_csn C))
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      p0040 p0068
  have p0070 :=
    @g_a1i
      (.classMem (syn_cima (syn_clec) (syn_csn C))
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      (.classMem C (syn_chwcards (syn_cvv))) p0069
  have p0071 :=
    @g_jca (.classMem C (syn_chwcards (syn_cvv)))
      (.classMem C (syn_cima (syn_clec) (syn_csn C)))
      (.classMem (syn_cima (syn_clec) (syn_csn C))
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      p0015 p0070
  have p0072 :=
    @g_elunii C (syn_cima (syn_clec) (syn_csn C))
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
  have p0073 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem C (syn_cima (syn_clec) (syn_csn C)))
        (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_crn
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))))
      (.classMem C (syn_cuni (syn_crn
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))))
      p0071 p0072
  have p0074 := (Nominal.classEqRefl (syn_cwppreach F C))
  have p0075 :=
    @g_eleq2i (syn_cwppreach F C)
      (syn_cuni
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      C p0074
  have p0076 :=
    @g_sylibr (.classMem C (syn_chwcards (syn_cvv)))
      (.classMem C (syn_cuni (syn_crn
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))))
      (.classMem C (syn_cwppreach F C)) p0073 p0075
  have p0077 :=
    @g_jca (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C))
      (.classMem C (syn_cwppreach F C)) p0006 p0076
  have p0078 := @g_elwppcand C C F
  have p0079 :=
    @g_sylibr (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wa (syn_wa (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C))
        (.classMem C (syn_cwppreach F C)))
      (.classMem C (syn_cwppcand F C)) p0077 p0078
  exact p0079

@[expose]
noncomputable def g_wppcandstrictsliceemptyminndv (C : Class) (k : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (hyp_wppcandstrictsliceemptyminndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppcandstrictsliceemptyminndv_2 :
      Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_c0)) (syn_wa (.classMem C (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv k))))) :=
  by
  have dv_cache_0001 :
    k ∉
      ((Wff.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_c0))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_k,
          dv_F_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_wppcandselfndv C F hyp_wppcandstrictsliceemptyminndv_1
  have p0001 := Nominal.mp hyp_wppcandstrictsliceemptyminndv_2 p0000
  have p0002 :=
    @g_a1i (.classMem C (syn_cwppcand F C))
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      p0001
  have p0003 := @g_hwcardssnc (syn_cvv)
  have p0004 := @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) C
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := Nominal.mp hyp_wppcandstrictsliceemptyminndv_2 p0005
  have p0007 := @g_nclecid C
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_a1i (syn_wbr C (syn_clec) C)
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      p0008
  have p0010 :=
    @g_simpr
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (.classMem (.cv k) (syn_cwppcand F C))
  have p0011 := @g_noel (.cv k)
  have p0012 :=
    @g_a1i (.neg (.classMem (.cv k) (syn_c0)))
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      p0011
  have p0013 :=
    @g_simpl
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (.classMem (.cv k) (syn_cwppcand F C))
  have p0014 :=
    @g_eleq2d
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)
      (.cv k) p0013
  have p0015 :=
    @g_biimpd
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_c0)) p0014
  have p0016 :=
    @g_con3d
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (.classMem (.cv k) (syn_c0)) p0015
  have p0017 :=
    @g_mpd
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (.neg (.classMem (.cv k) (syn_c0)))
      (.neg (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))))
      p0012 p0016
  have p0019 := @g_elwppcandstrictslice C k F
  have p0020 :=
    @g_biimpri
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0019
  have p0021 :=
    @g_ex (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      p0020
  have p0022 :=
    @g_syl
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (.classMem (.cv k) (syn_cwppcand F C))
      (.imp (syn_wbr (.cv k) (syn_cltc) C) (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))))
      p0010 p0021
  have p0023 :=
    @g_con3d
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (syn_wbr (.cv k) (syn_cltc) C)
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      p0022
  have p0024 :=
    @g_mpd
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (.neg (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))))
      (.neg (syn_wbr (.cv k) (syn_cltc) C)) p0017 p0023
  have p0025 :=
    @g_jca
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)) p0010
      p0024
  have p0026 := @g_wppcandnltpivoteqd C k F
  have p0027 :=
    @g_syl
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (.classEq (.cv k) C) p0025 p0026
  have p0028 :=
    @g_breqtrrd
      (syn_wa (.classEq
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))
        (.classMem (.cv k) (syn_cwppcand F C)))
      C C (.cv k) (syn_clec) p0009 p0027
  have p0029 :=
    @g_ex
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr C (syn_clec) (.cv k)) p0028
  have p0030 :=
    @g_ralrimiv
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (syn_wbr C (syn_clec) (.cv k)) k (syn_cwppcand F C) dv_cache_0001 p0029
  have p0031 :=
    @g_jca
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (.classMem C (syn_cwppcand F C))
      (syn_wral k (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv k))) p0002 p0030
  exact p0031

@[expose]
noncomputable def g_wppcandstrictsliceemptypublicminndv (z : Var) (C : Class) (n : Var)
    (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_n : n ∉ F.fv)
    (dv_F_z : z ∉ F.fv) (dv_n_z : n ≠ z)
    (hyp_wppcandstrictsliceemptypublicminndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppcandstrictsliceemptypublicminndv_2 :
      Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
          (syn_c0)) (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) :=
  by
  have dv_cache_0001 : z ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0002 : z ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_z, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv n) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_n_z), dv_C_z, or_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((syn_cwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0006 :
    n ∉ ((syn_wral z (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_C_n, dv_F_n, dv_n_z, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppcandstrictsliceemptyminndv C z F dv_cache_0001 dv_cache_0002
      hyp_wppcandstrictsliceemptypublicminndv_1 hyp_wppcandstrictsliceemptypublicminndv_2
  have p0001 := @g_id (.classEq (.cv n) C)
  have p0002 := @g_breq1d (.classEq (.cv n) C) (.cv n) C (.cv z) (syn_clec) p0001
  have p0003 :=
    @g_ralbidv (.classEq (.cv n) C) (syn_wbr (.cv n) (syn_clec) (.cv z))
      (syn_wbr C (syn_clec) (.cv z)) z (syn_cwppcand F C) dv_cache_0003 p0002
  have p0004 :=
    @g_rspcev (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))
      (syn_wral z (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv z))) n C
      (syn_cwppcand F C) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0003
  have p0005 :=
    @g_syl
      (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_c0))
      (syn_wa (.classMem C (syn_cwppcand F C))
        (syn_wral z (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wppcandminfixedpivotdrfdv (z : Var) (C : Class) (D : Class)
    (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z)
    (hyp_wppcandminfixedpivotdrfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wppcandminfixedpivotdrfdv_2 : Nominal.NPrf (.classEq C (syn_cnc D)))
    (hyp_wppcandminfixedpivotdrfdv_3 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) :=
  by
  let proofSupport : Finset Var :=
    ({ z } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({ n } : Finset Var) ∪ F.fv
  let c : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_ne_z : k ≠ z := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_k_not_D : k ∉ D.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_k_not_R : k ∉ R.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_ne_z : q ≠ z := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_q : n ≠ q := Ne.symm fresh_q_ne_n
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_c_ne_s : c ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_c : s ≠ c := Ne.symm fresh_c_ne_s
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_k_ne_q : k ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have dv_cache_0001 : d ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have dv_cache_0002 : s ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_D, not_false_eq_true])
  have dv_cache_0003 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0004 : s ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_R, not_false_eq_true])
  have dv_cache_0005 :
    d ∉ ((syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_d_not_R, fresh_d_not_D, fresh_d_ne_c,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    s ∉ ((syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_s_not_R, fresh_s_not_D, fresh_s_ne_c,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0008 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0009 : c ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show c ≠ s from (by exact fresh_c_ne_s))
  have dv_cache_0010 : c ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0011 :
    c ∉ ((Wff.imp (.classEq C (syn_cnc D)) (.classMem C (syn_chwcards (syn_cvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_c_not_C, fresh_c_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0013 : z ∉ (C).fv :=
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
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0014 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0015 : z ∉ (F).fv :=
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
        simp only [dv_F_z, not_false_eq_true])
  have dv_cache_0016 : n ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show n ≠ z from (by exact dv_n_z))
  have dv_cache_0017 : k ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0018 : q ∉ (C).fv :=
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
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0019 : k ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_D, not_false_eq_true])
  have dv_cache_0020 : q ∉ (D).fv :=
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
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0021 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0022 : q ∉ (F).fv :=
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
        simp only [fresh_q_not_F, not_false_eq_true])
  have dv_cache_0023 : k ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_R, not_false_eq_true])
  have dv_cache_0024 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0025 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show k ≠ q from (by exact fresh_k_ne_q))
  have dv_cache_0026 : n ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_n, not_false_eq_true])
  have dv_cache_0027 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0028 : n ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_n, not_false_eq_true])
  have dv_cache_0029 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0030 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show k ≠ n from (by exact fresh_k_ne_n))
  have dv_cache_0031 : k ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show k ≠ z from (by exact fresh_k_ne_z))
  have dv_cache_0032 : n ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have dv_cache_0033 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have p0000 := @g_ncex D
  have p0001 := @g_eqeltri C (syn_cnc D) (syn_cvv) hyp_wppcandminfixedpivotdrfdv_2 p0000
  have p0002 := @g_id (.classEq (.cv c) C)
  have p0003 := @g_eqeq1d (.classEq (.cv c) C) (.cv c) C (syn_cnc D) p0002
  have p0005 := @g_eleq1d (.classEq (.cv c) C) (.cv c) C (syn_chwcards (syn_cvv)) p0002
  have p0006 :=
    @g_imbi12d (.classEq (.cv c) C) (.classEq (.cv c) (syn_cnc D))
      (.classEq C (syn_cnc D)) (.classMem (.cv c) (syn_chwcards (syn_cvv)))
      (.classMem C (syn_chwcards (syn_cvv))) p0003 p0005
  have p0007 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D))
      hyp_wppcandminfixedpivotdrfdv_1
  have p0008 := @g_id (.classEq (.cv c) (syn_cnc D))
  have p0009 :=
    @g_jca (.classEq (.cv c) (syn_cnc D)) (syn_wbr R (syn_cwe) D)
      (.classEq (.cv c) (syn_cnc D)) p0007 p0008
  have p0010 := @g_brex R D (syn_cwe)
  have p0011 := Nominal.mp hyp_wppcandminfixedpivotdrfdv_1 p0010
  have p0012 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0013 := Nominal.mp p0011 p0012
  have p0016 := @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0017 := Nominal.mp p0011 p0016
  have p0018 := @g_simpr (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0019 := @g_simpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0020 :=
    @g_breq12d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv s) R (.cv d) D
      (syn_cwe) p0018 p0019
  have p0022 :=
    @g_nceqd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv d) D p0019
  have p0023 :=
    @g_eqeq2d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (syn_cnc (.cv d))
      (syn_cnc D) (.cv c) p0022
  have p0024 :=
    @g_anbi12d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr R (syn_cwe) D)
      (.classEq (.cv c) (syn_cnc (.cv d))) (.classEq (.cv c) (syn_cnc D)) p0020 p0023
  have p0025 :=
    @g_spc2ev
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D))) d s D R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0013 p0017 p0024
  have p0026 :=
    @g_syl (.classEq (.cv c) (syn_cnc D))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv c) (syn_cnc (.cv d))))))
      p0009 p0025
  have p0027 := @g_elhwcardswev c s d dv_cache_0008 dv_cache_0007 dv_cache_0009
  have p0028 :=
    @g_biimpri (.classMem (.cv c) (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv c) (syn_cnc (.cv d))))))
      p0027
  have p0029 :=
    @g_syl (.classEq (.cv c) (syn_cnc D))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv c) (syn_cnc (.cv d))))))
      (.classMem (.cv c) (syn_chwcards (syn_cvv))) p0026 p0028
  have p0030 :=
    @g_vtoclg
      (.imp (.classEq (.cv c) (syn_cnc D)) (.classMem (.cv c) (syn_chwcards (syn_cvv))))
      (.imp (.classEq C (syn_cnc D)) (.classMem C (syn_chwcards (syn_cvv)))) c C (syn_cvv)
      dv_cache_0010 dv_cache_0011 p0006 p0029
  have p0031 := Nominal.mp p0001 p0030
  have p0032 := Nominal.mp hyp_wppcandminfixedpivotdrfdv_2 p0031
  have p0033 :=
    @g_wppcandstrictsliceemptypublicminndv z C n F dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wppcandminfixedpivotdrfdv_3 p0032
  have p0034 :=
    @g_wppcandstrictslicecutrepfixdrfdv C D R k F q dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 hyp_wppcandminfixedpivotdrfdv_1 hyp_wppcandminfixedpivotdrfdv_2
  have p0035 :=
    @g_wppcandstrictslicenonemptyminndv z C D R k n F q dv_cache_0017 dv_cache_0012
      dv_cache_0018 dv_cache_0013 dv_cache_0019 dv_cache_0026 dv_cache_0020 dv_cache_0027
      dv_cache_0021 dv_cache_0014 dv_cache_0022 dv_cache_0015 dv_cache_0023 dv_cache_0028
      dv_cache_0024 dv_cache_0029 dv_cache_0030 dv_cache_0025 dv_cache_0031 dv_cache_0032
      dv_cache_0016 dv_cache_0033 hyp_wppcandminfixedpivotdrfdv_1
      hyp_wppcandminfixedpivotdrfdv_3 p0034
  have p0036 :=
    @g_pm2_61ine
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)
      p0033 p0035
  exact p0036

@[expose]
noncomputable def g_wecomparisondefaultemptywe :
    Nominal.NPrf
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0)) :=
  by
  have p0000 := @g_finlewe
  have p0001 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) syn_wtru p0000
  have p0002 := @g_n_0ss (syn_cnnc)
  have p0003 := @g_a1i (syn_wss (syn_c0) (syn_cnnc)) syn_wtru p0002
  have p0004 := @g_n_0ex
  have p0005 := @g_a1i (.classMem (syn_c0) (syn_cvv)) syn_wtru p0004
  have p0006 :=
    @g_werestrndv syn_wtru (syn_c0) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0001 p0003 p0005
  have p0007 :=
    @g_trud
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppcandminfixedpivotpairdrfdv (z : Var) (C : Class) (D : Class)
    (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z)
    (hyp_wppcandminfixedpivotpairdrfdv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
        (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) :=
  by
  have dv_cache_0001 : z ∉ ((syn_cwppcand F C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_z, dv_F_z, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉
      ((syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_z,
          dv_R_z, dv_D_z, dv_F_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((syn_cwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0004 :
    n ∉
      ((syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_n,
          dv_R_n, dv_D_n, dv_F_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    n ∉
      ((Wff.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_n,
          dv_R_n, dv_D_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    n ∉
      ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_n,
          dv_R_n, dv_D_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    z ∉
      ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_z,
          dv_R_z, dv_D_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    n ∉
      ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_D_n,
          dv_R_n, dv_C_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_D_z,
          dv_R_z, dv_C_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0011 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_z, not_false_eq_true])
  have dv_cache_0012 :
    n ∉
      ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_R_n,
          dv_D_n, dv_C_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    z ∉
      ((syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_R_z,
          dv_D_z, dv_C_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : n ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show n ≠ z from (by exact dv_n_z))
  have p0000 :=
    @g_biid
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
        (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))))
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      p0000
  have p0003 :=
    @g_a1i
      (syn_wb (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
        (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))))
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      p0000
  have p0004 :=
    @g_id
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
  have p0005 :=
    @g_sneqd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      C
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))
      p0004
  have p0006 :=
    @g_imaeq2d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_csn C)
      (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_ccnv (syn_clec)) p0005
  have p0007 :=
    @g_ineq2d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
      (syn_cima (syn_ccnv (syn_clec)) (syn_csn
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0)))))
      (syn_chwcards (syn_cvv)) p0006
  have p0008 :=
    @g_eqidd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cimage (syn_ccnv F))
  have p0011 :=
    @g_imaeq2d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_csn C)
      (syn_csn (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_clec) p0005
  have p0012 :=
    @g_jca
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)))
      (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
              (syn_cnc (syn_c0))))))
      p0008 p0011
  have p0013 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))
      (syn_cima (syn_clec) (syn_csn C))
      (syn_cima (syn_clec) (syn_csn
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0)))))
  have p0014 :=
    @g_syl
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)))
        (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn
              (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
                (syn_cnc (syn_c0)))))))
      (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn
              (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
                (syn_cnc (syn_c0)))))))
      p0012 p0013
  have p0015 :=
    @g_rneqd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
              (syn_cnc (syn_c0))))))
      p0014
  have p0016 :=
    @g_unieqd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn
              (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
                (syn_cnc (syn_c0)))))))
      p0015
  have p0017 := (Nominal.classEqRefl (syn_cwppreach F C))
  have p0018 :=
    (Nominal.classEqRefl (syn_cwppreach F
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0)))))
  have p0019 :=
    @g_n_3eqtr4g
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cuni
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn
                (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
                  (syn_cnc (syn_c0))))))))
      (syn_cwppreach F C)
      (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      p0016 p0017 p0018
  have p0020 :=
    @g_ineq12d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
              (syn_cnc (syn_c0))))))
      (syn_cwppreach F C)
      (syn_cwppreach F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      p0007 p0019
  have p0021 := (Nominal.classEqRefl (syn_cwppcand F C))
  have p0022 :=
    (Nominal.classEqRefl (syn_cwppcand F
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0)))))
  have p0023 :=
    @g_n_3eqtr4g
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
        (syn_cwppreach F C))
      (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn
              (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
                (syn_cnc (syn_c0)))))) (syn_cwppreach F
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0)))))
      (syn_cwppcand F C)
      (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      p0020 p0021 p0022
  have p0044 :=
    @g_raleqdv
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_wbr (.cv n) (syn_clec) (.cv z)) z (syn_cwppcand F C)
      (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      dv_cache_0001 dv_cache_0002 p0023
  have p0045 :=
    @g_rexeqbidv
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))
      (syn_wral z (syn_cwppcand F
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0)))) (syn_wbr (.cv n) (syn_clec) (.cv z)))
      n (syn_cwppcand F C)
      (syn_cwppcand F (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0023 p0044
  have p0046 :=
    @g_id
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0047 :=
    @g_eqidd
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      D
  have p0048 :=
    @g_breq12d
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      R
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      D D (syn_cwe) p0046 p0047
  have p0049 :=
    @g_eqidd
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      C
  have p0051 :=
    @g_nceqd
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      D D p0047
  have p0052 :=
    @g_eqeq12d
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      C C (syn_cnc D) (syn_cnc D) p0049 p0051
  have p0053 :=
    @g_anbi12d
      (.classEq R (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_wbr R (syn_cwe) D)
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D)
      (.classEq C (syn_cnc D)) (.classEq C (syn_cnc D)) p0048 p0052
  have p0054 :=
    @g_eqidd
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0055 :=
    @g_id
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0056 :=
    @g_breq12d
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cwe) p0054 p0055
  have p0057 :=
    @g_eqidd
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      C
  have p0059 :=
    @g_nceqd
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      D (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      p0055
  have p0060 :=
    @g_eqeq12d
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      C C (syn_cnc D)
      (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      p0057 p0059
  have p0061 :=
    @g_anbi12d
      (.classEq D
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D)
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (.classEq C (syn_cnc D))
      (.classEq C (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
      p0056 p0060
  have p0062 :=
    @g_eqidd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0063 :=
    @g_eqidd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0064 :=
    @g_breq12d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cwe) p0062 p0063
  have p0067 :=
    @g_nceqd
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0063
  have p0068 :=
    @g_eqeq12d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      C
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))
      (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      p0004 p0067
  have p0069 :=
    @g_anbi12d
      (.classEq C (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (.classEq C (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
      (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))) (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
      p0064 p0068
  have p0070 :=
    @g_id
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
  have p0071 :=
    @g_eqidd
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_c0)
  have p0072 :=
    @g_breq12d
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_c0) (syn_c0) (syn_cwe) p0070 p0071
  have p0073 :=
    @g_eqidd
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_cnc (syn_c0))
  have p0075 :=
    @g_nceqd
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_c0) (syn_c0) p0071
  have p0076 :=
    @g_eqeq12d
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) p0073
      p0075
  have p0077 :=
    @g_anbi12d
      (.classEq (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))))
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
      (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0)))
      (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) p0072 p0076
  have p0078 :=
    @g_eqidd
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0079 :=
    @g_id
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
  have p0080 :=
    @g_breq12d
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_c0)
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cwe) p0078 p0079
  have p0081 :=
    @g_eqidd
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cnc (syn_c0))
  have p0083 :=
    @g_nceqd
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_c0)
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0079
  have p0084 :=
    @g_eqeq12d
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cnc (syn_c0)) (syn_cnc (syn_c0)) (syn_cnc (syn_c0))
      (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      p0081 p0083
  have p0085 :=
    @g_anbi12d
      (.classEq (syn_c0)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0)))
      (.classEq (syn_cnc (syn_c0)) (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
      p0080 p0084
  have p0086 :=
    @g_eqidd
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0087 :=
    @g_eqidd
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
  have p0088 :=
    @g_breq12d
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cwe) p0086 p0087
  have p0089 :=
    @g_id
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
  have p0091 :=
    @g_nceqd
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)) p0087
  have p0092 :=
    @g_eqeq12d
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_cnc (syn_c0))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))
      (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_cnc (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      p0089 p0091
  have p0093 :=
    @g_anbi12d
      (.classEq (syn_cnc (syn_c0))
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (.classEq (syn_cnc (syn_c0)) (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
      (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))) (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
      p0088 p0092
  have p0094 := @g_wecomparisondefaultemptywe
  have p0095 := @g_eqid (syn_cnc (syn_c0))
  have p0096 :=
    @g_pm3_2i
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))) p0094 p0095
  have p0097 :=
    @g_elimhyp3v (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
      (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) D)
        (.classEq C (syn_cnc D)))
      (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
        (.classEq C (syn_cnc
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))))
      (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
        (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0))) (syn_cnc
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))))
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))))
      (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe) (syn_c0))
        (.classEq (syn_cnc (syn_c0)) (syn_cnc (syn_c0))))
      (syn_wa (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
        (.classEq (syn_cnc (syn_c0)) (syn_cnc
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))))
      R D C (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      (syn_cnc (syn_c0)) p0053 p0061 p0069 p0077 p0085 p0093 p0096
  have p0098 :=
    @g_simpl
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))) (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
  have p0099 := Nominal.mp p0097 p0098
  have p0152 :=
    @g_simpr
      (syn_wbr (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))) (syn_cwe)
        (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0)))
      (.classEq (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
          (syn_cnc (syn_c0))) (syn_cnc
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))))
  have p0153 := Nominal.mp p0097 p0152
  have p0154 :=
    @g_wppcandminfixedpivotdrfdv z
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C (syn_cnc (syn_c0)))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) D (syn_c0))
      (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) R
        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
      n F dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0099 p0153
      hyp_wppcandminfixedpivotpairdrfdv_1
  have p0155 :=
    @g_dedth3v (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand F
          (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
            (syn_cnc (syn_c0)))) (syn_wral z (syn_cwppcand F
            (syn_cif (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))) C
              (syn_cnc (syn_c0)))) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      R D C (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      (syn_cnc (syn_c0)) p0001 p0003 p0045 p0154
  exact p0155


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppcandminfixedpivotsetdeddrfdv (z : Var) (C : Class) (D : Class)
    (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z) :
    Nominal.NPrf
      (.imp (.classMem F (syn_cvv))
        (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
          (syn_wrex n (syn_cwppcand F C)
            (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ z } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({ n } : Finset Var) ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cimage (syn_ccnv F))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cimage (syn_ccnv F))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_F,
          not_false_eq_true])
  have dv_cache_0003 :
    x ∉ ((syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    y ∉ ((syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉ ((Wff.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((Wff.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : z ∉ ((syn_cwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_z, dv_F_z, or_false, not_false_eq_true])
  have dv_cache_0009 :
    z ∉ ((syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_z,
          dv_F_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((syn_cwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0011 :
    n ∉ ((syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_C_n,
          dv_F_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    n ∉ ((Wff.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_F_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0014 : z ∉ (C).fv :=
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
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0015 : n ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_n, not_false_eq_true])
  have dv_cache_0016 : z ∉ (D).fv :=
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
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((syn_cif (.classMem F (syn_cvv)) F (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_F_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_cif (.classMem F (syn_cvv)) F (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_F_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : n ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_n, not_false_eq_true])
  have dv_cache_0020 : z ∉ (R).fv :=
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
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0021 : n ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show n ≠ z from (by exact dv_n_z))
  have p0000 := @g_biid (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
        (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D))))
      (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) p0000
  have p0002 :=
    @g_eqidd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0003 := @g_id (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
  have p0004 :=
    @g_cnveqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) F
      (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) p0003
  have p0005 :=
    @g_imaeq1d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (syn_ccnv F)
      (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x) p0004
  have p0006 :=
    @g_eqeq2d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cima (syn_ccnv F) (.cv x))
      (syn_cima (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x)) (.cv y)
      p0005
  have p0007 := @g_vex x
  have p0008 := @g_vex y
  have p0009 := @g_brimage (.cv x) (.cv y) (syn_ccnv F) p0007 p0008
  have p0012 :=
    @g_brimage (.cv x) (.cv y) (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      p0007 p0008
  have p0013 :=
    @g_n_3bitr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (.classEq (.cv y) (syn_cima (syn_ccnv F) (.cv x)))
      (.classEq (.cv y)
        (syn_cima (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) (.cv x)))
      (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y))
      (syn_wbr (.cv x)
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y))
      p0006 p0009 p0012
  have p0014 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y)))
  have p0015 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv F))) p0014
  have p0016 :=
    (Nominal.biimpRefl (syn_wbr (.cv x)
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y)))
  have p0017 :=
    @g_bicomi
      (syn_wbr (.cv x)
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))))
      p0016
  have p0018 :=
    @g_n_3bitr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_wbr (.cv x) (syn_cimage (syn_ccnv F)) (.cv y))
      (syn_wbr (.cv x)
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cimage (syn_ccnv F)))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))))
      p0013 p0015 p0017
  have p0019 :=
    @g_eqrelrdv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0))) x y
      (syn_cimage (syn_ccnv F))
      (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0018
  have p0020 :=
    @g_eqidd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cima (syn_clec) (syn_csn C))
  have p0021 :=
    @g_jca (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (.classEq (syn_cimage (syn_ccnv F))
        (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))))
      (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))) p0019
      p0020
  have p0022 :=
    @g_freceq12 (syn_cimage (syn_ccnv F))
      (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))
      (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))
  have p0023 :=
    @g_syl (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_wa (.classEq (syn_cimage (syn_ccnv F))
          (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))))
        (.classEq (syn_cima (syn_clec) (syn_csn C)) (syn_cima (syn_clec) (syn_csn C))))
      (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))
          (syn_cima (syn_clec) (syn_csn C))))
      p0021 p0022
  have p0024 :=
    @g_rneqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))
        (syn_cima (syn_clec) (syn_csn C)))
      p0023
  have p0025 :=
    @g_unieqd (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))
          (syn_cima (syn_clec) (syn_csn C))))
      p0024
  have p0026 := (Nominal.classEqRefl (syn_cwppreach F C))
  have p0027 :=
    (Nominal.classEqRefl (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C))
  have p0028 :=
    @g_n_3eqtr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cuni
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      (syn_cuni (syn_crn
          (syn_cfrec (syn_cimage (syn_ccnv (syn_cif (.classMem F (syn_cvv)) F (syn_c0))))
            (syn_cima (syn_clec) (syn_csn C)))))
      (syn_cwppreach F C) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
      p0025 p0026 p0027
  have p0029 :=
    @g_ineq12d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_cwppreach F C) (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
      p0002 p0028
  have p0030 := (Nominal.classEqRefl (syn_cwppcand F C))
  have p0031 :=
    (Nominal.classEqRefl (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C))
  have p0032 :=
    @g_n_3eqtr4g (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
        (syn_cwppreach F C))
      (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
        (syn_cwppreach (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C))
      (syn_cwppcand F C) (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
      p0029 p0030 p0031
  have p0064 :=
    @g_raleqdv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_wbr (.cv n) (syn_clec) (.cv z)) z (syn_cwppcand F C)
      (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C) dv_cache_0008
      dv_cache_0009 p0032
  have p0065 :=
    @g_rexeqbidv (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))
      (syn_wral z (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
        (syn_wbr (.cv n) (syn_clec) (.cv z)))
      n (syn_cwppcand F C) (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
      dv_cache_0010 dv_cache_0011 dv_cache_0012 p0032 p0064
  have p0066 :=
    @g_imbi12d (.classEq F (syn_cif (.classMem F (syn_cvv)) F (syn_c0)))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      (syn_wrex n (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
        (syn_wral z (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
          (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0001 p0065
  have p0067 := @g_tru
  have p0068 := @g_simpr syn_wtru (.classMem F (syn_cvv))
  have p0069 := @g_n_0ex
  have p0070 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) (syn_wa syn_wtru (.neg (.classMem F (syn_cvv))))
      p0069
  have p0071 :=
    @g_ifclda syn_wtru (.classMem F (syn_cvv)) F (syn_c0) (syn_cvv) p0068 p0070
  have p0072 := Nominal.mp p0067 p0071
  have p0073 :=
    @g_wppcandminfixedpivotpairdrfdv z C D R n
      (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 p0072
  have p0074 :=
    @g_dedth (.classMem F (syn_cvv))
      (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
        (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))))
      (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classEq C (syn_cnc D)))
        (syn_wrex n (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
          (syn_wral z (syn_cwppcand (syn_cif (.classMem F (syn_cvv)) F (syn_c0)) C)
            (syn_wbr (.cv n) (syn_clec) (.cv z)))))
      F (syn_c0) p0066 p0073
  exact p0074

@[expose]
noncomputable def g_wppcandminhwndv (z : Var) (C : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_n_z : n ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ z } : Finset Var) ∪ C.fv ∪ ({ n } : Finset Var) ∪ F.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_ne_z : s ≠ z := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_s : z ≠ s := Ne.symm fresh_s_ne_z
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_ne_n : s ≠ n := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_s : n ≠ s := Ne.symm fresh_s_ne_n
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_ne_z : d ≠ z := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_d : z ≠ d := Ne.symm fresh_d_ne_z
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_d : n ≠ d := Ne.symm fresh_d_ne_n
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_s_ne_c : s ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_s : c ≠ s := Ne.symm fresh_s_ne_c
  have fresh_d_ne_c : d ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have dv_cache_0001 : s ∉ ((Wff.classEq (.cv c) C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_c, fresh_s_not_C, or_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((Wff.classEq (.cv c) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_c, fresh_d_not_C, or_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0004 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0005 : c ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show c ≠ s from (by exact fresh_c_ne_s))
  have dv_cache_0006 : c ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0007 :
    c ∉
      ((syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
              (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
                (.classEq C (syn_cnc (.cv d)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_not_C, fresh_c_ne_s,
          fresh_c_ne_d, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0009 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_d, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_d, not_false_eq_true])
  have dv_cache_0012 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0013 : z ∉ (F).fv :=
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
        simp only [dv_F_z, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_s, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv s)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_s, not_false_eq_true])
  have dv_cache_0016 : n ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show n ≠ z from (by exact dv_n_z))
  have dv_cache_0017 :
    d ∉
      ((syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_d_not_C, fresh_d_not_F,
          fresh_d_ne_n, fresh_d_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0018 :
    s ∉
      ((syn_wrex n (syn_cwppcand F C)
          (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_s_not_C, fresh_s_not_F,
          fresh_s_ne_n, fresh_s_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0019 : d ∉ ((Wff.classMem F (syn_cvv))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_d_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : s ∉ ((Wff.classMem F (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_s_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (.classMem C (syn_chwcards (syn_cvv)))
  have p0001 := @g_elex C (syn_chwcards (syn_cvv))
  have p0002 := @g_id (.classEq (.cv c) C)
  have p0003 := @g_eleq1d (.classEq (.cv c) C) (.cv c) C (syn_chwcards (syn_cvv)) p0002
  have p0005 := @g_eqeq1d (.classEq (.cv c) C) (.cv c) C (syn_cnc (.cv d)) p0002
  have p0006 :=
    @g_anbi2d (.classEq (.cv c) C) (.classEq (.cv c) (syn_cnc (.cv d)))
      (.classEq C (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0005
  have p0007 :=
    @g_exbidv (.classEq (.cv c) C)
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))) s
      dv_cache_0001 p0006
  have p0008 :=
    @g_exbidv (.classEq (.cv c) C)
      (syn_wex s
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))))
      (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))
      d dv_cache_0002 p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv c) C) (.classMem (.cv c) (syn_chwcards (syn_cvv)))
      (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv c) (syn_cnc (.cv d))))))
      (syn_wex d (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))))
      p0003 p0008
  have p0010 := @g_elhwcardswev c s d dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0011 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))))))
      (syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))))
      c C (syn_cvv) dv_cache_0006 dv_cache_0007 p0009 p0010
  have p0012 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cvv))
      (syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d)))))))
      p0001 p0011
  have p0013 :=
    @g_mpbid (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))))
      p0000 p0012
  have p0014 :=
    @g_wppcandminfixedpivotsetdeddrfdv z C (.cv d) (.cv s) n F dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016
  have p0015 :=
    @g_exlimdvv (.classMem F (syn_cvv))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      d s dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0014
  have p0016 :=
    @g_syl5 (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq C (syn_cnc (.cv d))))))
      (.classMem F (syn_cvv))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0013 p0015
  have p0017 :=
    @g_imp (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wrex n (syn_cwppcand F C)
        (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))
      p0016
  exact p0017

@[expose]
noncomputable def g_wppcandleastuniqclndv (A : Class) (B : Class) (C : Class) (k : Var)
    (F : Class) (dv_A_k : k ∉ A.fv) (dv_B_k : k ∉ B.fv) (dv_C_k : k ∉ C.fv)
    (dv_F_k : k ∉ F.fv)
    (hyp_wppcandleastuniqclndv_1 : Nominal.NPrf (.classMem A (syn_cwppcand F C)))
    (hyp_wppcandleastuniqclndv_2 :
      Nominal.NPrf (syn_wral k (syn_cwppcand F C) (syn_wbr A (syn_clec) (.cv k))))
    (hyp_wppcandleastuniqclndv_3 : Nominal.NPrf (.classMem B (syn_cwppcand F C)))
    (hyp_wppcandleastuniqclndv_4 :
      Nominal.NPrf (syn_wral k (syn_cwppcand F C) (syn_wbr B (syn_clec) (.cv k)))) :
    Nominal.NPrf (.classEq A B) :=
  by
  have dv_cache_0001 : k ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_k, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((syn_cwppcand F C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_wbr A (syn_clec) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_A_k,
          dv_B_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_k, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((syn_wbr B (syn_clec) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_B_k,
          dv_A_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv k) B)
  have p0001 := @g_breq2d (.classEq (.cv k) B) (.cv k) B A (syn_clec) p0000
  have p0002 :=
    @g_rspcv (syn_wbr A (syn_clec) (.cv k)) (syn_wbr A (syn_clec) B) k B
      (syn_cwppcand F C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 := Nominal.mp hyp_wppcandleastuniqclndv_3 p0002
  have p0004 := Nominal.mp hyp_wppcandleastuniqclndv_2 p0003
  have p0005 := @g_id (.classEq (.cv k) A)
  have p0006 := @g_breq2d (.classEq (.cv k) A) (.cv k) A B (syn_clec) p0005
  have p0007 :=
    @g_rspcv (syn_wbr B (syn_clec) (.cv k)) (syn_wbr B (syn_clec) A) k A
      (syn_cwppcand F C) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0006
  have p0008 := Nominal.mp hyp_wppcandleastuniqclndv_1 p0007
  have p0009 := Nominal.mp hyp_wppcandleastuniqclndv_4 p0008
  have p0010 := @g_pm3_2i (syn_wbr A (syn_clec) B) (syn_wbr B (syn_clec) A) p0004 p0009
  have p0011 := @g_elwppcand C A F
  have p0012 :=
    @g_biimpi (.classMem A (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))
        (.classMem A (syn_cwppreach F C)))
      p0011
  have p0013 := Nominal.mp hyp_wppcandleastuniqclndv_1 p0012
  have p0014 :=
    @g_simpl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))
      (.classMem A (syn_cwppreach F C))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_simpl (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @g_hwcardssnc (syn_cvv)
  have p0019 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) A p0018
  have p0020 := Nominal.mp p0017 p0019
  have p0021 := @g_elwppcand C B F
  have p0022 :=
    @g_biimpi (.classMem B (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem B (syn_chwcards (syn_cvv))) (syn_wbr B (syn_clec) C))
        (.classMem B (syn_cwppreach F C)))
      p0021
  have p0023 := Nominal.mp hyp_wppcandleastuniqclndv_3 p0022
  have p0024 :=
    @g_simpl (syn_wa (.classMem B (syn_chwcards (syn_cvv))) (syn_wbr B (syn_clec) C))
      (.classMem B (syn_cwppreach F C))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_simpl (.classMem B (syn_chwcards (syn_cvv))) (syn_wbr B (syn_clec) C)
  have p0027 := Nominal.mp p0025 p0026
  have p0029 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) B p0018
  have p0030 := Nominal.mp p0027 p0029
  have p0031 := @g_pm3_2i (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) p0020 p0030
  have p0032 := @g_sbth A B
  have p0033 := Nominal.mp p0031 p0032
  have p0034 := Nominal.mp p0010 p0033
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end
