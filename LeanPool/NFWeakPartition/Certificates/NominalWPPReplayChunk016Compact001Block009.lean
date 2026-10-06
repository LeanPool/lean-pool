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

/-- Checked nominal proof certificate identified upstream as `g_wecomparisoncutreplttargetdfdv`. -/
@[expose]
noncomputable def gWecomparisoncutreplttargetdfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_R_x : x ∉ R.fv)
    (dv_S_x : x ∉ S.fv)
    (hyp_wecomparisoncutreplttargetdfdv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
        (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))) :=
  by
  have dv_cache_0001 :
    x ∉
      ((Wff.classEq R (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
            (synCin (synCkqrel (synClefin))
              (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))).fv :=
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
      ((synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c)))).fv :=
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
      ((Wff.classEq D (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c))))).fv :=
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
      ((Wff.classEq E (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0)))).fv :=
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
      ((synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0))).fv :=
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
      ((synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))).fv :=
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
      ((synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))).fv :=
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
    @gId
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
  have p0001 :=
    @gDifeq1d
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      R
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
      (synCid) p0000
  have p0002 :=
    @gCnveqd
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      (synCdif R (synCid))
      (synCdif (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
        (synCid))
      p0001
  have p0003 :=
    @gImaeq1d
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      (synCcnv (synCdif R (synCid)))
      (synCcnv (synCdif (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
            (synCin (synCkqrel (synClefin))
              (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
      (synCsn (.cv x)) p0002
  have p0004 :=
    @gIneq2d
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) R
              (synCin (synCkqrel (synClefin))
                (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
        (synCsn (.cv x)))
      D p0003
  have p0005 :=
    @gNceqd
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                  (synWbr (synCnc E) (synCltc) (synCnc D))) R
                (synCin (synCkqrel (synClefin))
                  (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
          (synCsn (.cv x))))
      p0004
  have p0006 :=
    @gEqeq2d
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCnc (synCin D (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                    (synWbr (synCnc E) (synCltc) (synCnc D))) R
                  (synCin (synCkqrel (synClefin))
                    (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
            (synCsn (.cv x)))))
      (synCnc E) p0005
  have p0007 :=
    @gRexbidv
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif (synCif
                    (synWa (synWbr S (synCwe) E)
                      (synWbr (synCnc E) (synCltc) (synCnc D))) R
                    (synCin (synCkqrel (synClefin))
                      (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
              (synCsn (.cv x))))))
      x D dv_cache_0001 p0006
  have p0008 :=
    @gBiid
      (synWrex x D (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif
                    (synCif (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
  have p0009 :=
    @gA1i
      (synWb (synWrex x D (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv
                    (synCdif (synCif (synWa (synWbr S (synCwe) E)
                          (synWbr (synCnc E) (synCltc) (synCnc D))) R
                        (synCin (synCkqrel (synClefin))
                          (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                  (synCsn (.cv x))))))) (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                          (synWbr (synCnc E) (synCltc) (synCnc D))) R
                        (synCin (synCkqrel (synClefin))
                          (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                  (synCsn (.cv x))))))))
      (.classEq S (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      p0008
  have p0010 :=
    @gRexeq
      (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif (synCif
                    (synWa (synWbr S (synCwe) E)
                      (synWbr (synCnc E) (synCltc) (synCnc D))) R
                    (synCin (synCkqrel (synClefin))
                      (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
              (synCsn (.cv x))))))
      x D
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      dv_cache_0002 dv_cache_0003
  have p0011 :=
    @gId
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
  have p0012 :=
    @gIneq1d
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      D
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) R
              (synCin (synCkqrel (synClefin))
                (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
        (synCsn (.cv x)))
      p0011
  have p0013 :=
    @gNceqd
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCin D (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                  (synWbr (synCnc E) (synCltc) (synCnc D))) R
                (synCin (synCkqrel (synClefin))
                  (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))) (synCima (synCcnv (synCdif (synCif
                (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
                (synCin (synCkqrel (synClefin))
                  (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
          (synCsn (.cv x))))
      p0012
  have p0014 :=
    @gEqeq2d
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCnc (synCin D (synCima (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                    (synWbr (synCnc E) (synCltc) (synCnc D))) R
                  (synCin (synCkqrel (synClefin))
                    (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
            (synCsn (.cv x)))))
      (synCnc (synCin (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c))) (synCima (synCcnv (synCdif (synCif
                  (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
                  R (synCin (synCkqrel (synClefin))
                    (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
            (synCsn (.cv x)))))
      (synCnc E) p0013
  have p0015 :=
    @gRexbidv
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif (synCif
                    (synWa (synWbr S (synCwe) E)
                      (synWbr (synCnc E) (synCltc) (synCnc D))) R
                    (synCin (synCkqrel (synClefin))
                      (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (synCnc E) (synCnc (synCin (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) D (synCsn (synC0c))) (synCima
              (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                      (synWbr (synCnc E) (synCltc) (synCnc D))) R
                    (synCin (synCkqrel (synClefin))
                      (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
              (synCsn (.cv x))))))
      x
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      dv_cache_0004 p0014
  have p0016 :=
    @gBitrd
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synWrex x D (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif
                    (synCif (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      (synWrex x (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))) (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv
                  (synCdif (synCif (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      (synWrex x (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))) (.classEq (synCnc E) (synCnc (synCin (synCif
                (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
                D (synCsn (synC0c))) (synCima (synCcnv (synCdif (synCif
                      (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      p0010 p0015
  have p0017 :=
    @gId
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
  have p0018 :=
    @gNceqd
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      E
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
        (synC0))
      p0017
  have p0019 :=
    @gEqeq1d
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synCnc E)
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synCnc (synCin (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c))) (synCima (synCcnv (synCdif (synCif
                  (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
                  R (synCin (synCkqrel (synClefin))
                    (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
            (synCsn (.cv x)))))
      p0018
  have p0020 :=
    @gRexbidv
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (.classEq (synCnc E) (synCnc (synCin (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) D (synCsn (synC0c))) (synCima
              (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                      (synWbr (synCnc E) (synCltc) (synCnc D))) R
                    (synCin (synCkqrel (synClefin))
                      (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0))) (synCnc (synCin (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) D (synCsn (synC0c))) (synCima
              (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                      (synWbr (synCnc E) (synCltc) (synCnc D))) R
                    (synCin (synCkqrel (synClefin))
                      (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
              (synCsn (.cv x))))))
      x
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      dv_cache_0005 p0019
  have p0021 :=
    @gBreq1 R
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
      D (synCwe)
  have p0022 :=
    @gBreq2 D
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
      (synCwe)
  have p0023 :=
    @gBreq1
      (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c))))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
      (synCsn (synC0c)) (synCwe)
  have p0024 :=
    @gBreq2 (synCsn (synC0c))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
      (synCwe)
  have p0025 := @gFinlewe
  have p0026 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc)) synWtru p0025
  have p0027 := @gPeano1
  have p0028 := @gSnssi (synC0c) (synCnnc)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @gA1i (synWss (synCsn (synC0c)) (synCnnc)) synWtru p0029
  have p0031 := @gSnex (synC0c)
  have p0032 := @gA1i (.classMem (synCsn (synC0c)) (synCvv)) synWtru p0031
  have p0033 :=
    @gWerestrndv synWtru (synCsn (synC0c)) (synCnnc) (synCkqrel (synClefin)) p0026
      p0030 p0032
  have p0034 :=
    @gTrud
      (synWbr (synCin (synCkqrel (synClefin))
          (synCxp (synCsn (synC0c)) (synCsn (synC0c)))) (synCwe) (synCsn (synC0c)))
      p0033
  have p0035 :=
    @gKeephyp2v
      (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
      (synWbr R (synCwe) D)
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
        (synCwe) D)
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
        (synCwe) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synWbr (synCin (synCkqrel (synClefin))
          (synCxp (synCsn (synC0c)) (synCsn (synC0c)))) (synCwe) (synCsn (synC0c)))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
        (synCwe) (synCsn (synC0c)))
      R D
      (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c))))
      (synCsn (synC0c)) p0021 p0022 p0023 p0024 hyp_wecomparisoncutreplttargetdfdv_1
      p0034
  have p0036 :=
    @gBiid (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
  have p0037 :=
    @gA1i
      (synWb (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
        (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))))
      (.classEq R (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      p0036
  have p0038 :=
    @gId
      (.classEq S (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
  have p0039 :=
    @gBreq1d
      (.classEq S (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      S
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      E (synCwe) p0038
  have p0040 := @gBiid (synWbr (synCnc E) (synCltc) (synCnc D))
  have p0041 :=
    @gA1i
      (synWb (synWbr (synCnc E) (synCltc) (synCnc D))
        (synWbr (synCnc E) (synCltc) (synCnc D)))
      (.classEq S (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      p0040
  have p0042 :=
    @gAnbi12d
      (.classEq S (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synWbr S (synCwe) E)
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
      (synWbr (synCnc E) (synCltc) (synCnc D))
      (synWbr (synCnc E) (synCltc) (synCnc D)) p0039 p0041
  have p0043 :=
    @gBiid
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
  have p0044 :=
    @gA1i
      (synWb (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
        (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E))
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      p0043
  have p0046 :=
    @gNceqd
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      D
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      p0011
  have p0047 :=
    @gBreq2d
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCnc D)
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCnc E) (synCltc) p0046
  have p0048 :=
    @gAnbi12d
      (.classEq D (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
      (synWbr (synCnc E) (synCltc) (synCnc D))
      (synWbr (synCnc E) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      p0044 p0047
  have p0050 :=
    @gBreq2d
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      E
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
        (synC0))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCwe) p0017
  have p0053 :=
    @gBreq1d
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synCnc E)
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCltc) p0018
  have p0054 :=
    @gAnbi12d
      (.classEq E (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synWbr (synCnc E) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      (synWbr (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0))) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      p0050 p0053
  have p0055 :=
    @gBiid
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))))
  have p0056 :=
    @gA1i
      (synWb (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synCwe) (synC0))
          (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c))))) (synWa
          (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synCwe) (synC0))
          (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c))))))
      (.classEq (synCin (synCkqrel (synClefin))
          (synCxp (synCsn (synC0c)) (synCsn (synC0c)))) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
          (synCin (synCkqrel (synClefin))
            (synCxp (synCsn (synC0c)) (synCsn (synC0c))))))
      p0055
  have p0057 :=
    @gId
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
  have p0058 :=
    @gBreq1d
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synC0) (synCwe) p0057
  have p0059 :=
    @gBiid (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c))))
  have p0060 :=
    @gA1i
      (synWb (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c))))
        (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))))
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      p0059
  have p0061 :=
    @gAnbi12d
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
      (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c))))
      (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))) p0058 p0060
  have p0062 :=
    @gBiid
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
  have p0063 :=
    @gA1i
      (synWb (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
          (synCwe) (synC0)) (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
          (synCwe) (synC0)))
      (.classEq (synCsn (synC0c)) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      p0062
  have p0064 :=
    @gId
      (.classEq (synCsn (synC0c)) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
  have p0065 :=
    @gNceqd
      (.classEq (synCsn (synC0c)) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCsn (synC0c))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      p0064
  have p0066 :=
    @gBreq2d
      (.classEq (synCsn (synC0c)) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCnc (synCsn (synC0c)))
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCnc (synC0)) (synCltc) p0065
  have p0067 :=
    @gAnbi12d
      (.classEq (synCsn (synC0c)) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
      (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c))))
      (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      p0063 p0066
  have p0068 :=
    @gId
      (.classEq (synC0) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
  have p0069 :=
    @gBreq2d
      (.classEq (synC0) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synC0)
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
        (synC0))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCwe) p0068
  have p0071 :=
    @gNceqd
      (.classEq (synC0) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synC0)
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
        (synC0))
      p0068
  have p0072 :=
    @gBreq1d
      (.classEq (synC0) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synCnc (synC0))
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synCnc (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))))
      (synCltc) p0071
  have p0073 :=
    @gAnbi12d
      (.classEq (synC0) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      (synWbr (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0))) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      p0069 p0072
  have p0076 := @gN0ss (synCnnc)
  have p0077 := @gA1i (synWss (synC0) (synCnnc)) synWtru p0076
  have p0078 := @gN0ex
  have p0079 := @gA1i (.classMem (synC0) (synCvv)) synWtru p0078
  have p0080 :=
    @gWerestrndv synWtru (synC0) (synCnnc) (synCkqrel (synClefin)) p0026 p0077 p0079
  have p0081 :=
    @gTrud
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      p0080
  have p0082 := @gN0lt1c
  have p0083 := @gDf0c2
  have p0084 := @gN0cex
  have p0085 := @gDf1c3 (synC0c) p0084
  have p0086 :=
    @gN3brtr3i (synC0c) (synC1c) (synCnc (synC0)) (synCnc (synCsn (synC0c)))
      (synCltc) p0082 p0083 p0085
  have p0087 :=
    @gPm32i
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))) p0081 p0086
  have p0088 :=
    @gElimhyp4v
      (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
      (synWa (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
          (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0))) (synWbr (synCnc (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) E (synC0))) (synCltc) (synCnc
            (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) D (synCsn (synC0c))))))
      (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
      (synWa (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
        (synWbr (synCnc E) (synCltc) (synCnc D)))
      (synWa (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) E)
        (synWbr (synCnc E) (synCltc) (synCnc (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) D (synCsn (synC0c))))))
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))))
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))))
      (synWa (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
          (synCwe) (synC0))
        (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCsn (synC0c)))))
      (synWa (synWbr (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            S (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
          (synCwe) (synC0)) (synWbr (synCnc (synC0)) (synCltc) (synCnc (synCif
              (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
              D (synCsn (synC0c))))))
      R S D
      (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c))))
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCsn (synC0c))
      E (synC0) p0037 p0042 p0048 p0054 p0056 p0061 p0067 p0073 p0087
  have p0089 :=
    @gSimpli
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synWbr (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0))) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      p0088
  have p0143 :=
    @gSimpri
      (synWbr (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
          (synC0)))
      (synWbr (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            E (synC0))) (synCltc) (synCnc (synCif
            (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
            D (synCsn (synC0c)))))
      p0088
  have p0144 :=
    @gWecomparisoncutrepltfdv x
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
        (synCsn (synC0c)))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c)))))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) S
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) E
        (synC0))
      dv_cache_0003 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0035 p0089 p0143
  have p0145 :=
    @gDedth4v
      (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWrex x D (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif
                    (synCif (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      (synWrex x D (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif
                    (synCif (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      (synWrex x (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))) (.classEq (synCnc E) (synCnc (synCin (synCif
                (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
                D (synCsn (synC0c))) (synCima (synCcnv (synCdif (synCif
                      (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      (synWrex x (synCif
          (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D))) D
          (synCsn (synC0c))) (.classEq (synCnc (synCif (synWa (synWbr S (synCwe) E)
                (synWbr (synCnc E) (synCltc) (synCnc D))) E (synC0))) (synCnc (synCin
              (synCif (synWa (synWbr S (synCwe) E)
                  (synWbr (synCnc E) (synCltc) (synCnc D))) D (synCsn (synC0c))) (synCima
                (synCcnv (synCdif (synCif (synWa (synWbr S (synCwe) E)
                        (synWbr (synCnc E) (synCltc) (synCnc D))) R
                      (synCin (synCkqrel (synClefin))
                        (synCxp (synCsn (synC0c)) (synCsn (synC0c))))) (synCid)))
                (synCsn (.cv x)))))))
      R S D E
      (synCin (synCkqrel (synClefin)) (synCxp (synCsn (synC0c)) (synCsn (synC0c))))
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCsn (synC0c))
      (synC0) p0007 p0009 p0016 p0020 p0144
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

/-- Checked nominal proof certificate identified upstream as
`g_wecomparisoncutreptypedliftdndv`.
-/
@[expose]
noncomputable def gWecomparisoncutreptypedliftdndv (x : Var) (D : Class) (R : Class)
    (E : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_q : q ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_R_q : q ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_q_x : q ≠ x) :
    Nominal.NPrf
      (.imp (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))) :=
  by
  have dv_cache_0001 : q ∉ ((synCsn (synCsn (.cv x)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_q_x,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
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
      ((Wff.classEq (synCnc E) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))).fv :=
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
      ((synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))).fv :=
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
    @gSimpl (.classMem (.cv x) D)
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0001 := @gSnelpw1 (synCsn (.cv x)) (synCpw1 D)
  have p0002 := @gSnelpw1 (.cv x) D
  have p0003 :=
    @gBitri (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 D)))
      (.classMem (synCsn (.cv x)) (synCpw1 D)) (.classMem (.cv x) D) p0001 p0002
  have p0004 :=
    @gBiimpri (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 D)))
      (.classMem (.cv x) D) p0003
  have p0005 :=
    @gSyl
      (synWa (.classMem (.cv x) D) (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (.cv x) D)
      (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 D))) p0000 p0004
  have p0006 :=
    @gSimpr (.classMem (.cv x) D)
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0007 :=
    @gJca
      (synWa (.classMem (.cv x) D) (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 D)))
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0005 p0006
  have p0008 := @gId (.classEq (.cv q) (synCsn (synCsn (.cv x))))
  have p0009 :=
    @gUnieqd (.classEq (.cv q) (synCsn (synCsn (.cv x)))) (.cv q)
      (synCsn (synCsn (.cv x))) p0008
  have p0010 :=
    @gUnieqd (.classEq (.cv q) (synCsn (synCsn (.cv x)))) (synCuni (.cv q))
      (synCuni (synCsn (synCsn (.cv x)))) p0009
  have p0011 := @gSnex (.cv x)
  have p0012 := @gUnisn (synCsn (.cv x)) p0011
  have p0013 := @gUnieqi (synCuni (synCsn (synCsn (.cv x)))) (synCsn (.cv x)) p0012
  have p0014 := @gVex x
  have p0015 := @gUnisn (.cv x) p0014
  have p0016 :=
    @gEqtri (synCuni (synCuni (synCsn (synCsn (.cv x)))))
      (synCuni (synCsn (.cv x))) (.cv x) p0013 p0015
  have p0017 :=
    @gA1i (.classEq (synCuni (synCuni (synCsn (synCsn (.cv x))))) (.cv x))
      (.classEq (.cv q) (synCsn (synCsn (.cv x)))) p0016
  have p0018 :=
    @gEqtrd (.classEq (.cv q) (synCsn (synCsn (.cv x)))) (synCuni (synCuni (.cv q)))
      (synCuni (synCuni (synCsn (synCsn (.cv x))))) (.cv x) p0010 p0017
  have p0019 :=
    @gSneqd (.classEq (.cv q) (synCsn (synCsn (.cv x)))) (synCuni (synCuni (.cv q)))
      (.cv x) p0018
  have p0020 :=
    @gImaeq2d (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCsn (.cv x))
      (synCcnv (synCdif R (synCid))) p0019
  have p0021 :=
    @gIneq2d (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q)))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) D p0020
  have p0022 :=
    @gNceqd (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0021
  have p0023 :=
    @gEqeq2d (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCnc E) p0022
  have p0024 :=
    @gRspcev
      (.classEq (synCnc E) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      q (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 D)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0023
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv x) D) (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWa (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 D)))
        (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0007 p0024
  have p0026 :=
    @gRexlimiva
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      x D dv_cache_0004 p0025
  have p0027 :=
    @gId
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0028 :=
    @gA1ii
      (.imp (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.imp (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) (synWrex x D
          (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0026 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as
`g_wecomparisoncutreptypedtargetdfdv`.
-/
@[expose]
noncomputable def gWecomparisoncutreptypedtargetdfdv (D : Class) (R : Class) (S : Class)
    (E : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_E_q : q ∉ E.fv) (dv_R_q : q ∉ R.fv)
    (hyp_wecomparisoncutreptypedtargetdfdv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
        (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))) :=
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
    @gWecomparisoncutreplttargetdfdv x D R S E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_wecomparisoncutreptypedtargetdfdv_1
  have p0001 :=
    @gWecomparisoncutreptypedliftdndv x D R E q dv_cache_0005 dv_cache_0001 dv_cache_0006
      dv_cache_0002 dv_cache_0007 dv_cache_0003 dv_cache_0008
  have p0002 :=
    @gSyl (synWa (synWbr S (synCwe) E) (synWbr (synCnc E) (synCltc) (synCnc D)))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc E) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as
`g_wppcandstrictslicecutrepfixdrfdv`.
-/
@[expose]
noncomputable def gWppcandstrictslicecutrepfixdrfdv (C : Class) (D : Class) (R : Class)
    (k : Var) (F : Class) (q : Var) (_dv_C_k : k ∉ C.fv) (dv_C_q : q ∉ C.fv)
    (_dv_D_k : k ∉ D.fv) (dv_D_q : q ∉ D.fv) (_dv_F_k : k ∉ F.fv) (dv_F_q : q ∉ F.fv)
    (_dv_R_k : k ∉ R.fv) (dv_R_q : q ∉ R.fv) (dv_k_q : k ≠ q)
    (hyp_wppcandstrictslicecutrepfixdrfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wppcandstrictslicecutrepfixdrfdv_2 : Nominal.NPrf (.classEq C (synCnc D))) :
    Nominal.NPrf
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))) :=
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
      ((synWa (.classMem (.cv k)
            (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
          (synWa (synWbr (.cv s) (synCwe) (.cv e))
            (.classEq (.cv k) (synCnc (.cv e)))))).fv :=
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
      ((synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))).fv :=
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
      ((synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))).fv :=
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
      ((Wff.classMem (.cv k) (synCin (synCwppcand F C)
            (synCima (synCcnv (synCltc)) (synCsn C))))).fv :=
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
      ((Wff.classMem (.cv k) (synCin (synCwppcand F C)
            (synCima (synCcnv (synCltc)) (synCsn C))))).fv :=
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
  have p0000 := @gElwppcandstrictslice C k F
  have p0001 :=
    @gBiimpi
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C)) p0000
  have p0002 :=
    @gSimpld
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C) p0001
  have p0003 := @gElwppcand C (.cv k) F
  have p0004 :=
    @gBiimpi (.classMem (.cv k) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) C)) (.classMem (.cv k) (synCwppreach F C)))
      p0003
  have p0005 :=
    @gSyl
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) C)) (.classMem (.cv k) (synCwppreach F C)))
      p0002 p0004
  have p0006 :=
    @gSimpld
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv k) (synChwcards (synCvv))) (synWbr (.cv k) (synClec) C))
      (.classMem (.cv k) (synCwppreach F C)) p0005
  have p0007 :=
    @gSimpld
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synChwcards (synCvv))) (synWbr (.cv k) (synClec) C) p0006
  have p0008 := @gElhwcardswev k s e dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @gBiimpi (.classMem (.cv k) (synChwcards (synCvv)))
      (synWex e (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv e))
            (.classEq (.cv k) (synCnc (.cv e))))))
      p0008
  have p0010 :=
    @gSyl
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synChwcards (synCvv)))
      (synWex e (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv e))
            (.classEq (.cv k) (synCnc (.cv e))))))
      p0007 p0009
  have p0011 :=
    @gSimpr
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e))))
  have p0012 :=
    @gSimpl (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e))))
      (synWbr (.cv s) (synCwe) (.cv e)) p0011 p0012
  have p0014 :=
    @gSimpl
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e))))
  have p0017 :=
    @gSimprd
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C) p0001
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWbr (.cv k) (synCltc) C) p0014 p0017
  have p0020 :=
    @gSimpr (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))
  have p0021 :=
    @gSyl
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e))))
      (.classEq (.cv k) (synCnc (.cv e))) p0011 p0020
  have p0022 :=
    @gA1i (.classEq C (synCnc D))
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      hyp_wppcandstrictslicecutrepfixdrfdv_2
  have p0023 :=
    @gBreq12d
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (.cv k) (synCnc (.cv e)) C (synCnc D) (synCltc) p0021 p0022
  have p0024 :=
    @gMpbid
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (synWbr (.cv k) (synCltc) C) (synWbr (synCnc (.cv e)) (synCltc) (synCnc D))
      p0018 p0023
  have p0025 :=
    @gJca
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (synWbr (.cv s) (synCwe) (.cv e))
      (synWbr (synCnc (.cv e)) (synCltc) (synCnc D)) p0013 p0024
  have p0026 :=
    @gWecomparisoncutreptypedtargetdfdv D R (.cv s) (.cv e) q dv_cache_0004 dv_cache_0005
      dv_cache_0006 hyp_wppcandstrictslicecutrepfixdrfdv_1
  have p0027 :=
    @gSyl
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e))
        (synWbr (synCnc (.cv e)) (synCltc) (synCnc D)))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc (.cv e)) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0025 p0026
  have p0031 :=
    @gEqeq1d
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (.cv k) (synCnc (.cv e))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      p0021
  have p0032 :=
    @gRexbidv
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (.classEq (synCnc (.cv e)) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      q (synCpw1 (synCpw1 D)) dv_cache_0007 p0031
  have p0033 :=
    @gMpbird
      (synWa (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e)))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (synCnc (.cv e)) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0027 p0032
  have p0034 :=
    @gEx
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0033
  have p0035 :=
    @gExlimdvv
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (synWbr (.cv s) (synCwe) (.cv e)) (.classEq (.cv k) (synCnc (.cv e))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      e s dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0034
  have p0036 :=
    @gMpd
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWex e (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv e))
            (.classEq (.cv k) (synCnc (.cv e))))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0010 p0035
  have p0037 :=
    @gRgen
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as
`g_wppcandstrictslicenonemptyminndv`.
-/
@[expose]
noncomputable def gWppcandstrictslicenonemptyminndv (z : Var) (C : Class) (D : Class)
    (R : Class) (k : Var) (n : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv)
    (dv_C_n : n ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_D_k : k ∉ D.fv)
    (_dv_D_n : n ∉ D.fv) (dv_D_q : q ∉ D.fv) (_dv_D_z : z ∉ D.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_R_k : k ∉ R.fv)
    (_dv_R_n : n ∉ R.fv) (dv_R_q : q ∉ R.fv) (_dv_R_z : z ∉ R.fv) (_dv_k_n : k ≠ n)
    (dv_k_q : k ≠ q) (dv_k_z : k ≠ z) (_dv_n_q : n ≠ q) (dv_n_z : n ≠ z) (_dv_q_z : q ≠ z)
    (hyp_wppcandstrictslicenonemptyminndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wppcandstrictslicenonemptyminndv_2 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppcandstrictslicenonemptyminndv_3 : Nominal.NPrf (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv q))))))))))) :
    Nominal.NPrf
      (.imp (synWne (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synC0)) (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))) :=
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
  have dv_cache_0022 : n ∉ ((synCwppcand F C)).fv :=
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
    n ∉ ((synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z)))).fv :=
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
      ((synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))).fv :=
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
    @gWppcandstrictsliceleastdndvv C D R k m F q dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 hyp_wppcandstrictslicenonemptyminndv_1
      hyp_wppcandstrictslicenonemptyminndv_2 hyp_wppcandstrictslicenonemptyminndv_3
  have p0001 :=
    @gWppcandstrictsliceleastextenddv z C k m F dv_cache_0001 dv_cache_0002 dv_cache_0016
      dv_cache_0007 dv_cache_0008 dv_cache_0017 dv_cache_0013 dv_cache_0018 dv_cache_0019
  have p0002 :=
    @gId
      (synWa (.classMem (.cv m) (synCwppcand F C))
        (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))))
  have p0003 := @gId (.classEq (.cv n) (.cv m))
  have p0004 :=
    @gBreq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (.cv z) (synClec) p0003
  have p0005 :=
    @gRalbidv (.classEq (.cv n) (.cv m)) (synWbr (.cv n) (synClec) (.cv z))
      (synWbr (.cv m) (synClec) (.cv z)) z (synCwppcand F C) dv_cache_0020 p0004
  have p0006 :=
    @gRspcev (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))
      (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))) n (.cv m)
      (synCwppcand F C) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0005
  have p0007 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCwppcand F C))
        (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))))
      (synWa (.classMem (.cv m) (synCwppcand F C))
        (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      p0002 p0006
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv m)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))) (synWral k
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWa (.classMem (.cv m) (synCwppcand F C))
        (synWral z (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv z))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      p0001 p0007
  have p0009 :=
    @gRexlimiva
      (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWbr (.cv m) (synClec) (.cv k)))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      m (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
      dv_cache_0024 p0008
  have p0010 :=
    @gSyl
      (synWne (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (synWrex m (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synWral k (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synWbr (.cv m) (synClec) (.cv k))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
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

/-- Checked nominal proof certificate identified upstream as `g_wppcandselfndv`. -/
@[expose]
noncomputable def gWppcandselfndv (C : Class) (F : Class)
    (hyp_wppcandselfndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem C (synChwcards (synCvv))) (.classMem C (synCwppcand F C))) :=
  by
  have p0000 := @gId (.classMem C (synChwcards (synCvv)))
  have p0001 := @gHwcardssnc (synCvv)
  have p0002 := @gSsel (synChwcards (synCvv)) (synCncs) C
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gNclecid C
  have p0005 :=
    @gSyl (.classMem C (synChwcards (synCvv))) (.classMem C (synCncs))
      (synWbr C (synClec) C) p0003 p0004
  have p0006 :=
    @gJca (.classMem C (synChwcards (synCvv))) (.classMem C (synChwcards (synCvv)))
      (synWbr C (synClec) C) p0000 p0005
  have p0012 := @gElimasn (synClec) C C
  have p0013 := (Nominal.biimpRefl (synWbr C (synClec) C))
  have p0014 :=
    @gBitr4i (.classMem C (synCima (synClec) (synCsn C)))
      (.classMem (synCop C C) (synClec)) (synWbr C (synClec) C) p0012 p0013
  have p0015 :=
    @gSylibr (.classMem C (synChwcards (synCvv))) (synWbr C (synClec) C)
      (.classMem C (synCima (synClec) (synCsn C))) p0005 p0014
  have p0016 := @gCnvex F hyp_wppcandselfndv_1
  have p0017 := @gWppimagefn (synCcnv F) p0016
  have p0018 := @gFnfun (synCvv) (synCimage (synCcnv F))
  have p0019 := Nominal.mp p0017 p0018
  have p0021 := @gImageex (synCcnv F) p0016
  have p0022 := @gElfuns (synCimage (synCcnv F)) p0021
  have p0023 :=
    @gMpbir (.classMem (synCimage (synCcnv F)) (synCfuns))
      (synWfun (synCimage (synCcnv F))) p0019 p0022
  have p0024 := @gLecex
  have p0025 := @gSnex C
  have p0026 := @gImaex (synClec) (synCsn C) p0024 p0025
  have p0029 := @gFndm (synCvv) (synCimage (synCcnv F))
  have p0030 := Nominal.mp p0017 p0029
  have p0031 :=
    @gEleqtrri (synCima (synClec) (synCsn C)) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0026 p0030
  have p0032 := @gSsv (synCrn (synCimage (synCcnv F)))
  have p0037 :=
    @gSseqtr4i (synCrn (synCimage (synCcnv F))) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0032 p0030
  have p0038 :=
    @gN3pm32i (.classMem (synCimage (synCcnv F)) (synCfuns))
      (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
      (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F))))
      p0023 p0031 p0037
  have p0039 :=
    @gWpporbit0ndv (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))
  have p0040 := Nominal.mp p0038 p0039
  have p0064 :=
    @gWpporbitfnndv (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))
  have p0065 := Nominal.mp p0038 p0064
  have p0066 := @gPeano1
  have p0067 :=
    @gFnfvelrn (synCnnc) (synC0c)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0068 :=
    @gMp2an
      (synWfn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCnnc))
      (.classMem (synC0c) (synCnnc))
      (.classMem
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synC0c))
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      p0065 p0066 p0067
  have p0069 :=
    @gEqeltrri
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synC0c))
      (synCima (synClec) (synCsn C))
      (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      p0040 p0068
  have p0070 :=
    @gA1i
      (.classMem (synCima (synClec) (synCsn C))
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      (.classMem C (synChwcards (synCvv))) p0069
  have p0071 :=
    @gJca (.classMem C (synChwcards (synCvv)))
      (.classMem C (synCima (synClec) (synCsn C)))
      (.classMem (synCima (synClec) (synCsn C))
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      p0015 p0070
  have p0072 :=
    @gElunii C (synCima (synClec) (synCsn C))
      (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
  have p0073 :=
    @gSyl (.classMem C (synChwcards (synCvv)))
      (synWa (.classMem C (synCima (synClec) (synCsn C)))
        (.classMem (synCima (synClec) (synCsn C)) (synCrn
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))))
      (.classMem C (synCuni (synCrn
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))))
      p0071 p0072
  have p0074 := (Nominal.classEqRefl (synCwppreach F C))
  have p0075 :=
    @gEleq2i (synCwppreach F C)
      (synCuni
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      C p0074
  have p0076 :=
    @gSylibr (.classMem C (synChwcards (synCvv)))
      (.classMem C (synCuni (synCrn
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))))
      (.classMem C (synCwppreach F C)) p0073 p0075
  have p0077 :=
    @gJca (.classMem C (synChwcards (synCvv)))
      (synWa (.classMem C (synChwcards (synCvv))) (synWbr C (synClec) C))
      (.classMem C (synCwppreach F C)) p0006 p0076
  have p0078 := @gElwppcand C C F
  have p0079 :=
    @gSylibr (.classMem C (synChwcards (synCvv)))
      (synWa (synWa (.classMem C (synChwcards (synCvv))) (synWbr C (synClec) C))
        (.classMem C (synCwppreach F C)))
      (.classMem C (synCwppcand F C)) p0077 p0078
  exact p0079

/-- Checked nominal proof certificate identified upstream as `g_wppcandstrictsliceemptyminndv`. -/
@[expose]
noncomputable def gWppcandstrictsliceemptyminndv (C : Class) (k : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (hyp_wppcandstrictsliceemptyminndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppcandstrictsliceemptyminndv_2 :
      Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synC0)) (synWa (.classMem C (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr C (synClec) (.cv k))))) :=
  by
  have dv_cache_0001 :
    k ∉
      ((Wff.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synC0))).fv :=
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
  have p0000 := @gWppcandselfndv C F hyp_wppcandstrictsliceemptyminndv_1
  have p0001 := Nominal.mp hyp_wppcandstrictsliceemptyminndv_2 p0000
  have p0002 :=
    @gA1i (.classMem C (synCwppcand F C))
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      p0001
  have p0003 := @gHwcardssnc (synCvv)
  have p0004 := @gSsel (synChwcards (synCvv)) (synCncs) C
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := Nominal.mp hyp_wppcandstrictsliceemptyminndv_2 p0005
  have p0007 := @gNclecid C
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gA1i (synWbr C (synClec) C)
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      p0008
  have p0010 :=
    @gSimpr
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (.classMem (.cv k) (synCwppcand F C))
  have p0011 := @gNoel (.cv k)
  have p0012 :=
    @gA1i (.neg (.classMem (.cv k) (synC0)))
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      p0011
  have p0013 :=
    @gSimpl
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (.classMem (.cv k) (synCwppcand F C))
  have p0014 :=
    @gEleq2d
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0)
      (.cv k) p0013
  have p0015 :=
    @gBiimpd
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synC0)) p0014
  have p0016 :=
    @gCon3d
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (.classMem (.cv k) (synC0)) p0015
  have p0017 :=
    @gMpd
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (.neg (.classMem (.cv k) (synC0)))
      (.neg (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))))
      p0012 p0016
  have p0019 := @gElwppcandstrictslice C k F
  have p0020 :=
    @gBiimpri
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C)) p0019
  have p0021 :=
    @gEx (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C)
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      p0020
  have p0022 :=
    @gSyl
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (.classMem (.cv k) (synCwppcand F C))
      (.imp (synWbr (.cv k) (synCltc) C) (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))))
      p0010 p0021
  have p0023 :=
    @gCon3d
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (synWbr (.cv k) (synCltc) C)
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      p0022
  have p0024 :=
    @gMpd
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (.neg (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))))
      (.neg (synWbr (.cv k) (synCltc) C)) p0017 p0023
  have p0025 :=
    @gJca
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)) p0010
      p0024
  have p0026 := @gWppcandnltpivoteqd C k F
  have p0027 :=
    @gSyl
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (.classEq (.cv k) C) p0025 p0026
  have p0028 :=
    @gBreqtrrd
      (synWa (.classEq
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0))
        (.classMem (.cv k) (synCwppcand F C)))
      C C (.cv k) (synClec) p0009 p0027
  have p0029 :=
    @gEx
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (.classMem (.cv k) (synCwppcand F C)) (synWbr C (synClec) (.cv k)) p0028
  have p0030 :=
    @gRalrimiv
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (synWbr C (synClec) (.cv k)) k (synCwppcand F C) dv_cache_0001 p0029
  have p0031 :=
    @gJca
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (.classMem C (synCwppcand F C))
      (synWral k (synCwppcand F C) (synWbr C (synClec) (.cv k))) p0002 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as
`g_wppcandstrictsliceemptypublicminndv`.
-/
@[expose]
noncomputable def gWppcandstrictsliceemptypublicminndv (z : Var) (C : Class) (n : Var)
    (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_n : n ∉ F.fv)
    (dv_F_z : z ∉ F.fv) (dv_n_z : n ≠ z)
    (hyp_wppcandstrictsliceemptypublicminndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppcandstrictsliceemptypublicminndv_2 :
      Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
          (synC0)) (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))) :=
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
  have dv_cache_0005 : n ∉ ((synCwppcand F C)).fv :=
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
    n ∉ ((synWral z (synCwppcand F C) (synWbr C (synClec) (.cv z)))).fv :=
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
    @gWppcandstrictsliceemptyminndv C z F dv_cache_0001 dv_cache_0002
      hyp_wppcandstrictsliceemptypublicminndv_1 hyp_wppcandstrictsliceemptypublicminndv_2
  have p0001 := @gId (.classEq (.cv n) C)
  have p0002 := @gBreq1d (.classEq (.cv n) C) (.cv n) C (.cv z) (synClec) p0001
  have p0003 :=
    @gRalbidv (.classEq (.cv n) C) (synWbr (.cv n) (synClec) (.cv z))
      (synWbr C (synClec) (.cv z)) z (synCwppcand F C) dv_cache_0003 p0002
  have p0004 :=
    @gRspcev (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))
      (synWral z (synCwppcand F C) (synWbr C (synClec) (.cv z))) n C
      (synCwppcand F C) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0003
  have p0005 :=
    @gSyl
      (.classEq (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synC0))
      (synWa (.classMem C (synCwppcand F C))
        (synWral z (synCwppcand F C) (synWbr C (synClec) (.cv z))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppcandminfixedpivotdrfdv`. -/
@[expose]
noncomputable def gWppcandminfixedpivotdrfdv (z : Var) (C : Class) (D : Class)
    (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z)
    (hyp_wppcandminfixedpivotdrfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wppcandminfixedpivotdrfdv_2 : Nominal.NPrf (.classEq C (synCnc D)))
    (hyp_wppcandminfixedpivotdrfdv_3 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))) :=
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
    d ∉ ((synWa (synWbr R (synCwe) D) (.classEq (.cv c) (synCnc D)))).fv :=
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
    s ∉ ((synWa (synWbr R (synCwe) D) (.classEq (.cv c) (synCnc D)))).fv :=
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
    c ∉ ((Wff.imp (.classEq C (synCnc D)) (.classMem C (synChwcards (synCvv))))).fv :=
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
  have p0000 := @gNcex D
  have p0001 := @gEqeltri C (synCnc D) (synCvv) hyp_wppcandminfixedpivotdrfdv_2 p0000
  have p0002 := @gId (.classEq (.cv c) C)
  have p0003 := @gEqeq1d (.classEq (.cv c) C) (.cv c) C (synCnc D) p0002
  have p0005 := @gEleq1d (.classEq (.cv c) C) (.cv c) C (synChwcards (synCvv)) p0002
  have p0006 :=
    @gImbi12d (.classEq (.cv c) C) (.classEq (.cv c) (synCnc D))
      (.classEq C (synCnc D)) (.classMem (.cv c) (synChwcards (synCvv)))
      (.classMem C (synChwcards (synCvv))) p0003 p0005
  have p0007 :=
    @gA1i (synWbr R (synCwe) D) (.classEq (.cv c) (synCnc D))
      hyp_wppcandminfixedpivotdrfdv_1
  have p0008 := @gId (.classEq (.cv c) (synCnc D))
  have p0009 :=
    @gJca (.classEq (.cv c) (synCnc D)) (synWbr R (synCwe) D)
      (.classEq (.cv c) (synCnc D)) p0007 p0008
  have p0010 := @gBrex R D (synCwe)
  have p0011 := Nominal.mp hyp_wppcandminfixedpivotdrfdv_1 p0010
  have p0012 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0013 := Nominal.mp p0011 p0012
  have p0016 := @gSimpl (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0017 := Nominal.mp p0011 p0016
  have p0018 := @gSimpr (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0019 := @gSimpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0020 :=
    @gBreq12d (synWa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv s) R (.cv d) D
      (synCwe) p0018 p0019
  have p0022 :=
    @gNceqd (synWa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv d) D p0019
  have p0023 :=
    @gEqeq2d (synWa (.classEq (.cv d) D) (.classEq (.cv s) R)) (synCnc (.cv d))
      (synCnc D) (.cv c) p0022
  have p0024 :=
    @gAnbi12d (synWa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (synWbr (.cv s) (synCwe) (.cv d)) (synWbr R (synCwe) D)
      (.classEq (.cv c) (synCnc (.cv d))) (.classEq (.cv c) (synCnc D)) p0020 p0023
  have p0025 :=
    @gSpc2ev
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv c) (synCnc (.cv d))))
      (synWa (synWbr R (synCwe) D) (.classEq (.cv c) (synCnc D))) d s D R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0013 p0017 p0024
  have p0026 :=
    @gSyl (.classEq (.cv c) (synCnc D))
      (synWa (synWbr R (synCwe) D) (.classEq (.cv c) (synCnc D)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv c) (synCnc (.cv d))))))
      p0009 p0025
  have p0027 := @gElhwcardswev c s d dv_cache_0008 dv_cache_0007 dv_cache_0009
  have p0028 :=
    @gBiimpri (.classMem (.cv c) (synChwcards (synCvv)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv c) (synCnc (.cv d))))))
      p0027
  have p0029 :=
    @gSyl (.classEq (.cv c) (synCnc D))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv c) (synCnc (.cv d))))))
      (.classMem (.cv c) (synChwcards (synCvv))) p0026 p0028
  have p0030 :=
    @gVtoclg
      (.imp (.classEq (.cv c) (synCnc D)) (.classMem (.cv c) (synChwcards (synCvv))))
      (.imp (.classEq C (synCnc D)) (.classMem C (synChwcards (synCvv)))) c C (synCvv)
      dv_cache_0010 dv_cache_0011 p0006 p0029
  have p0031 := Nominal.mp p0001 p0030
  have p0032 := Nominal.mp hyp_wppcandminfixedpivotdrfdv_2 p0031
  have p0033 :=
    @gWppcandstrictsliceemptypublicminndv z C n F dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wppcandminfixedpivotdrfdv_3 p0032
  have p0034 :=
    @gWppcandstrictslicecutrepfixdrfdv C D R k F q dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 hyp_wppcandminfixedpivotdrfdv_1 hyp_wppcandminfixedpivotdrfdv_2
  have p0035 :=
    @gWppcandstrictslicenonemptyminndv z C D R k n F q dv_cache_0017 dv_cache_0012
      dv_cache_0018 dv_cache_0013 dv_cache_0019 dv_cache_0026 dv_cache_0020 dv_cache_0027
      dv_cache_0021 dv_cache_0014 dv_cache_0022 dv_cache_0015 dv_cache_0023 dv_cache_0028
      dv_cache_0024 dv_cache_0029 dv_cache_0030 dv_cache_0025 dv_cache_0031 dv_cache_0032
      dv_cache_0016 dv_cache_0033 hyp_wppcandminfixedpivotdrfdv_1
      hyp_wppcandminfixedpivotdrfdv_3 p0034
  have p0036 :=
    @gPm261ine
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))) (synC0)
      p0033 p0035
  exact p0036

/-- Checked nominal proof certificate identified upstream as `g_wecomparisondefaultemptywe`. -/
@[expose]
noncomputable def gWecomparisondefaultemptywe :
    Nominal.NPrf
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0)) :=
  by
  have p0000 := @gFinlewe
  have p0001 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc)) synWtru p0000
  have p0002 := @gN0ss (synCnnc)
  have p0003 := @gA1i (synWss (synC0) (synCnnc)) synWtru p0002
  have p0004 := @gN0ex
  have p0005 := @gA1i (.classMem (synC0) (synCvv)) synWtru p0004
  have p0006 :=
    @gWerestrndv synWtru (synC0) (synCnnc) (synCkqrel (synClefin)) p0001 p0003 p0005
  have p0007 :=
    @gTrud
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
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

/-- Checked nominal proof certificate identified upstream as `g_wppcandminfixedpivotpairdrfdv`. -/
@[expose]
noncomputable def gWppcandminfixedpivotpairdrfdv (z : Var) (C : Class) (D : Class)
    (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z)
    (hyp_wppcandminfixedpivotpairdrfdv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
        (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))) :=
  by
  have dv_cache_0001 : z ∉ ((synCwppcand F C)).fv := by
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
      ((synCwppcand F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0))))).fv :=
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
  have dv_cache_0003 : n ∉ ((synCwppcand F C)).fv :=
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
      ((synCwppcand F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0))))).fv :=
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
      ((Wff.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0))))).fv :=
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
      ((synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0)))).fv :=
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
      ((synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0)))).fv :=
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
      ((synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))).fv :=
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
      ((synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))).fv :=
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
      ((synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))).fv :=
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
      ((synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))).fv :=
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
    @gBiid
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
  have p0001 :=
    @gA1i
      (synWb (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
        (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))))
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      p0000
  have p0003 :=
    @gA1i
      (synWb (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
        (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))))
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      p0000
  have p0004 :=
    @gId
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
  have p0005 :=
    @gSneqd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      C
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C (synCnc (synC0)))
      p0004
  have p0006 :=
    @gImaeq2d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCsn C)
      (synCsn (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCcnv (synClec)) p0005
  have p0007 :=
    @gIneq2d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCima (synCcnv (synClec)) (synCsn C))
      (synCima (synCcnv (synClec)) (synCsn
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0)))))
      (synChwcards (synCvv)) p0006
  have p0008 :=
    @gEqidd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCimage (synCcnv F))
  have p0011 :=
    @gImaeq2d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCsn C)
      (synCsn (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synClec) p0005
  have p0012 :=
    @gJca
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (.classEq (synCimage (synCcnv F)) (synCimage (synCcnv F)))
      (.classEq (synCima (synClec) (synCsn C)) (synCima (synClec) (synCsn
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
              (synCnc (synC0))))))
      p0008 p0011
  have p0013 :=
    @gFreceq12 (synCimage (synCcnv F)) (synCimage (synCcnv F))
      (synCima (synClec) (synCsn C))
      (synCima (synClec) (synCsn
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0)))))
  have p0014 :=
    @gSyl
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synWa (.classEq (synCimage (synCcnv F)) (synCimage (synCcnv F)))
        (.classEq (synCima (synClec) (synCsn C)) (synCima (synClec) (synCsn
              (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
                (synCnc (synC0)))))))
      (.classEq (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn
              (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
                (synCnc (synC0)))))))
      p0012 p0013
  have p0015 :=
    @gRneqd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
              (synCnc (synC0))))))
      p0014
  have p0016 :=
    @gUnieqd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn
              (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
                (synCnc (synC0)))))))
      p0015
  have p0017 := (Nominal.classEqRefl (synCwppreach F C))
  have p0018 :=
    (Nominal.classEqRefl (synCwppreach F
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0)))))
  have p0019 :=
    @gN3eqtr4g
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCuni
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      (synCuni (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn
                (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
                  (synCnc (synC0))))))))
      (synCwppreach F C)
      (synCwppreach F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      p0016 p0017 p0018
  have p0020 :=
    @gIneq12d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
              (synCnc (synC0))))))
      (synCwppreach F C)
      (synCwppreach F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      p0007 p0019
  have p0021 := (Nominal.classEqRefl (synCwppcand F C))
  have p0022 :=
    (Nominal.classEqRefl (synCwppcand F
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0)))))
  have p0023 :=
    @gN3eqtr4g
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
        (synCwppreach F C))
      (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn
              (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
                (synCnc (synC0)))))) (synCwppreach F
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0)))))
      (synCwppcand F C)
      (synCwppcand F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      p0020 p0021 p0022
  have p0044 :=
    @gRaleqdv
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synWbr (.cv n) (synClec) (.cv z)) z (synCwppcand F C)
      (synCwppcand F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      dv_cache_0001 dv_cache_0002 p0023
  have p0045 :=
    @gRexeqbidv
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))
      (synWral z (synCwppcand F
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0)))) (synWbr (.cv n) (synClec) (.cv z)))
      n (synCwppcand F C)
      (synCwppcand F (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0023 p0044
  have p0046 :=
    @gId
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
  have p0047 :=
    @gEqidd
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      D
  have p0048 :=
    @gBreq12d
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      R
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      D D (synCwe) p0046 p0047
  have p0049 :=
    @gEqidd
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      C
  have p0051 :=
    @gNceqd
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      D D p0047
  have p0052 :=
    @gEqeq12d
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      C C (synCnc D) (synCnc D) p0049 p0051
  have p0053 :=
    @gAnbi12d
      (.classEq R (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synWbr R (synCwe) D)
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) D)
      (.classEq C (synCnc D)) (.classEq C (synCnc D)) p0048 p0052
  have p0054 :=
    @gEqidd
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
  have p0055 :=
    @gId
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
  have p0056 :=
    @gBreq12d
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      D (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCwe) p0054 p0055
  have p0057 :=
    @gEqidd
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      C
  have p0059 :=
    @gNceqd
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      D (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      p0055
  have p0060 :=
    @gEqeq12d
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      C C (synCnc D)
      (synCnc (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      p0057 p0059
  have p0061 :=
    @gAnbi12d
      (.classEq D
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) D)
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (.classEq C (synCnc D))
      (.classEq C (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
      p0056 p0060
  have p0062 :=
    @gEqidd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
  have p0063 :=
    @gEqidd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
  have p0064 :=
    @gBreq12d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCwe) p0062 p0063
  have p0067 :=
    @gNceqd
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)) p0063
  have p0068 :=
    @gEqeq12d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      C
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C (synCnc (synC0)))
      (synCnc (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCnc (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      p0004 p0067
  have p0069 :=
    @gAnbi12d
      (.classEq C (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (.classEq C (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
      (.classEq (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))) (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
      p0064 p0068
  have p0070 :=
    @gId
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
  have p0071 :=
    @gEqidd
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synC0)
  have p0072 :=
    @gBreq12d
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synC0) (synC0) (synCwe) p0070 p0071
  have p0073 :=
    @gEqidd
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synCnc (synC0))
  have p0075 :=
    @gNceqd
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synC0) (synC0) p0071
  have p0076 :=
    @gEqeq12d
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synCnc (synC0)) (synCnc (synC0)) (synCnc (synC0)) (synCnc (synC0)) p0073
      p0075
  have p0077 :=
    @gAnbi12d
      (.classEq (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))))
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
      (.classEq (synCnc (synC0)) (synCnc (synC0)))
      (.classEq (synCnc (synC0)) (synCnc (synC0))) p0072 p0076
  have p0078 :=
    @gEqidd
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
  have p0079 :=
    @gId
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
  have p0080 :=
    @gBreq12d
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synC0)
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCwe) p0078 p0079
  have p0081 :=
    @gEqidd
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCnc (synC0))
  have p0083 :=
    @gNceqd
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synC0)
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)) p0079
  have p0084 :=
    @gEqeq12d
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCnc (synC0)) (synCnc (synC0)) (synCnc (synC0))
      (synCnc (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      p0081 p0083
  have p0085 :=
    @gAnbi12d
      (.classEq (synC0)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (.classEq (synCnc (synC0)) (synCnc (synC0)))
      (.classEq (synCnc (synC0)) (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
      p0080 p0084
  have p0086 :=
    @gEqidd
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
  have p0087 :=
    @gEqidd
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
  have p0088 :=
    @gBreq12d
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCwe) p0086 p0087
  have p0089 :=
    @gId
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
  have p0091 :=
    @gNceqd
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)) p0087
  have p0092 :=
    @gEqeq12d
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synCnc (synC0))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C (synCnc (synC0)))
      (synCnc (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synCnc (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      p0089 p0091
  have p0093 :=
    @gAnbi12d
      (.classEq (synCnc (synC0))
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (.classEq (synCnc (synC0)) (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
      (.classEq (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))) (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
      p0088 p0092
  have p0094 := @gWecomparisondefaultemptywe
  have p0095 := @gEqid (synCnc (synC0))
  have p0096 :=
    @gPm32i
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (.classEq (synCnc (synC0)) (synCnc (synC0))) p0094 p0095
  have p0097 :=
    @gElimhyp3v (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
      (synWa (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) D)
        (.classEq C (synCnc D)))
      (synWa (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
        (.classEq C (synCnc
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))))
      (synWa (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
        (.classEq (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0))) (synCnc
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))))
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (.classEq (synCnc (synC0)) (synCnc (synC0))))
      (synWa (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe) (synC0))
        (.classEq (synCnc (synC0)) (synCnc (synC0))))
      (synWa (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
        (.classEq (synCnc (synC0)) (synCnc
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))))
      R D C (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      (synCnc (synC0)) p0053 p0061 p0069 p0077 p0085 p0093 p0096
  have p0098 :=
    @gSimpl
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (.classEq (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))) (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
  have p0099 := Nominal.mp p0097 p0098
  have p0152 :=
    @gSimpr
      (synWbr (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))) (synCwe)
        (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0)))
      (.classEq (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
          (synCnc (synC0))) (synCnc
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))))
  have p0153 := Nominal.mp p0097 p0152
  have p0154 :=
    @gWppcandminfixedpivotdrfdv z
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C (synCnc (synC0)))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) D (synC0))
      (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) R
        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))))
      n F dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0099 p0153
      hyp_wppcandminfixedpivotpairdrfdv_1
  have p0155 :=
    @gDedth3v (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      (synWrex n (synCwppcand F
          (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
            (synCnc (synC0)))) (synWral z (synCwppcand F
            (synCif (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))) C
              (synCnc (synC0)))) (synWbr (.cv n) (synClec) (.cv z))))
      R D C (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      (synCnc (synC0)) p0001 p0003 p0045 p0154
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

/-- Checked nominal proof certificate identified upstream as
`g_wppcandminfixedpivotsetdeddrfdv`.
-/
@[expose]
noncomputable def gWppcandminfixedpivotsetdeddrfdv (z : Var) (C : Class) (D : Class)
    (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z) :
    Nominal.NPrf
      (.imp (.classMem F (synCvv))
        (.imp (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
          (synWrex n (synCwppcand F C)
            (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))))) :=
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
  have dv_cache_0001 : x ∉ ((synCimage (synCcnv F))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCimage (synCcnv F))).fv :=
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
    x ∉ ((synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))).fv :=
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
    y ∉ ((synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))).fv :=
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
    x ∉ ((Wff.classEq F (synCif (.classMem F (synCvv)) F (synC0)))).fv :=
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
    y ∉ ((Wff.classEq F (synCif (.classMem F (synCvv)) F (synC0)))).fv :=
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
  have dv_cache_0008 : z ∉ ((synCwppcand F C)).fv :=
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
    z ∉ ((synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)).fv :=
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
  have dv_cache_0010 : n ∉ ((synCwppcand F C)).fv :=
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
    n ∉ ((synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)).fv :=
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
    n ∉ ((Wff.classEq F (synCif (.classMem F (synCvv)) F (synC0)))).fv :=
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
  have dv_cache_0017 : n ∉ ((synCif (.classMem F (synCvv)) F (synC0))).fv :=
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
  have dv_cache_0018 : z ∉ ((synCif (.classMem F (synCvv)) F (synC0))).fv :=
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
  have p0000 := @gBiid (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
  have p0001 :=
    @gA1i
      (synWb (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
        (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D))))
      (.classEq F (synCif (.classMem F (synCvv)) F (synC0))) p0000
  have p0002 :=
    @gEqidd (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0003 := @gId (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
  have p0004 :=
    @gCnveqd (.classEq F (synCif (.classMem F (synCvv)) F (synC0))) F
      (synCif (.classMem F (synCvv)) F (synC0)) p0003
  have p0005 :=
    @gImaeq1d (.classEq F (synCif (.classMem F (synCvv)) F (synC0))) (synCcnv F)
      (synCcnv (synCif (.classMem F (synCvv)) F (synC0))) (.cv x) p0004
  have p0006 :=
    @gEqeq2d (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCima (synCcnv F) (.cv x))
      (synCima (synCcnv (synCif (.classMem F (synCvv)) F (synC0))) (.cv x)) (.cv y)
      p0005
  have p0007 := @gVex x
  have p0008 := @gVex y
  have p0009 := @gBrimage (.cv x) (.cv y) (synCcnv F) p0007 p0008
  have p0012 :=
    @gBrimage (.cv x) (.cv y) (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))
      p0007 p0008
  have p0013 :=
    @gN3bitr4g (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (.classEq (.cv y) (synCima (synCcnv F) (.cv x)))
      (.classEq (.cv y)
        (synCima (synCcnv (synCif (.classMem F (synCvv)) F (synC0))) (.cv x)))
      (synWbr (.cv x) (synCimage (synCcnv F)) (.cv y))
      (synWbr (.cv x)
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))) (.cv y))
      p0006 p0009 p0012
  have p0014 := (Nominal.biimpRefl (synWbr (.cv x) (synCimage (synCcnv F)) (.cv y)))
  have p0015 :=
    @gBicomi (synWbr (.cv x) (synCimage (synCcnv F)) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCimage (synCcnv F))) p0014
  have p0016 :=
    (Nominal.biimpRefl (synWbr (.cv x)
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))) (.cv y)))
  have p0017 :=
    @gBicomi
      (synWbr (.cv x)
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y))
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))))
      p0016
  have p0018 :=
    @gN3bitr4g (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synWbr (.cv x) (synCimage (synCcnv F)) (.cv y))
      (synWbr (.cv x)
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCimage (synCcnv F)))
      (.classMem (synCop (.cv x) (.cv y))
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))))
      p0013 p0015 p0017
  have p0019 :=
    @gEqrelrdv (.classEq F (synCif (.classMem F (synCvv)) F (synC0))) x y
      (synCimage (synCcnv F))
      (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0018
  have p0020 :=
    @gEqidd (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCima (synClec) (synCsn C))
  have p0021 :=
    @gJca (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (.classEq (synCimage (synCcnv F))
        (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))))
      (.classEq (synCima (synClec) (synCsn C)) (synCima (synClec) (synCsn C))) p0019
      p0020
  have p0022 :=
    @gFreceq12 (synCimage (synCcnv F))
      (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))
      (synCima (synClec) (synCsn C)) (synCima (synClec) (synCsn C))
  have p0023 :=
    @gSyl (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synWa (.classEq (synCimage (synCcnv F))
          (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0)))))
        (.classEq (synCima (synClec) (synCsn C)) (synCima (synClec) (synCsn C))))
      (.classEq (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCfrec (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))
          (synCima (synClec) (synCsn C))))
      p0021 p0022
  have p0024 :=
    @gRneqd (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCfrec (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))
        (synCima (synClec) (synCsn C)))
      p0023
  have p0025 :=
    @gUnieqd (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      (synCrn (synCfrec (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))
          (synCima (synClec) (synCsn C))))
      p0024
  have p0026 := (Nominal.classEqRefl (synCwppreach F C))
  have p0027 :=
    (Nominal.classEqRefl (synCwppreach (synCif (.classMem F (synCvv)) F (synC0)) C))
  have p0028 :=
    @gN3eqtr4g (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCuni
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      (synCuni (synCrn
          (synCfrec (synCimage (synCcnv (synCif (.classMem F (synCvv)) F (synC0))))
            (synCima (synClec) (synCsn C)))))
      (synCwppreach F C) (synCwppreach (synCif (.classMem F (synCvv)) F (synC0)) C)
      p0025 p0026 p0027
  have p0029 :=
    @gIneq12d (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synCwppreach F C) (synCwppreach (synCif (.classMem F (synCvv)) F (synC0)) C)
      p0002 p0028
  have p0030 := (Nominal.classEqRefl (synCwppcand F C))
  have p0031 :=
    (Nominal.classEqRefl (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C))
  have p0032 :=
    @gN3eqtr4g (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
        (synCwppreach F C))
      (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
        (synCwppreach (synCif (.classMem F (synCvv)) F (synC0)) C))
      (synCwppcand F C) (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
      p0029 p0030 p0031
  have p0064 :=
    @gRaleqdv (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synWbr (.cv n) (synClec) (.cv z)) z (synCwppcand F C)
      (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C) dv_cache_0008
      dv_cache_0009 p0032
  have p0065 :=
    @gRexeqbidv (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))
      (synWral z (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
        (synWbr (.cv n) (synClec) (.cv z)))
      n (synCwppcand F C) (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
      dv_cache_0010 dv_cache_0011 dv_cache_0012 p0032 p0064
  have p0066 :=
    @gImbi12d (.classEq F (synCif (.classMem F (synCvv)) F (synC0)))
      (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
      (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      (synWrex n (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
        (synWral z (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
          (synWbr (.cv n) (synClec) (.cv z))))
      p0001 p0065
  have p0067 := @gTru
  have p0068 := @gSimpr synWtru (.classMem F (synCvv))
  have p0069 := @gN0ex
  have p0070 :=
    @gA1i (.classMem (synC0) (synCvv)) (synWa synWtru (.neg (.classMem F (synCvv))))
      p0069
  have p0071 :=
    @gIfclda synWtru (.classMem F (synCvv)) F (synC0) (synCvv) p0068 p0070
  have p0072 := Nominal.mp p0067 p0071
  have p0073 :=
    @gWppcandminfixedpivotpairdrfdv z C D R n
      (synCif (.classMem F (synCvv)) F (synC0)) dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 p0072
  have p0074 :=
    @gDedth (.classMem F (synCvv))
      (.imp (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
        (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z)))))
      (.imp (synWa (synWbr R (synCwe) D) (.classEq C (synCnc D)))
        (synWrex n (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
          (synWral z (synCwppcand (synCif (.classMem F (synCvv)) F (synC0)) C)
            (synWbr (.cv n) (synClec) (.cv z)))))
      F (synC0) p0066 p0073
  exact p0074

/-- Checked nominal proof certificate identified upstream as `g_wppcandminhwndv`. -/
@[expose]
noncomputable def gWppcandminhwndv (z : Var) (C : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv)
    (dv_n_z : n ≠ z) :
    Nominal.NPrf
      (.imp (synWa (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv))))
        (synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))) :=
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
      ((synWb (.classMem C (synChwcards (synCvv))) (synWex d (synWex s
              (synWa (synWbr (.cv s) (synCwe) (.cv d))
                (.classEq C (synCnc (.cv d)))))))).fv :=
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
      ((synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))).fv :=
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
      ((synWrex n (synCwppcand F C)
          (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))).fv :=
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
  have dv_cache_0019 : d ∉ ((Wff.classMem F (synCvv))).fv :=
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
  have dv_cache_0020 : s ∉ ((Wff.classMem F (synCvv))).fv :=
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
  have p0000 := @gId (.classMem C (synChwcards (synCvv)))
  have p0001 := @gElex C (synChwcards (synCvv))
  have p0002 := @gId (.classEq (.cv c) C)
  have p0003 := @gEleq1d (.classEq (.cv c) C) (.cv c) C (synChwcards (synCvv)) p0002
  have p0005 := @gEqeq1d (.classEq (.cv c) C) (.cv c) C (synCnc (.cv d)) p0002
  have p0006 :=
    @gAnbi2d (.classEq (.cv c) C) (.classEq (.cv c) (synCnc (.cv d)))
      (.classEq C (synCnc (.cv d))) (synWbr (.cv s) (synCwe) (.cv d)) p0005
  have p0007 :=
    @gExbidv (.classEq (.cv c) C)
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv c) (synCnc (.cv d))))
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d)))) s
      dv_cache_0001 p0006
  have p0008 :=
    @gExbidv (.classEq (.cv c) C)
      (synWex s
        (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv c) (synCnc (.cv d)))))
      (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d)))))
      d dv_cache_0002 p0007
  have p0009 :=
    @gBibi12d (.classEq (.cv c) C) (.classMem (.cv c) (synChwcards (synCvv)))
      (.classMem C (synChwcards (synCvv)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv c) (synCnc (.cv d))))))
      (synWex d (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d))))))
      p0003 p0008
  have p0010 := @gElhwcardswev c s d dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0011 :=
    @gVtoclg
      (synWb (.classMem (.cv c) (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv c) (synCnc (.cv d)))))))
      (synWb (.classMem C (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d)))))))
      c C (synCvv) dv_cache_0006 dv_cache_0007 p0009 p0010
  have p0012 :=
    @gSyl (.classMem C (synChwcards (synCvv))) (.classMem C (synCvv))
      (synWb (.classMem C (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d)))))))
      p0001 p0011
  have p0013 :=
    @gMpbid (.classMem C (synChwcards (synCvv))) (.classMem C (synChwcards (synCvv)))
      (synWex d (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d))))))
      p0000 p0012
  have p0014 :=
    @gWppcandminfixedpivotsetdeddrfdv z C (.cv d) (.cv s) n F dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016
  have p0015 :=
    @gExlimdvv (.classMem F (synCvv))
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d))))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      d s dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0014
  have p0016 :=
    @gSyl5 (.classMem C (synChwcards (synCvv)))
      (synWex d (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq C (synCnc (.cv d))))))
      (.classMem F (synCvv))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      p0013 p0015
  have p0017 :=
    @gImp (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv)))
      (synWrex n (synCwppcand F C)
        (synWral z (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv z))))
      p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wppcandleastuniqclndv`. -/
@[expose]
noncomputable def gWppcandleastuniqclndv (A : Class) (B : Class) (C : Class) (k : Var)
    (F : Class) (dv_A_k : k ∉ A.fv) (dv_B_k : k ∉ B.fv) (dv_C_k : k ∉ C.fv)
    (dv_F_k : k ∉ F.fv)
    (hyp_wppcandleastuniqclndv_1 : Nominal.NPrf (.classMem A (synCwppcand F C)))
    (hyp_wppcandleastuniqclndv_2 :
      Nominal.NPrf (synWral k (synCwppcand F C) (synWbr A (synClec) (.cv k))))
    (hyp_wppcandleastuniqclndv_3 : Nominal.NPrf (.classMem B (synCwppcand F C)))
    (hyp_wppcandleastuniqclndv_4 :
      Nominal.NPrf (synWral k (synCwppcand F C) (synWbr B (synClec) (.cv k)))) :
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
  have dv_cache_0002 : k ∉ ((synCwppcand F C)).fv :=
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
  have dv_cache_0003 : k ∉ ((synWbr A (synClec) B)).fv :=
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
  have dv_cache_0005 : k ∉ ((synWbr B (synClec) A)).fv :=
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
  have p0000 := @gId (.classEq (.cv k) B)
  have p0001 := @gBreq2d (.classEq (.cv k) B) (.cv k) B A (synClec) p0000
  have p0002 :=
    @gRspcv (synWbr A (synClec) (.cv k)) (synWbr A (synClec) B) k B
      (synCwppcand F C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 := Nominal.mp hyp_wppcandleastuniqclndv_3 p0002
  have p0004 := Nominal.mp hyp_wppcandleastuniqclndv_2 p0003
  have p0005 := @gId (.classEq (.cv k) A)
  have p0006 := @gBreq2d (.classEq (.cv k) A) (.cv k) A B (synClec) p0005
  have p0007 :=
    @gRspcv (synWbr B (synClec) (.cv k)) (synWbr B (synClec) A) k A
      (synCwppcand F C) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0006
  have p0008 := Nominal.mp hyp_wppcandleastuniqclndv_1 p0007
  have p0009 := Nominal.mp hyp_wppcandleastuniqclndv_4 p0008
  have p0010 := @gPm32i (synWbr A (synClec) B) (synWbr B (synClec) A) p0004 p0009
  have p0011 := @gElwppcand C A F
  have p0012 :=
    @gBiimpi (.classMem A (synCwppcand F C))
      (synWa (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C))
        (.classMem A (synCwppreach F C)))
      p0011
  have p0013 := Nominal.mp hyp_wppcandleastuniqclndv_1 p0012
  have p0014 :=
    @gSimpl (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C))
      (.classMem A (synCwppreach F C))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gSimpl (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @gHwcardssnc (synCvv)
  have p0019 := @gSseli (synChwcards (synCvv)) (synCncs) A p0018
  have p0020 := Nominal.mp p0017 p0019
  have p0021 := @gElwppcand C B F
  have p0022 :=
    @gBiimpi (.classMem B (synCwppcand F C))
      (synWa (synWa (.classMem B (synChwcards (synCvv))) (synWbr B (synClec) C))
        (.classMem B (synCwppreach F C)))
      p0021
  have p0023 := Nominal.mp hyp_wppcandleastuniqclndv_3 p0022
  have p0024 :=
    @gSimpl (synWa (.classMem B (synChwcards (synCvv))) (synWbr B (synClec) C))
      (.classMem B (synCwppreach F C))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gSimpl (.classMem B (synChwcards (synCvv))) (synWbr B (synClec) C)
  have p0027 := Nominal.mp p0025 p0026
  have p0029 := @gSseli (synChwcards (synCvv)) (synCncs) B p0018
  have p0030 := Nominal.mp p0027 p0029
  have p0031 := @gPm32i (.classMem A (synCncs)) (.classMem B (synCncs)) p0020 p0030
  have p0032 := @gSbth A B
  have p0033 := Nominal.mp p0031 p0032
  have p0034 := Nominal.mp p0010 p0033
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end
