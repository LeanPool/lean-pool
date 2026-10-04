/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part066`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapexgndv`. -/
@[expose]
noncomputable def gHnsicodemapexgndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (.classMem (synChnsicodemap A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnsicodemap A))
  have p0001 :=
    @gA1i
      (.classEq (synChnsicodemap A) (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))))
      (.classMem A (synCvv)) p0000
  have p0002 := @gHnsicodeliftfnexndv
  have p0003 :=
    @gA1i (.classMem (synChnsicodeliftfn) (synCvv)) (.classMem A (synCvv)) p0002
  have p0004 := @gHwcnexg A
  have p0005 := @gPw1exg (synChwcn A) (synCvv)
  have p0006 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))
      (.classMem (synCpw1 (synChwcn A)) (synCvv)) p0004 p0005
  have p0007 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChnsicodeliftfn) (synCvv))
      (.classMem (synCpw1 (synChwcn A)) (synCvv)) p0003 p0006
  have p0008 :=
    @gResexg (synChnsicodeliftfn) (synCpw1 (synChwcn A)) (synCvv) (synCvv)
  have p0009 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChnsicodeliftfn) (synCvv))
        (.classMem (synCpw1 (synChwcn A)) (synCvv)))
      (.classMem (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) (synCvv))
      p0007 p0008
  have p0010 :=
    @gEqeltrd (.classMem A (synCvv)) (synChnsicodemap A)
      (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) (synCvv) p0001 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapvalndv`. -/
@[expose]
noncomputable def gHnsicodemapvalndv (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classEq (synCfv (synChnsicodemap A) (.cv q))
          (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ q } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : u ∉ ((synCuni (.cv q))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_q,
          not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((Wff.imp (.classMem (synCuni (.cv q)) (synChwcn A)) (.classEq (synCuni (.cv q))
            (synCop (synCfv (synC1st) (synCuni (.cv q)))
              (synCfv (synC2nd) (synCuni (.cv q))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (.classMem (synCuni (.cv q)) (synChwcn A))
          (synWss (synCfv (synC1st) (synCuni (.cv q)))
            (synCxp (synCfv (synC2nd) (synCuni (.cv q)))
              (synCfv (synC2nd) (synCuni (.cv q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChnsicodemap A))
  have p0001 :=
    @gFveq1i (.cv q) (synChnsicodemap A)
      (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synChnsicodemap A) (.cv q))
        (synCfv (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) (.cv q)))
      (.classMem (.cv q) (synCpw1 (synChwcn A))) p0001
  have p0003 := @gFvres (.cv q) (synCpw1 (synChwcn A)) (synChnsicodeliftfn)
  have p0004 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) (.cv q))
      (synCfv (synChnsicodeliftfn) (.cv q)) p0002 p0003
  have p0005 := @gHnwpw1argcl (synChwcn A) q
  have p0006 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0005
  have p0008 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0005
  have p0009 := @gElex (synCuni (.cv q)) (synChwcn A)
  have p0010 := @gId (.classEq (.cv u) (synCuni (.cv q)))
  have p0011 :=
    @gEleq1d (.classEq (.cv u) (synCuni (.cv q))) (.cv u) (synCuni (.cv q))
      (synChwcn A) p0010
  have p0014 :=
    @gFveq2d (.classEq (.cv u) (synCuni (.cv q))) (.cv u) (synCuni (.cv q)) (synC1st)
      p0010
  have p0016 :=
    @gFveq2d (.classEq (.cv u) (synCuni (.cv q))) (.cv u) (synCuni (.cv q)) (synC2nd)
      p0010
  have p0017 :=
    @gOpeq12d (.classEq (.cv u) (synCuni (.cv q))) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (synCuni (.cv q))) p0014 p0016
  have p0018 :=
    @gEqeq12d (.classEq (.cv u) (synCuni (.cv q))) (.cv u) (synCuni (.cv q))
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCop (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv q))))
      p0010 p0017
  have p0019 :=
    @gImbi12d (.classEq (.cv u) (synCuni (.cv q))) (.classMem (.cv u) (synChwcn A))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCuni (.cv q)) (synCop (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0011 p0018
  have p0020 := @gHwcnpair u A
  have p0021 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A)) (.classEq (.cv u)
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.imp (.classMem (synCuni (.cv q)) (synChwcn A)) (.classEq (synCuni (.cv q))
          (synCop (synCfv (synC1st) (synCuni (.cv q)))
            (synCfv (synC2nd) (synCuni (.cv q))))))
      u (synCuni (.cv q)) (synCvv) dv_cache_0001 dv_cache_0002 p0019 p0020
  have p0022 :=
    @gMpcom (.classMem (synCuni (.cv q)) (synCvv))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCop (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0009 p0021
  have p0023 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCop (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0008 p0022
  have p0024 :=
    @gSneqd (.classMem (.cv q) (synCpw1 (synChwcn A))) (synCuni (.cv q))
      (synCop (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv q))))
      p0023
  have p0025 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q)
      (synCsn (synCuni (.cv q)))
      (synCsn (synCop (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0006 p0024
  have p0026 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q)
      (synCsn (synCop (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      (synChnsicodeliftfn) p0025
  have p0038 :=
    @gXpeq12d (.classEq (.cv u) (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (synCuni (.cv q))) p0016 p0016
  have p0039 :=
    @gSseq12d (.classEq (.cv u) (synCuni (.cv q))) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (synCuni (.cv q)))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCxp (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv q))))
      p0014 p0038
  have p0040 :=
    @gImbi12d (.classEq (.cv u) (synCuni (.cv q))) (.classMem (.cv u) (synChwcn A))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (synCuni (.cv q)))
        (synCxp (synCfv (synC2nd) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0011 p0039
  have p0041 := @gHwcnsupp u A
  have p0042 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.imp (.classMem (synCuni (.cv q)) (synChwcn A))
        (synWss (synCfv (synC1st) (synCuni (.cv q)))
          (synCxp (synCfv (synC2nd) (synCuni (.cv q)))
            (synCfv (synC2nd) (synCuni (.cv q))))))
      u (synCuni (.cv q)) (synCvv) dv_cache_0001 dv_cache_0003 p0040 p0041
  have p0043 :=
    @gMpcom (.classMem (synCuni (.cv q)) (synCvv))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (synWss (synCfv (synC1st) (synCuni (.cv q)))
        (synCxp (synCfv (synC2nd) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0009 p0042
  have p0044 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (synWss (synCfv (synC1st) (synCuni (.cv q)))
        (synCxp (synCfv (synC2nd) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))))
      p0008 p0043
  have p0045 := @gSsv (synCfv (synC2nd) (synCuni (.cv q)))
  have p0047 :=
    @gPm32i (synWss (synCfv (synC2nd) (synCuni (.cv q))) (synCvv))
      (synWss (synCfv (synC2nd) (synCuni (.cv q))) (synCvv)) p0045 p0045
  have p0048 :=
    @gXpss12 (synCfv (synC2nd) (synCuni (.cv q))) (synCvv)
      (synCfv (synC2nd) (synCuni (.cv q))) (synCvv)
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @gA1i
      (synWss (synCxp (synCfv (synC2nd) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv q)))) (synCxp (synCvv) (synCvv)))
      (.classMem (.cv q) (synCpw1 (synChwcn A))) p0049
  have p0051 :=
    @gSstrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synC1st) (synCuni (.cv q)))
      (synCxp (synCfv (synC2nd) (synCuni (.cv q))) (synCfv (synC2nd) (synCuni (.cv q))))
      (synCxp (synCvv) (synCvv)) p0044 p0050
  have p0052 := @gFvex (synCuni (.cv q)) (synC1st)
  have p0053 := @gFvex (synCuni (.cv q)) (synC2nd)
  have p0054 :=
    @gHnsicodeliftfnvalgndv (synCfv (synC2nd) (synCuni (.cv q)))
      (synCfv (synC1st) (synCuni (.cv q))) p0052 p0053
  have p0055 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synWss (synCfv (synC1st) (synCuni (.cv q))) (synCxp (synCvv) (synCvv)))
      (.classEq (synCfv (synChnsicodeliftfn) (synCsn
            (synCop (synCfv (synC1st) (synCuni (.cv q)))
              (synCfv (synC2nd) (synCuni (.cv q))))))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
      p0051 p0054
  have p0056 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synChnsicodeliftfn) (.cv q))
      (synCfv (synChnsicodeliftfn) (synCsn (synCop (synCfv (synC1st) (synCuni (.cv q)))
            (synCfv (synC2nd) (synCuni (.cv q))))))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      p0026 p0055
  have p0057 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodeliftfn) (.cv q))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      p0004 p0056
  exact p0057

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapfndv`. -/
@[expose]
noncomputable def gHnsicodemapfndv (A : Class) :
    Nominal.NPrf
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synCuni (.cv q))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_q,
          not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (.classMem (synCuni (.cv q)) (synChwcn A))
          (.classMem (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
            (synChwcn (synCpw1 A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodeliftfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synChwcn (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((synChnsicodemap A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          fresh_q_not_A, not_false_eq_true])
  have p0000 := @gHnsicodeliftfnfnndv
  have p0001 := @gSsv (synCpw1 (synChwcn A))
  have p0002 :=
    @gPm32i (synWfn (synChnsicodeliftfn) (synCvv))
      (synWss (synCpw1 (synChwcn A)) (synCvv)) p0000 p0001
  have p0003 := @gFnssres (synCvv) (synCpw1 (synChwcn A)) (synChnsicodeliftfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (synChnsicodemap A))
  have p0006 :=
    @gFneq1i (synCpw1 (synChwcn A)) (synChnsicodemap A)
      (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) p0005
  have p0007 :=
    @gMpbir (synWfn (synChnsicodemap A) (synCpw1 (synChwcn A)))
      (synWfn (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A)))
        (synCpw1 (synChwcn A)))
      p0004 p0006
  have p0017 :=
    @gFveq1i (.cv q) (synChnsicodemap A)
      (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) p0005
  have p0018 :=
    @gA1i
      (.classEq (synCfv (synChnsicodemap A) (.cv q))
        (synCfv (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) (.cv q)))
      (.classMem (.cv q) (synCpw1 (synChwcn A))) p0017
  have p0019 := @gFvres (.cv q) (synCpw1 (synChwcn A)) (synChnsicodeliftfn)
  have p0020 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synCres (synChnsicodeliftfn) (synCpw1 (synChwcn A))) (.cv q))
      (synCfv (synChnsicodeliftfn) (.cv q)) p0018 p0019
  have p0021 := @gHnwpw1argcl (synChwcn A) q
  have p0022 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0021
  have p0023 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synChwcn A))) (.cv q)
      (synCsn (synCuni (.cv q))) (synChnsicodeliftfn) p0022
  have p0025 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0021
  have p0026 := @gElex (synCuni (.cv q)) (synChwcn A)
  have p0027 := @gId (.classEq (.cv u) (synCuni (.cv q)))
  have p0028 :=
    @gEleq1d (.classEq (.cv u) (synCuni (.cv q))) (.cv u) (synCuni (.cv q))
      (synChwcn A) p0027
  have p0030 :=
    @gSneqd (.classEq (.cv u) (synCuni (.cv q))) (.cv u) (synCuni (.cv q)) p0027
  have p0031 :=
    @gFveq2d (.classEq (.cv u) (synCuni (.cv q))) (synCsn (.cv u))
      (synCsn (synCuni (.cv q))) (synChnsicodeliftfn) p0030
  have p0032 :=
    @gEleq1d (.classEq (.cv u) (synCuni (.cv q)))
      (synCfv (synChnsicodeliftfn) (synCsn (.cv u)))
      (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
      (synChwcn (synCpw1 A)) p0031
  have p0033 :=
    @gImbi12d (.classEq (.cv u) (synCuni (.cv q))) (.classMem (.cv u) (synChwcn A))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classMem (synCfv (synChnsicodeliftfn) (synCsn (.cv u))) (synChwcn (synCpw1 A)))
      (.classMem (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
        (synChwcn (synCpw1 A)))
      p0028 p0032
  have p0034 := @gHwcnpair u A
  have p0035 :=
    @gSneqd (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) p0034
  have p0036 :=
    @gFveq2d (.classMem (.cv u) (synChwcn A)) (synCsn (.cv u))
      (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synChnsicodeliftfn) p0035
  have p0037 := @gHwcnsupp u A
  have p0038 := @gSsv (synCfv (synC2nd) (.cv u))
  have p0040 :=
    @gPm32i (synWss (synCfv (synC2nd) (.cv u)) (synCvv))
      (synWss (synCfv (synC2nd) (.cv u)) (synCvv)) p0038 p0038
  have p0041 :=
    @gXpss12 (synCfv (synC2nd) (.cv u)) (synCvv) (synCfv (synC2nd) (.cv u))
      (synCvv)
  have p0042 := Nominal.mp p0040 p0041
  have p0043 :=
    @gA1i
      (synWss (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synCxp (synCvv) (synCvv)))
      (.classMem (.cv u) (synChwcn A)) p0042
  have p0044 :=
    @gSstrd (.classMem (.cv u) (synChwcn A)) (synCfv (synC1st) (.cv u))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCxp (synCvv) (synCvv)) p0037 p0043
  have p0045 := @gFvex (.cv u) (synC1st)
  have p0046 := @gFvex (.cv u) (synC2nd)
  have p0047 :=
    @gHnsicodeliftfnvalgndv (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      p0045 p0046
  have p0048 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (synWss (synCfv (synC1st) (.cv u)) (synCxp (synCvv) (synCvv)))
      (.classEq (synCfv (synChnsicodeliftfn)
          (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCop (synCsi (synCfv (synC1st) (.cv u)))
          (synCpw1 (synCfv (synC2nd) (.cv u)))))
      p0044 p0047
  have p0049 :=
    @gEqtrd (.classMem (.cv u) (synChwcn A))
      (synCfv (synChnsicodeliftfn) (synCsn (.cv u)))
      (synCfv (synChnsicodeliftfn)
        (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (synCop (synCsi (synCfv (synC1st) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv u))))
      p0036 p0048
  have p0050 := @gHnsicodeliftcodeclndv u A dv_cache_0001
  have p0051 :=
    @gEqeltrd (.classMem (.cv u) (synChwcn A))
      (synCfv (synChnsicodeliftfn) (synCsn (.cv u)))
      (synCop (synCsi (synCfv (synC1st) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synChwcn (synCpw1 A)) p0049 p0050
  have p0052 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classMem (synCfv (synChnsicodeliftfn) (synCsn (.cv u))) (synChwcn (synCpw1 A))))
      (.imp (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classMem (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
          (synChwcn (synCpw1 A))))
      u (synCuni (.cv q)) (synCvv) dv_cache_0002 dv_cache_0003 p0033 p0051
  have p0053 :=
    @gMpcom (.classMem (synCuni (.cv q)) (synCvv))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classMem (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
        (synChwcn (synCpw1 A)))
      p0026 p0052
  have p0054 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classMem (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
        (synChwcn (synCpw1 A)))
      p0025 p0053
  have p0055 :=
    @gEqeltrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synChnsicodeliftfn) (.cv q))
      (synCfv (synChnsicodeliftfn) (synCsn (synCuni (.cv q))))
      (synChwcn (synCpw1 A)) p0023 p0054
  have p0056 :=
    @gEqeltrd (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synCfv (synChnsicodemap A) (.cv q)) (synCfv (synChnsicodeliftfn) (.cv q))
      (synChwcn (synCpw1 A)) p0020 p0055
  have p0057 :=
    @gRgen (.classMem (synCfv (synChnsicodemap A) (.cv q)) (synChwcn (synCpw1 A))) q
      (synCpw1 (synChwcn A)) p0056
  have p0058 :=
    @gPm32i (synWfn (synChnsicodemap A) (synCpw1 (synChwcn A)))
      (synWral q (synCpw1 (synChwcn A))
        (.classMem (synCfv (synChnsicodemap A) (.cv q)) (synChwcn (synCpw1 A))))
      p0007 p0057
  have p0059 :=
    @gFnfvrnss q (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synChnsicodemap A)
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0060 := Nominal.mp p0058 p0059
  have p0061 :=
    @gPm32i (synWfn (synChnsicodemap A) (synCpw1 (synChwcn A)))
      (synWss (synCrn (synChnsicodemap A)) (synChwcn (synCpw1 A))) p0007 p0060
  have p0062 :=
    (Nominal.biimpRefl
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A))))
  have p0063 :=
    @gMpbir
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (synWfn (synChnsicodemap A) (synCpw1 (synChwcn A)))
        (synWss (synCrn (synChnsicodemap A)) (synChwcn (synCpw1 A))))
      p0061 p0062
  exact p0063

/-- Checked nominal proof certificate identified upstream as `g_pw1typedbrndv`. -/
@[expose]
noncomputable def gPw1typedbrndv (D : Class) (R : Class) (q : Var) (p : Var)
    (_dv_D_p : p ∉ D.fv) (_dv_D_q : q ∉ D.fv) (_dv_R_p : p ∉ R.fv) (_dv_R_q : q ∉ R.fv)
    (_dv_p_q : p ≠ q) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
        (synWb (synWbr (.cv p) (synCsi R) (.cv q))
          (synWbr (synCuni (.cv p)) R (synCuni (.cv q))))) :=
  by
  have p0000 := @gSimpl (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))
  have p0001 := @gHnwpw1argcl D p
  have p0002 :=
    @gSyl (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (.classMem (.cv p) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv p)) D) (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      p0000 p0001
  have p0003 :=
    @gSimpr (.classMem (synCuni (.cv p)) D)
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0004 :=
    @gSyl (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv p)) D) (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0002 p0003
  have p0005 := @gSimpr (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))
  have p0006 := @gHnwpw1argcl D q
  have p0007 :=
    @gSyl (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0005 p0006
  have p0008 :=
    @gSimpr (.classMem (synCuni (.cv q)) D)
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0009 :=
    @gSyl (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0007 p0008
  have p0010 :=
    @gBreq12d (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (.cv p) (synCsn (synCuni (.cv p))) (.cv q) (synCsn (synCuni (.cv q)))
      (synCsi R) p0004 p0009
  have p0011 := @gVex p
  have p0012 := @gUniex (.cv p) p0011
  have p0013 := @gVex q
  have p0014 := @gUniex (.cv q) p0013
  have p0015 := @gBrsnsi (synCuni (.cv p)) (synCuni (.cv q)) R p0012 p0014
  have p0016 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv p))) (synCsi R) (synCsn (synCuni (.cv q))))
        (synWbr (synCuni (.cv p)) R (synCuni (.cv q))))
      (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))) p0015
  have p0017 :=
    @gBitrd (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (synWbr (.cv p) (synCsi R) (.cv q))
      (synWbr (synCsn (synCuni (.cv p))) (synCsi R) (synCsn (synCuni (.cv q))))
      (synWbr (synCuni (.cv p)) R (synCuni (.cv q))) p0010 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_pw1argclcl`. -/
@[expose]
noncomputable def gPw1argclcl (D : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (.classMem Q (synCpw1 D))
        (synWa (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ Q.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_Q : z ∉ Q.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (Q).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_Q, not_false_eq_true])
  have dv_cache_0002 : z ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0003 :
    z ∉ ((synWa (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_z_not_Q, fresh_z_not_D, or_false, not_false_eq_true])
  have p0000 := @gElpw1 z Q D dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classMem Q (synCpw1 D)) (synWrex z D (.classEq Q (synCsn (.cv z))))
      p0000
  have p0002 := @gSimpr (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))
  have p0003 :=
    @gUnieqd (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) Q
      (synCsn (.cv z)) p0002
  have p0004 := @gVex z
  have p0005 := @gUnisn (.cv z) p0004
  have p0006 :=
    @gA1i (.classEq (synCuni (synCsn (.cv z))) (.cv z))
      (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) p0005
  have p0007 :=
    @gEqtrd (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) (synCuni Q)
      (synCuni (synCsn (.cv z))) (.cv z) p0003 p0006
  have p0008 := @gSimpl (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))
  have p0009 :=
    @gEqeltrd (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) (synCuni Q)
      (.cv z) D p0007 p0008
  have p0017 :=
    @gEqcomd (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) (synCuni Q)
      (.cv z) p0007
  have p0018 :=
    @gSneqd (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) (.cv z)
      (synCuni Q) p0017
  have p0019 :=
    @gEqtrd (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z)))) Q
      (synCsn (.cv z)) (synCsn (synCuni Q)) p0002 p0018
  have p0020 :=
    @gJca (synWa (.classMem (.cv z) D) (.classEq Q (synCsn (.cv z))))
      (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q))) p0009 p0019
  have p0021 :=
    @gRexlimiva (.classEq Q (synCsn (.cv z)))
      (synWa (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q)))) z D
      dv_cache_0003 p0020
  have p0022 :=
    @gSyl (.classMem Q (synCpw1 D)) (synWrex z D (.classEq Q (synCsn (.cv z))))
      (synWa (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q)))) p0001 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_pw1descentf1odv`. -/
@[expose]
noncomputable def gPw1descentf1odv (x : Var) (D : Class) (g : Var) (E : Class)
    (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_g_x : g ≠ x) :
    Nominal.NPrf
      (.imp (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWf1o (synCmpt x D (synCuni (synCfv (.cv g) (synCsn (.cv x))))) D E)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ D.fv ∪ ({ g } : Finset Var) ∪ E.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0003 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_E, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCuni (synCfv (.cv g) (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_g, or_false, not_false_eq_true])
  have dv_cache_0006 :
    x ∉ ((synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, (Ne.symm dv_g_x), or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synWf1o (.cv g) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, dv_D_x, dv_E_x, (Ne.symm dv_g_x), or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWf1o (.cv g) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_E, fresh_y_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gEqid (synCmpt x D (synCuni (synCfv (.cv g) (synCsn (.cv x)))))
  have p0001 :=
    @gSimpl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D)
  have p0002 := @gF1of (synCpw1 D) (synCpw1 E) (.cv g)
  have p0003 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E)) p0001 p0002
  have p0004 :=
    @gSimpr (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D)
  have p0005 := @gSnelpw1 (.cv x) D
  have p0006 :=
    @gSylibr (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0004 p0005
  have p0007 :=
    @gJca (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCsn (.cv x)) (synCpw1 D)) p0003 p0006
  have p0008 := @gFfvelrn (synCpw1 D) (synCpw1 E) (synCsn (.cv x)) (.cv g)
  have p0009 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D))
      (synWa (synWf (.cv g) (synCpw1 D) (synCpw1 E))
        (.classMem (synCsn (.cv x)) (synCpw1 D)))
      (.classMem (synCfv (.cv g) (synCsn (.cv x))) (synCpw1 E)) p0007 p0008
  have p0010 := @gPw1argclcl E (synCfv (.cv g) (synCsn (.cv x)))
  have p0011 :=
    @gSimpl (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv x)))) E)
      (.classEq (synCfv (.cv g) (synCsn (.cv x)))
        (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x))))))
  have p0012 :=
    @gSyl (.classMem (synCfv (.cv g) (synCsn (.cv x))) (synCpw1 E))
      (synWa (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv x)))) E)
        (.classEq (synCfv (.cv g) (synCsn (.cv x)))
          (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x)))))))
      (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv x)))) E) p0010 p0011
  have p0013 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv x) D))
      (.classMem (synCfv (.cv g) (synCsn (.cv x))) (synCpw1 E))
      (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv x)))) E) p0009 p0012
  have p0014 :=
    @gSimpl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E)
  have p0015 := @gF1ocnv (synCpw1 D) (synCpw1 E) (.cv g)
  have p0016 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf1o (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D)) p0014 p0015
  have p0017 := @gF1of (synCpw1 E) (synCpw1 D) (synCcnv (.cv g))
  have p0018 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E))
      (synWf1o (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D))
      (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D)) p0016 p0017
  have p0019 :=
    @gSimpr (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E)
  have p0020 := @gSnelpw1 (.cv y) E
  have p0021 :=
    @gSylibr (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E))
      (.classMem (.cv y) E) (.classMem (synCsn (.cv y)) (synCpw1 E)) p0019 p0020
  have p0022 :=
    @gJca (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E))
      (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D))
      (.classMem (synCsn (.cv y)) (synCpw1 E)) p0018 p0021
  have p0023 := @gFfvelrn (synCpw1 E) (synCpw1 D) (synCsn (.cv y)) (synCcnv (.cv g))
  have p0024 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E))
      (synWa (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D))
        (.classMem (synCsn (.cv y)) (synCpw1 E)))
      (.classMem (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCpw1 D)) p0022 p0023
  have p0025 := @gPw1argclcl D (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
  have p0026 :=
    @gSimpl (.classMem (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) D)
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
        (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))))
  have p0027 :=
    @gSyl (.classMem (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCpw1 D))
      (synWa (.classMem (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) D)
        (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
          (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))))
      (.classMem (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) D) p0025 p0026
  have p0028 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv y) E))
      (.classMem (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCpw1 D))
      (.classMem (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) D) p0024 p0027
  have p0029 :=
    @gSimpl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0032 :=
    @gSyl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf1o (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D))
      (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D)) p0015 p0017
  have p0033 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D)) p0029 p0032
  have p0034 :=
    @gSimpr (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0035 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0036 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0034
      p0035
  have p0038 :=
    @gSylibr
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (.cv y) E) (.classMem (synCsn (.cv y)) (synCpw1 E)) p0036 p0020
  have p0039 :=
    @gJca
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D))
      (.classMem (synCsn (.cv y)) (synCpw1 E)) p0033 p0038
  have p0041 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWa (synWf (synCcnv (.cv g)) (synCpw1 E) (synCpw1 D))
        (.classMem (synCsn (.cv y)) (synCpw1 E)))
      (.classMem (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCpw1 D)) p0039 p0023
  have p0043 :=
    @gSimpr (.classMem (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) D)
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
        (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))))
  have p0044 :=
    @gSyl (.classMem (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCpw1 D))
      (synWa (.classMem (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) D)
        (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
          (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
        (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))))
      p0025 p0043
  have p0045 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCpw1 D))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
        (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))))
      p0041 p0044
  have p0046 :=
    @gEqeq1d
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))
      (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))
      (synCsn (.cv x)) p0045
  have p0047 := @gFvex (synCsn (.cv y)) (synCcnv (.cv g))
  have p0048 := @gUniex (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) p0047
  have p0049 :=
    @gSneqb (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) (.cv x) p0048
  have p0050 :=
    @gA1i
      (synWb (.classEq (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))
          (synCsn (.cv x)))
        (.classEq (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) (.cv x)))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0049
  have p0051 :=
    @gBitrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCsn (.cv x)))
      (.classEq (synCsn (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))
        (synCsn (.cv x)))
      (.classEq (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) (.cv x)) p0046
      p0050
  have p0052 := @gEqcom (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) (.cv x)
  have p0053 :=
    @gA1i
      (synWb (.classEq (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) (.cv x))
        (.classEq (.cv x) (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0052
  have p0054 :=
    @gBitrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCsn (.cv x)))
      (.classEq (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))) (.cv x))
      (.classEq (.cv x) (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))) p0051
      p0053
  have p0055 :=
    @gBicomd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCsn (.cv x)))
      (.classEq (.cv x) (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))) p0054
  have p0058 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0059 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0034
      p0058
  have p0061 :=
    @gSylibr
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0059 p0005
  have p0067 :=
    @gN3jca
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCsn (.cv x)) (synCpw1 D))
      (.classMem (synCsn (.cv y)) (synCpw1 E)) p0029 p0061 p0038
  have p0068 :=
    @gF1ocnvfvb (synCpw1 D) (synCpw1 E) (synCsn (.cv x)) (synCsn (.cv y)) (.cv g)
  have p0069 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synW3a (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (.classMem (synCsn (.cv x)) (synCpw1 D)) (.classMem (synCsn (.cv y)) (synCpw1 E)))
      (synWb (.classEq (synCfv (.cv g) (synCsn (.cv x))) (synCsn (.cv y)))
        (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCsn (.cv x))))
      p0067 p0068
  have p0070 :=
    @gBicomd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (synCfv (.cv g) (synCsn (.cv x))) (synCsn (.cv y)))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCsn (.cv x))) p0069
  have p0071 :=
    @gBitrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (.cv x) (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))
      (.classEq (synCfv (synCcnv (.cv g)) (synCsn (.cv y))) (synCsn (.cv x)))
      (.classEq (synCfv (.cv g) (synCsn (.cv x))) (synCsn (.cv y))) p0055 p0070
  have p0074 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E)) p0029 p0002
  have p0080 :=
    @gJca
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCsn (.cv x)) (synCpw1 D)) p0074 p0061
  have p0082 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synWa (synWf (.cv g) (synCpw1 D) (synCpw1 E))
        (.classMem (synCsn (.cv x)) (synCpw1 D)))
      (.classMem (synCfv (.cv g) (synCsn (.cv x))) (synCpw1 E)) p0080 p0008
  have p0084 :=
    @gSimpr (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv x)))) E)
      (.classEq (synCfv (.cv g) (synCsn (.cv x)))
        (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x))))))
  have p0085 :=
    @gSyl (.classMem (synCfv (.cv g) (synCsn (.cv x))) (synCpw1 E))
      (synWa (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv x)))) E)
        (.classEq (synCfv (.cv g) (synCsn (.cv x)))
          (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x)))))))
      (.classEq (synCfv (.cv g) (synCsn (.cv x)))
        (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x))))))
      p0010 p0084
  have p0086 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (synCfv (.cv g) (synCsn (.cv x))) (synCpw1 E))
      (.classEq (synCfv (.cv g) (synCsn (.cv x)))
        (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x))))))
      p0082 p0085
  have p0087 :=
    @gEqeq1d
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (synCfv (.cv g) (synCsn (.cv x)))
      (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x))))) (synCsn (.cv y)) p0086
  have p0088 := @gFvex (synCsn (.cv x)) (.cv g)
  have p0089 := @gUniex (synCfv (.cv g) (synCsn (.cv x))) p0088
  have p0090 := @gSneqb (synCuni (synCfv (.cv g) (synCsn (.cv x)))) (.cv y) p0089
  have p0091 :=
    @gA1i
      (synWb (.classEq (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x)))))
          (synCsn (.cv y))) (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv x)))) (.cv y)))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0090
  have p0092 :=
    @gBitrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (synCfv (.cv g) (synCsn (.cv x))) (synCsn (.cv y)))
      (.classEq (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv x))))) (synCsn (.cv y)))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv x)))) (.cv y)) p0087 p0091
  have p0093 := @gEqcom (synCuni (synCfv (.cv g) (synCsn (.cv x)))) (.cv y)
  have p0094 :=
    @gA1i
      (synWb (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv x)))) (.cv y))
        (.classEq (.cv y) (synCuni (synCfv (.cv g) (synCsn (.cv x))))))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0093
  have p0095 :=
    @gBitrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (synCfv (.cv g) (synCsn (.cv x))) (synCsn (.cv y)))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv x)))) (.cv y))
      (.classEq (.cv y) (synCuni (synCfv (.cv g) (synCsn (.cv x))))) p0092 p0094
  have p0096 :=
    @gBitrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (.cv x) (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y)))))
      (.classEq (synCfv (.cv g) (synCsn (.cv x))) (synCsn (.cv y)))
      (.classEq (.cv y) (synCuni (synCfv (.cv g) (synCsn (.cv x))))) p0071 p0095
  have p0097 :=
    @gF1o2d (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) x y D E
      (synCuni (synCfv (.cv g) (synCsn (.cv x))))
      (synCuni (synCfv (synCcnv (.cv g)) (synCsn (.cv y))))
      (synCmpt x D (synCuni (synCfv (.cv g) (synCsn (.cv x))))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 p0000 p0013 p0028 p0096
  exact p0097


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part067`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pw1typedbrcldv`. -/
@[expose]
noncomputable def gPw1typedbrcldv (D : Class) (P : Class) (Q : Class) (R : Class)
    (hyp_pw1typedbrcldv_1 : Nominal.NPrf (.classMem P (synCvv)))
    (hyp_pw1typedbrcldv_2 : Nominal.NPrf (.classMem Q (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D)))
        (synWb (synWbr P (synCsi R) Q) (synWbr (synCuni P) R (synCuni Q)))) :=
  by
  have p0000 := @gSimpl (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D))
  have p0001 := @gPw1argclcl D P
  have p0002 :=
    @gSyl (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D)))
      (.classMem P (synCpw1 D))
      (synWa (.classMem (synCuni P) D) (.classEq P (synCsn (synCuni P)))) p0000 p0001
  have p0003 := @gSimpr (.classMem (synCuni P) D) (.classEq P (synCsn (synCuni P)))
  have p0004 :=
    @gSyl (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D)))
      (synWa (.classMem (synCuni P) D) (.classEq P (synCsn (synCuni P))))
      (.classEq P (synCsn (synCuni P))) p0002 p0003
  have p0005 := @gSimpr (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D))
  have p0006 := @gPw1argclcl D Q
  have p0007 :=
    @gSyl (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D)))
      (.classMem Q (synCpw1 D))
      (synWa (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q)))) p0005 p0006
  have p0008 := @gSimpr (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q)))
  have p0009 :=
    @gSyl (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D)))
      (synWa (.classMem (synCuni Q) D) (.classEq Q (synCsn (synCuni Q))))
      (.classEq Q (synCsn (synCuni Q))) p0007 p0008
  have p0010 :=
    @gBreq12d (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D))) P
      (synCsn (synCuni P)) Q (synCsn (synCuni Q)) (synCsi R) p0004 p0009
  have p0011 := @gUniex P hyp_pw1typedbrcldv_1
  have p0012 := @gUniex Q hyp_pw1typedbrcldv_2
  have p0013 := @gBrsnsi (synCuni P) (synCuni Q) R p0011 p0012
  have p0014 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni P)) (synCsi R) (synCsn (synCuni Q)))
        (synWbr (synCuni P) R (synCuni Q)))
      (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D))) p0013
  have p0015 :=
    @gBitrd (synWa (.classMem P (synCpw1 D)) (.classMem Q (synCpw1 D)))
      (synWbr P (synCsi R) Q)
      (synWbr (synCsn (synCuni P)) (synCsi R) (synCsn (synCuni Q)))
      (synWbr (synCuni P) R (synCuni Q)) p0010 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_pw1descentisomdv`. -/
@[expose]
noncomputable def gPw1descentisomdv (z : Var) (D : Class) (R : Class) (S : Class)
    (g : Var) (E : Class) (dv_D_z : z ∉ D.fv) (dv_E_z : z ∉ E.fv) (dv_g_z : g ≠ z) :
    Nominal.NPrf
      (.imp (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWiso (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) R S D E)) :=
  by
  let proofSupport : Finset Var :=
    ({ z } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({ g } : Finset Var) ∪ E.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_g : a ≠ g := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_not_E : a ∉ E.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_z : b ≠ z := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_b : z ≠ b := Ne.symm fresh_b_ne_z
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_g : b ≠ g := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_not_E : b ∉ E.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : z ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0002 : z ∉ (E).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_z, not_false_eq_true])
  have dv_cache_0003 : g ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show g ≠ z from (by exact dv_g_z))
  have dv_cache_0004 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCuni (synCfv (.cv g) (synCsn (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_a, (Ne.symm dv_g_z), or_false,
          not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_b, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((synCuni (synCfv (.cv g) (synCsn (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_b, (Ne.symm dv_g_z), or_false,
          not_false_eq_true])
  have dv_cache_0008 : b ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_D, not_false_eq_true])
  have dv_cache_0009 :
    a ∉ ((synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_D, fresh_a_not_E, fresh_a_ne_g, fresh_a_not_R,
          fresh_a_not_S, or_false, not_false_eq_true])
  have dv_cache_0010 :
    b ∉ ((synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_D, fresh_b_not_E, fresh_b_ne_g, fresh_b_not_R,
          fresh_b_not_S, or_false, not_false_eq_true])
  have dv_cache_0011 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0012 : a ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_D, not_false_eq_true])
  have dv_cache_0013 : a ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_E, not_false_eq_true])
  have dv_cache_0014 : b ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_E, not_false_eq_true])
  have dv_cache_0015 :
    a ∉ ((synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_D, fresh_a_ne_z,
          fresh_a_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 :
    b ∉ ((synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_D, fresh_b_ne_z,
          fresh_b_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0018 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0019 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0020 : b ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_S, not_false_eq_true])
  have p0000 := @gIsof1o (synCpw1 D) (synCpw1 E) (synCsi R) (synCsi S) (.cv g)
  have p0001 := @gPw1descentf1odv z D g E dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gSyl (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf1o (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D E) p0000
      p0001
  have p0003 := @gVex a
  have p0004 := @gVex b
  have p0005 := @gBrsnsi (.cv a) (.cv b) R p0003 p0004
  have p0006 :=
    @gA1i
      (synWb (synWbr (synCsn (.cv a)) (synCsi R) (synCsn (.cv b)))
        (synWbr (.cv a) R (.cv b)))
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      p0005
  have p0007 :=
    @gBicomd
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWbr (synCsn (.cv a)) (synCsi R) (synCsn (.cv b)))
      (synWbr (.cv a) R (.cv b)) p0006
  have p0008 :=
    @gSimpl (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0009 :=
    @gSimpr (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0010 := @gSimpl (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0011 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv a) D) p0009
      p0010
  have p0012 := @gSnelpw1 (.cv a) D
  have p0013 :=
    @gSylibr
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv a) D) (.classMem (synCsn (.cv a)) (synCpw1 D)) p0011 p0012
  have p0015 := @gSimpr (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0016 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv b) D) p0009
      p0015
  have p0017 := @gSnelpw1 (.cv b) D
  have p0018 :=
    @gSylibr
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv b) D) (.classMem (synCsn (.cv b)) (synCpw1 D)) p0016 p0017
  have p0019 :=
    @gJca
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (synCsn (.cv a)) (synCpw1 D))
      (.classMem (synCsn (.cv b)) (synCpw1 D)) p0013 p0018
  have p0020 :=
    @gJca
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWa (.classMem (synCsn (.cv a)) (synCpw1 D))
        (.classMem (synCsn (.cv b)) (synCpw1 D)))
      p0008 p0019
  have p0021 :=
    @gIsorel (synCpw1 D) (synCpw1 E) (synCsn (.cv a)) (synCsn (.cv b)) (synCsi R)
      (synCsi S) (.cv g)
  have p0022 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (synCsn (.cv a)) (synCpw1 D))
          (.classMem (synCsn (.cv b)) (synCpw1 D))))
      (synWb (synWbr (synCsn (.cv a)) (synCsi R) (synCsn (.cv b)))
        (synWbr (synCfv (.cv g) (synCsn (.cv a))) (synCsi S)
          (synCfv (.cv g) (synCsn (.cv b)))))
      p0020 p0021
  have p0023 :=
    @gBitrd
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWbr (.cv a) R (.cv b))
      (synWbr (synCsn (.cv a)) (synCsi R) (synCsn (.cv b)))
      (synWbr (synCfv (.cv g) (synCsn (.cv a))) (synCsi S)
        (synCfv (.cv g) (synCsn (.cv b))))
      p0007 p0022
  have p0026 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) p0008 p0000
  have p0027 := @gF1of (synCpw1 D) (synCpw1 E) (.cv g)
  have p0028 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E)) p0026 p0027
  have p0034 :=
    @gJca
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCsn (.cv a)) (synCpw1 D)) p0028 p0013
  have p0035 := @gFfvelrn (synCpw1 D) (synCpw1 E) (synCsn (.cv a)) (.cv g)
  have p0036 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWa (synWf (.cv g) (synCpw1 D) (synCpw1 E))
        (.classMem (synCsn (.cv a)) (synCpw1 D)))
      (.classMem (synCfv (.cv g) (synCsn (.cv a))) (synCpw1 E)) p0034 p0035
  have p0047 :=
    @gJca
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCsn (.cv b)) (synCpw1 D)) p0028 p0018
  have p0048 := @gFfvelrn (synCpw1 D) (synCpw1 E) (synCsn (.cv b)) (.cv g)
  have p0049 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWa (synWf (.cv g) (synCpw1 D) (synCpw1 E))
        (.classMem (synCsn (.cv b)) (synCpw1 D)))
      (.classMem (synCfv (.cv g) (synCsn (.cv b))) (synCpw1 E)) p0047 p0048
  have p0050 :=
    @gJca
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (synCfv (.cv g) (synCsn (.cv a))) (synCpw1 E))
      (.classMem (synCfv (.cv g) (synCsn (.cv b))) (synCpw1 E)) p0036 p0049
  have p0051 := @gFvex (synCsn (.cv a)) (.cv g)
  have p0052 := @gFvex (synCsn (.cv b)) (.cv g)
  have p0053 :=
    @gPw1typedbrcldv E (synCfv (.cv g) (synCsn (.cv a)))
      (synCfv (.cv g) (synCsn (.cv b))) S p0051 p0052
  have p0054 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWa (.classMem (synCfv (.cv g) (synCsn (.cv a))) (synCpw1 E))
        (.classMem (synCfv (.cv g) (synCsn (.cv b))) (synCpw1 E)))
      (synWb (synWbr (synCfv (.cv g) (synCsn (.cv a))) (synCsi S)
          (synCfv (.cv g) (synCsn (.cv b))))
        (synWbr (synCuni (synCfv (.cv g) (synCsn (.cv a)))) S
          (synCuni (synCfv (.cv g) (synCsn (.cv b))))))
      p0050 p0053
  have p0055 :=
    @gBitrd
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWbr (.cv a) R (.cv b))
      (synWbr (synCfv (.cv g) (synCsn (.cv a))) (synCsi S)
        (synCfv (.cv g) (synCsn (.cv b))))
      (synWbr (synCuni (synCfv (.cv g) (synCsn (.cv a)))) S
        (synCuni (synCfv (.cv g) (synCsn (.cv b)))))
      p0023 p0054
  have p0059 := @gId (.classEq (.cv z) (.cv a))
  have p0060 := @gSneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0059
  have p0061 :=
    @gFveq2d (.classEq (.cv z) (.cv a)) (synCsn (.cv z)) (synCsn (.cv a)) (.cv g) p0060
  have p0062 :=
    @gUnieqd (.classEq (.cv z) (.cv a)) (synCfv (.cv g) (synCsn (.cv z)))
      (synCfv (.cv g) (synCsn (.cv a))) p0061
  have p0063 := @gEqid (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
  have p0065 := @gUniex (synCfv (.cv g) (synCsn (.cv a))) p0051
  have p0066 :=
    @gFvmpt z (.cv a) (synCuni (synCfv (.cv g) (synCsn (.cv z))))
      (synCuni (synCfv (.cv g) (synCsn (.cv a)))) D
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) dv_cache_0004
      dv_cache_0005 dv_cache_0001 p0062 p0063 p0065
  have p0067 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv a) D)
      (.classEq (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
        (synCuni (synCfv (.cv g) (synCsn (.cv a)))))
      p0011 p0066
  have p0068 :=
    @gEqcomd
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
      (synCuni (synCfv (.cv g) (synCsn (.cv a)))) p0067
  have p0072 := @gId (.classEq (.cv z) (.cv b))
  have p0073 := @gSneqd (.classEq (.cv z) (.cv b)) (.cv z) (.cv b) p0072
  have p0074 :=
    @gFveq2d (.classEq (.cv z) (.cv b)) (synCsn (.cv z)) (synCsn (.cv b)) (.cv g) p0073
  have p0075 :=
    @gUnieqd (.classEq (.cv z) (.cv b)) (synCfv (.cv g) (synCsn (.cv z)))
      (synCfv (.cv g) (synCsn (.cv b))) p0074
  have p0078 := @gUniex (synCfv (.cv g) (synCsn (.cv b))) p0052
  have p0079 :=
    @gFvmpt z (.cv b) (synCuni (synCfv (.cv g) (synCsn (.cv z))))
      (synCuni (synCfv (.cv g) (synCsn (.cv b)))) D
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0075 p0063 p0078
  have p0080 :=
    @gSyl
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv b) D)
      (.classEq (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
        (synCuni (synCfv (.cv g) (synCsn (.cv b)))))
      p0016 p0079
  have p0081 :=
    @gEqcomd
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      (synCuni (synCfv (.cv g) (synCsn (.cv b)))) p0080
  have p0082 :=
    @gBreq12d
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synCuni (synCfv (.cv g) (synCsn (.cv a))))
      (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
      (synCuni (synCfv (.cv g) (synCsn (.cv b))))
      (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)) S
      p0068 p0081
  have p0083 :=
    @gBitrd
      (synWa (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
        (synWa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (synWbr (.cv a) R (.cv b))
      (synWbr (synCuni (synCfv (.cv g) (synCsn (.cv a)))) S
        (synCuni (synCfv (.cv g) (synCsn (.cv b)))))
      (synWbr (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a)) S
        (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      p0055 p0082
  have p0084 :=
    @gRalrimivva (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWb (synWbr (.cv a) R (.cv b)) (synWbr
          (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a)) S
          (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))))
      a b D D dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0083
  have p0085 :=
    @gJca (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWf1o (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D E)
      (synWral a D (synWral b D (synWb (synWbr (.cv a) R (.cv b)) (synWbr
              (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a)) S
              (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
                (.cv b))))))
      p0002 p0084
  have p0086 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso a b D E R S
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) dv_cache_0012
      dv_cache_0008 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0011
  have p0087 :=
    @gBiimpri
      (synWiso (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) R S D E)
      (synWa (synWf1o (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D E)
        (synWral a D (synWral b D (synWb (synWbr (.cv a) R (.cv b)) (synWbr
                (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
                S (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
                  (.cv b)))))))
      p0086
  have p0088 :=
    @gSyl (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWa (synWf1o (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D E)
        (synWral a D (synWral b D (synWb (synWbr (.cv a) R (.cv b)) (synWbr
                (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
                S (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
                  (.cv b)))))))
      (synWiso (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) R S D E)
      p0085 p0087
  exact p0088

/-- Checked nominal proof certificate identified upstream as `g_sifvalimpclndv`. -/
@[expose]
noncomputable def gSifvalimpclndv (C : Class) (D : Class) (E : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf F D E) (.classMem C D))
        (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ E.fv ∪ F.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_E : c ∉ E.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have dv_cache_0001 : c ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0002 :
    c ∉
      ((Wff.imp (.classMem C D)
          (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_c_not_C, fresh_c_not_D, fresh_c_not_F, or_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((synWa (synWf F D E) (.classMem C D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_c_not_D,
          fresh_c_not_E, fresh_c_not_F, fresh_c_not_C, or_false, not_false_eq_true])
  have p0000 := @gSimpr (synWf F D E) (.classMem C D)
  have p0002 := @gElex C D
  have p0003 :=
    @gSyl (synWa (synWf F D E) (.classMem C D)) (.classMem C D) (.classMem C (synCvv))
      p0000 p0002
  have p0004 := @gSimpr (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C)
  have p0005 := @gEleq1 (.cv c) C D
  have p0006 :=
    @gSyl (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (.classEq (.cv c) C) (synWb (.classMem (.cv c) D) (.classMem C D)) p0004 p0005
  have p0008 :=
    @gSneqd (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C)) (.cv c)
      C p0004
  have p0009 :=
    @gFveq2d (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (synCsn (.cv c)) (synCsn C) (synCsi F) p0008
  have p0011 :=
    @gFveq2d (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (.cv c) C F p0004
  have p0012 :=
    @gSneqd (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (synCfv F (.cv c)) (synCfv F C) p0011
  have p0013 :=
    @gEqeq12d (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (synCfv (synCsi F) (synCsn (.cv c))) (synCfv (synCsi F) (synCsn C))
      (synCsn (synCfv F (.cv c))) (synCsn (synCfv F C)) p0009 p0012
  have p0014 :=
    @gImbi12d (synWa (synWa (synWf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (.classMem (.cv c) D) (.classMem C D)
      (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c))))
      (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))) p0006 p0013
  have p0015 := @gSimpl (synWf F D E) (.classMem C D)
  have p0016 := @gSimpl (synWf F D E) (.classMem (.cv c) D)
  have p0017 := @gFfn D E F
  have p0018 :=
    @gSyl (synWa (synWf F D E) (.classMem (.cv c) D)) (synWf F D E) (synWfn F D)
      p0016 p0017
  have p0019 := @gSimpr (synWf F D E) (.classMem (.cv c) D)
  have p0020 :=
    @gJca (synWa (synWf F D E) (.classMem (.cv c) D)) (synWfn F D)
      (.classMem (.cv c) D) p0018 p0019
  have p0021 := @gSifnvalv c D F
  have p0022 :=
    @gSyl (synWa (synWf F D E) (.classMem (.cv c) D))
      (synWa (synWfn F D) (.classMem (.cv c) D))
      (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c))))
      p0020 p0021
  have p0023 :=
    @gEx (synWf F D E) (.classMem (.cv c) D)
      (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c))))
      p0022
  have p0024 :=
    @gSyl (synWa (synWf F D E) (.classMem C D)) (synWf F D E)
      (.imp (.classMem (.cv c) D)
        (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c)))))
      p0015 p0023
  have p0025 :=
    @gVtocld (synWa (synWf F D E) (.classMem C D))
      (.imp (.classMem (.cv c) D)
        (.classEq (synCfv (synCsi F) (synCsn (.cv c))) (synCsn (synCfv F (.cv c)))))
      (.imp (.classMem C D)
        (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))))
      c C (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0003 p0014 p0024
  have p0026 :=
    @gMpd (synWa (synWf F D E) (.classMem C D)) (.classMem C D)
      (.classEq (synCfv (synCsi F) (synCsn C)) (synCsn (synCfv F C))) p0000 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_pw1sif1omapndv`. -/
@[expose]
noncomputable def gPw1sif1omapndv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWf1o F A B) (synWf1o (synCsi F) (synCpw1 A) (synCpw1 B))) :=
  by
  have p0000 := @gF1of A B F
  have p0001 := @gSifmap A B F
  have p0002 :=
    @gSyl (synWf1o F A B) (synWf F A B) (synWf (synCsi F) (synCpw1 A) (synCpw1 B))
      p0000 p0001
  have p0003 := @gFfn (synCpw1 A) (synCpw1 B) (synCsi F)
  have p0004 :=
    @gSyl (synWf1o F A B) (synWf (synCsi F) (synCpw1 A) (synCpw1 B))
      (synWfn (synCsi F) (synCpw1 A)) p0002 p0003
  have p0005 := @gF1ocnv A B F
  have p0006 := @gF1of B A (synCcnv F)
  have p0007 :=
    @gSyl (synWf1o F A B) (synWf1o (synCcnv F) B A) (synWf (synCcnv F) B A) p0005
      p0006
  have p0008 := @gSifmap B A (synCcnv F)
  have p0009 :=
    @gSyl (synWf1o F A B) (synWf (synCcnv F) B A)
      (synWf (synCsi (synCcnv F)) (synCpw1 B) (synCpw1 A)) p0007 p0008
  have p0010 := @gFfn (synCpw1 B) (synCpw1 A) (synCsi (synCcnv F))
  have p0011 :=
    @gSyl (synWf1o F A B) (synWf (synCsi (synCcnv F)) (synCpw1 B) (synCpw1 A))
      (synWfn (synCsi (synCcnv F)) (synCpw1 B)) p0009 p0010
  have p0012 := @gCnvsi F
  have p0013 := @gFneq1i (synCpw1 B) (synCcnv (synCsi F)) (synCsi (synCcnv F)) p0012
  have p0014 :=
    @gSylibr (synWf1o F A B) (synWfn (synCsi (synCcnv F)) (synCpw1 B))
      (synWfn (synCcnv (synCsi F)) (synCpw1 B)) p0011 p0013
  have p0015 :=
    @gJca (synWf1o F A B) (synWfn (synCsi F) (synCpw1 A))
      (synWfn (synCcnv (synCsi F)) (synCpw1 B)) p0004 p0014
  have p0016 := @gDff1o4 (synCpw1 A) (synCpw1 B) (synCsi F)
  have p0017 :=
    @gSylibr (synWf1o F A B)
      (synWa (synWfn (synCsi F) (synCpw1 A)) (synWfn (synCcnv (synCsi F)) (synCpw1 B)))
      (synWf1o (synCsi F) (synCpw1 A) (synCpw1 B)) p0015 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part068`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pw1raiseisomdv`. -/
@[expose]
noncomputable def gPw1raiseisomdv (D : Class) (R : Class) (S : Class) (f : Var)
    (E : Class) :
    Nominal.NPrf
      (.imp (synWiso (.cv f) R S D E)
        (synWiso (synCsi (.cv f)) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ E.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_S : p ∉ S.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_ne_f : p ≠ f := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_not_E : p ∉ E.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_S : q ∉ S.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_ne_f : q ≠ f := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_q_not_E : q ∉ E.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : p ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_D, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0003 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0004 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0005 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0006 : q ∉ ((synCpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0007 : p ∉ ((synWiso (.cv f) R S D E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_D, fresh_p_not_E, fresh_p_ne_f, fresh_p_not_R,
          fresh_p_not_S, or_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((synWiso (.cv f) R S D E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_D, fresh_q_not_E, fresh_q_ne_f, fresh_q_not_R,
          fresh_q_not_S, or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((synCpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCpw1 E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_E,
          not_false_eq_true])
  have dv_cache_0011 : q ∉ ((synCpw1 E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_E,
          not_false_eq_true])
  have dv_cache_0012 : p ∉ ((synCsi (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_p_ne_f,
          not_false_eq_true])
  have dv_cache_0013 : q ∉ ((synCsi (.cv f))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_f,
          not_false_eq_true])
  have dv_cache_0014 : p ∉ ((synCsi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_p_not_R,
          not_false_eq_true])
  have dv_cache_0015 : q ∉ ((synCsi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_q_not_R,
          not_false_eq_true])
  have dv_cache_0016 : p ∉ ((synCsi S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_p_not_S,
          not_false_eq_true])
  have dv_cache_0017 : q ∉ ((synCsi S)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_q_not_S,
          not_false_eq_true])
  have p0000 := @gIsof1o D E R S (.cv f)
  have p0001 := @gPw1sif1omapndv D E (.cv f)
  have p0002 :=
    @gSyl (synWiso (.cv f) R S D E) (synWf1o (.cv f) D E)
      (synWf1o (synCsi (.cv f)) (synCpw1 D) (synCpw1 E)) p0000 p0001
  have p0003 :=
    @gSimpr (synWiso (.cv f) R S D E)
      (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
  have p0004 :=
    @gPw1typedbrndv D R q p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0005 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (synWb (synWbr (.cv p) (synCsi R) (.cv q))
        (synWbr (synCuni (.cv p)) R (synCuni (.cv q))))
      p0003 p0004
  have p0006 :=
    @gSimpl (synWiso (.cv f) R S D E)
      (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
  have p0008 := @gSimpl (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))
  have p0009 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (.classMem (.cv p) (synCpw1 D)) p0003 p0008
  have p0010 := @gHnwpw1argcl D p
  have p0011 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (.classMem (.cv p) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv p)) D) (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      p0009 p0010
  have p0012 :=
    @gSimpl (.classMem (synCuni (.cv p)) D)
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0013 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (synCuni (.cv p)) D) (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classMem (synCuni (.cv p)) D) p0011 p0012
  have p0015 := @gSimpr (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))
  have p0016 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D)))
      (.classMem (.cv q) (synCpw1 D)) p0003 p0015
  have p0017 := @gHnwpw1argcl D q
  have p0018 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (.classMem (.cv q) (synCpw1 D))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0016 p0017
  have p0019 :=
    @gSimpl (.classMem (synCuni (.cv q)) D)
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0020 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) D) p0018 p0019
  have p0021 :=
    @gJca
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (.classMem (synCuni (.cv p)) D) (.classMem (synCuni (.cv q)) D) p0013 p0020
  have p0022 :=
    @gJca
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWiso (.cv f) R S D E)
      (synWa (.classMem (synCuni (.cv p)) D) (.classMem (synCuni (.cv q)) D)) p0006
      p0021
  have p0023 := @gIsorel D E (synCuni (.cv p)) (synCuni (.cv q)) R S (.cv f)
  have p0024 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (synCuni (.cv p)) D) (.classMem (synCuni (.cv q)) D)))
      (synWb (synWbr (synCuni (.cv p)) R (synCuni (.cv q)))
        (synWbr (synCfv (.cv f) (synCuni (.cv p))) S (synCfv (.cv f) (synCuni (.cv q)))))
      p0022 p0023
  have p0025 :=
    @gBitrd
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWbr (.cv p) (synCsi R) (.cv q))
      (synWbr (synCuni (.cv p)) R (synCuni (.cv q)))
      (synWbr (synCfv (.cv f) (synCuni (.cv p))) S (synCfv (.cv f) (synCuni (.cv q))))
      p0005 p0024
  have p0031 :=
    @gSimpr (.classMem (synCuni (.cv p)) D)
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0032 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (synCuni (.cv p)) D) (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0011 p0031
  have p0033 :=
    @gFveq2d
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (.cv p) (synCsn (synCuni (.cv p))) (synCsi (.cv f)) p0032
  have p0036 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWiso (.cv f) R S D E) (synWf1o (.cv f) D E) p0006 p0000
  have p0037 := @gF1of D E (.cv f)
  have p0038 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWf1o (.cv f) D E) (synWf (.cv f) D E) p0036 p0037
  have p0046 :=
    @gJca
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWf (.cv f) D E) (.classMem (synCuni (.cv p)) D) p0038 p0013
  have p0047 := @gSifvalimpclndv (synCuni (.cv p)) D E (.cv f)
  have p0048 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (synWf (.cv f) D E) (.classMem (synCuni (.cv p)) D))
      (.classEq (synCfv (synCsi (.cv f)) (synCsn (synCuni (.cv p))))
        (synCsn (synCfv (.cv f) (synCuni (.cv p)))))
      p0046 p0047
  have p0049 :=
    @gEqtrd
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synCfv (synCsi (.cv f)) (.cv p))
      (synCfv (synCsi (.cv f)) (synCsn (synCuni (.cv p))))
      (synCsn (synCfv (.cv f) (synCuni (.cv p)))) p0033 p0048
  have p0055 :=
    @gSimpr (.classMem (synCuni (.cv q)) D)
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0056 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (.classMem (synCuni (.cv q)) D) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0018 p0055
  have p0057 :=
    @gFveq2d
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (.cv q) (synCsn (synCuni (.cv q))) (synCsi (.cv f)) p0056
  have p0070 :=
    @gJca
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWf (.cv f) D E) (.classMem (synCuni (.cv q)) D) p0038 p0020
  have p0071 := @gSifvalimpclndv (synCuni (.cv q)) D E (.cv f)
  have p0072 :=
    @gSyl
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWa (synWf (.cv f) D E) (.classMem (synCuni (.cv q)) D))
      (.classEq (synCfv (synCsi (.cv f)) (synCsn (synCuni (.cv q))))
        (synCsn (synCfv (.cv f) (synCuni (.cv q)))))
      p0070 p0071
  have p0073 :=
    @gEqtrd
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synCfv (synCsi (.cv f)) (.cv q))
      (synCfv (synCsi (.cv f)) (synCsn (synCuni (.cv q))))
      (synCsn (synCfv (.cv f) (synCuni (.cv q)))) p0057 p0072
  have p0074 :=
    @gBreq12d
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synCfv (synCsi (.cv f)) (.cv p)) (synCsn (synCfv (.cv f) (synCuni (.cv p))))
      (synCfv (synCsi (.cv f)) (.cv q)) (synCsn (synCfv (.cv f) (synCuni (.cv q))))
      (synCsi S) p0049 p0073
  have p0075 := @gFvex (synCuni (.cv p)) (.cv f)
  have p0076 := @gFvex (synCuni (.cv q)) (.cv f)
  have p0077 :=
    @gBrsnsi (synCfv (.cv f) (synCuni (.cv p))) (synCfv (.cv f) (synCuni (.cv q))) S
      p0075 p0076
  have p0078 :=
    @gA1i
      (synWb (synWbr (synCsn (synCfv (.cv f) (synCuni (.cv p)))) (synCsi S)
          (synCsn (synCfv (.cv f) (synCuni (.cv q)))))
        (synWbr (synCfv (.cv f) (synCuni (.cv p))) S (synCfv (.cv f) (synCuni (.cv q)))))
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      p0077
  have p0079 :=
    @gBitrd
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
        (synCfv (synCsi (.cv f)) (.cv q)))
      (synWbr (synCsn (synCfv (.cv f) (synCuni (.cv p)))) (synCsi S)
        (synCsn (synCfv (.cv f) (synCuni (.cv q)))))
      (synWbr (synCfv (.cv f) (synCuni (.cv p))) S (synCfv (.cv f) (synCuni (.cv q))))
      p0074 p0078
  have p0080 :=
    @gBicomd
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
        (synCfv (synCsi (.cv f)) (.cv q)))
      (synWbr (synCfv (.cv f) (synCuni (.cv p))) S (synCfv (.cv f) (synCuni (.cv q))))
      p0079
  have p0081 :=
    @gBitrd
      (synWa (synWiso (.cv f) R S D E)
        (synWa (.classMem (.cv p) (synCpw1 D)) (.classMem (.cv q) (synCpw1 D))))
      (synWbr (.cv p) (synCsi R) (.cv q))
      (synWbr (synCfv (.cv f) (synCuni (.cv p))) S (synCfv (.cv f) (synCuni (.cv q))))
      (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
        (synCfv (synCsi (.cv f)) (.cv q)))
      p0025 p0080
  have p0082 :=
    @gRalrimivva (synWiso (.cv f) R S D E)
      (synWb (synWbr (.cv p) (synCsi R) (.cv q))
        (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
          (synCfv (synCsi (.cv f)) (.cv q))))
      p q (synCpw1 D) (synCpw1 D) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0005 p0081
  have p0083 :=
    @gJca (synWiso (.cv f) R S D E)
      (synWf1o (synCsi (.cv f)) (synCpw1 D) (synCpw1 E))
      (synWral p (synCpw1 D) (synWral q (synCpw1 D)
          (synWb (synWbr (.cv p) (synCsi R) (.cv q))
            (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
              (synCfv (synCsi (.cv f)) (.cv q))))))
      p0002 p0082
  have p0084 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso p q (synCpw1 D)
      (synCpw1 E) (synCsi R) (synCsi S) (synCsi (.cv f)) dv_cache_0009 dv_cache_0006
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0005
  have p0085 :=
    @gBiimpri
      (synWiso (synCsi (.cv f)) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWa (synWf1o (synCsi (.cv f)) (synCpw1 D) (synCpw1 E)) (synWral p (synCpw1 D)
          (synWral q (synCpw1 D) (synWb (synWbr (.cv p) (synCsi R) (.cv q))
              (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
                (synCfv (synCsi (.cv f)) (.cv q)))))))
      p0084
  have p0086 :=
    @gSyl (synWiso (.cv f) R S D E)
      (synWa (synWf1o (synCsi (.cv f)) (synCpw1 D) (synCpw1 E)) (synWral p (synCpw1 D)
          (synWral q (synCpw1 D) (synWb (synWbr (.cv p) (synCsi R) (.cv q))
              (synWbr (synCfv (synCsi (.cv f)) (.cv p)) (synCsi S)
                (synCfv (synCsi (.cv f)) (.cv q)))))))
      (synWiso (synCsi (.cv f)) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E)) p0083
      p0085
  exact p0086

/-- Checked nominal proof certificate identified upstream as `g_hndownbrndv`. -/
@[expose]
noncomputable def gHndownbrndv (x : Var) (y : Var) (g : Var) (a : Var) (b : Var)
    (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWbr (.cv a)
          (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))) :=
  by
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_x), not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_y), not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_b_x), not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_b_y), not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_x), (Ne.symm dv_b_x), (Ne.symm dv_g_x),
          or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_y), (Ne.symm dv_b_y), (Ne.symm dv_g_y),
          or_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gVex a
  have p0001 := @gVex b
  have p0002 := @gId (.classEq (.cv x) (.cv a))
  have p0003 := @gSneqd (.classEq (.cv x) (.cv a)) (.cv x) (.cv a) p0002
  have p0004 :=
    @gBreq1d (.classEq (.cv x) (.cv a)) (synCsn (.cv x)) (synCsn (.cv a))
      (synCsn (.cv y)) (.cv g) p0003
  have p0005 := @gId (.classEq (.cv y) (.cv b))
  have p0006 := @gSneqd (.classEq (.cv y) (.cv b)) (.cv y) (.cv b) p0005
  have p0007 :=
    @gBreq2d (.classEq (.cv y) (.cv b)) (synCsn (.cv y)) (synCsn (.cv b))
      (synCsn (.cv a)) (.cv g) p0006
  have p0008 :=
    @gEqid (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
  have p0009 :=
    @gBrab (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))) x y (.cv a) (.cv b)
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0000 p0001 p0004 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hndownexndv`. -/
@[expose]
noncomputable def gHndownexndv (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (synCvv)) :=
  by
  have dv_cache_0001 : g ≠ x := by exact (show g ≠ x from (by exact dv_g_x))
  have dv_cache_0002 : g ≠ y := by
    clear dv_cache_0001
    exact (show g ≠ y from (by exact dv_g_y))
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gEnpw1lem1 x y g dv_cache_0001 dv_cache_0002 dv_cache_0003
  exact p0000


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part069`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hndownmpteqdv`. -/
@[expose]
noncomputable def gHndownmpteqdv (x : Var) (y : Var) (z : Var) (D : Class) (g : Var)
    (E : Class) (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (_dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv) (dv_E_z : z ∉ E.fv) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_g_z : g ≠ z) (dv_x_y : x ≠ y) (_dv_x_z : x ≠ z)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (.classEq (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
          (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ D.fv ∪
        ({ g } : Finset Var) ∪
      E.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_g : a ≠ g := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_not_E : a ∉ E.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_b_ne_z : b ≠ z := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_g : b ≠ g := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_not_E : b ∉ E.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : a ≠ x := by exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0002 : a ≠ y := by
    clear dv_cache_0001
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0003 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0004 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0005 : g ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show g ≠ x from (by exact dv_g_x))
  have dv_cache_0006 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show g ≠ y from (by exact dv_g_y))
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCuni (synCfv (.cv g) (synCsn (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_a, (Ne.symm dv_g_z), or_false,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0011 : z ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_z, not_false_eq_true])
  have dv_cache_0012 : g ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show g ≠ z from (by exact dv_g_z))
  have dv_cache_0013 :
    a ∉ ((synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_ne_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0014 :
    b ∉ ((synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0015 :
    a ∉ ((synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_D, fresh_a_ne_z,
          fresh_a_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 :
    b ∉ ((synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_D, fresh_b_ne_z,
          fresh_b_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((synWf1o (.cv g) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_D, fresh_a_not_E, fresh_a_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0018 : b ∉ ((synWf1o (.cv g) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_D, fresh_b_not_E, fresh_b_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0019 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    (Nominal.biimpRefl (synWbr (.cv a)
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b)))
  have p0001 :=
    @gA1i
      (synWb (synWbr (.cv a)
          (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
        (.classMem (synCop (.cv a) (.cv b))
          (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) p0000
  have p0002 :=
    @gBicomd (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (.cv a)
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0001
  have p0003 :=
    @gHndownbrndv x y g a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @gA1i
      (synWb (synWbr (.cv a)
          (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) p0003
  have p0005 :=
    @gSimpr (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
  have p0006 :=
    @gSimpl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
  have p0008 := @gBreldm (synCsn (.cv a)) (synCsn (.cv b)) (.cv g)
  have p0009 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (.classMem (synCsn (.cv a)) (synCdm (.cv g))) p0005 p0008
  have p0011 := @gF1odm (synCpw1 D) (synCpw1 E) (.cv g)
  have p0012 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (.classEq (synCdm (.cv g)) (synCpw1 D)) p0006 p0011
  have p0013 :=
    @gEleqtrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synCsn (.cv a)) (synCdm (.cv g)) (synCpw1 D) p0009 p0012
  have p0014 := @gSnelpw1 (.cv a) D
  have p0015 :=
    @gBiimpi (.classMem (synCsn (.cv a)) (synCpw1 D)) (.classMem (.cv a) D) p0014
  have p0016 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (.classMem (synCsn (.cv a)) (synCpw1 D)) (.classMem (.cv a) D) p0013 p0015
  have p0017 :=
    @gJca
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D) p0006 p0016
  have p0018 :=
    @gSimpl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D)
  have p0019 := @gF1ofn (synCpw1 D) (synCpw1 E) (.cv g)
  have p0020 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (synWfn (.cv g) (synCpw1 D)) p0018
      p0019
  have p0021 :=
    @gSimpr (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D)
  have p0023 :=
    @gSylibr (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classMem (.cv a) D) (.classMem (synCsn (.cv a)) (synCpw1 D)) p0021 p0014
  have p0024 :=
    @gJca (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWfn (.cv g) (synCpw1 D)) (.classMem (synCsn (.cv a)) (synCpw1 D)) p0020
      p0023
  have p0025 := @gFnbrfvb (synCpw1 D) (synCsn (.cv a)) (synCsn (.cv b)) (.cv g)
  have p0026 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWa (synWfn (.cv g) (synCpw1 D)) (.classMem (synCsn (.cv a)) (synCpw1 D)))
      (synWb (.classEq (synCfv (.cv g) (synCsn (.cv a))) (synCsn (.cv b)))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      p0024 p0025
  have p0027 :=
    @gBicomd (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classEq (synCfv (.cv g) (synCsn (.cv a))) (synCsn (.cv b)))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))) p0026
  have p0029 := @gF1of (synCpw1 D) (synCpw1 E) (.cv g)
  have p0030 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E)) p0018 p0029
  have p0034 :=
    @gJca (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWf (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCsn (.cv a)) (synCpw1 D)) p0030 p0023
  have p0035 := @gFfvelrn (synCpw1 D) (synCpw1 E) (synCsn (.cv a)) (.cv g)
  have p0036 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWa (synWf (.cv g) (synCpw1 D) (synCpw1 E))
        (.classMem (synCsn (.cv a)) (synCpw1 D)))
      (.classMem (synCfv (.cv g) (synCsn (.cv a))) (synCpw1 E)) p0034 p0035
  have p0037 := @gPw1argclcl E (synCfv (.cv g) (synCsn (.cv a)))
  have p0038 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classMem (synCfv (.cv g) (synCsn (.cv a))) (synCpw1 E))
      (synWa (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv a)))) E)
        (.classEq (synCfv (.cv g) (synCsn (.cv a)))
          (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a)))))))
      p0036 p0037
  have p0039 :=
    @gSimpr (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv a)))) E)
      (.classEq (synCfv (.cv g) (synCsn (.cv a)))
        (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a))))))
  have p0040 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWa (.classMem (synCuni (synCfv (.cv g) (synCsn (.cv a)))) E)
        (.classEq (synCfv (.cv g) (synCsn (.cv a)))
          (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a)))))))
      (.classEq (synCfv (.cv g) (synCsn (.cv a)))
        (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a))))))
      p0038 p0039
  have p0041 :=
    @gEqeq1d (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synCfv (.cv g) (synCsn (.cv a)))
      (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a))))) (synCsn (.cv b)) p0040
  have p0042 := @gFvex (synCsn (.cv a)) (.cv g)
  have p0043 := @gUniex (synCfv (.cv g) (synCsn (.cv a))) p0042
  have p0044 := @gSneqb (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b) p0043
  have p0045 :=
    @gA1i
      (synWb (.classEq (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a)))))
          (synCsn (.cv b))) (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b)))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D)) p0044
  have p0046 :=
    @gBitrd (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classEq (synCfv (.cv g) (synCsn (.cv a))) (synCsn (.cv b)))
      (.classEq (synCsn (synCuni (synCfv (.cv g) (synCsn (.cv a))))) (synCsn (.cv b)))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b)) p0041 p0045
  have p0047 :=
    @gBitrd (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (.classEq (synCfv (.cv g) (synCsn (.cv a))) (synCsn (.cv b)))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b)) p0027 p0046
  have p0049 := @gId (.classEq (.cv z) (.cv a))
  have p0050 := @gSneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0049
  have p0051 :=
    @gFveq2d (.classEq (.cv z) (.cv a)) (synCsn (.cv z)) (synCsn (.cv a)) (.cv g) p0050
  have p0052 :=
    @gUnieqd (.classEq (.cv z) (.cv a)) (synCfv (.cv g) (synCsn (.cv z)))
      (synCfv (.cv g) (synCsn (.cv a))) p0051
  have p0053 := @gEqid (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
  have p0056 :=
    @gFvmpt z (.cv a) (synCuni (synCfv (.cv g) (synCsn (.cv z))))
      (synCuni (synCfv (.cv g) (synCsn (.cv a)))) D
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0052 p0053 p0043
  have p0057 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classMem (.cv a) D)
      (.classEq (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
        (synCuni (synCfv (.cv g) (synCsn (.cv a)))))
      p0021 p0056
  have p0058 :=
    @gEqeq1d (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
      (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b) p0057
  have p0059 :=
    @gBicomd (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classEq (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
        (.cv b))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b)) p0058
  have p0061 := @gPw1descentf1odv z D g E dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0062 := @gF1ofn D E (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
  have p0063 :=
    @gSyl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf1o (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D E)
      (synWfn (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D) p0061
      p0062
  have p0064 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWfn (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D) p0018
      p0063
  have p0066 :=
    @gJca (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWfn (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D)
      (.classMem (.cv a) D) p0064 p0021
  have p0067 :=
    @gFnbrfvb D (.cv a) (.cv b)
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
  have p0068 :=
    @gSyl (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWa (synWfn (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D)
        (.classMem (.cv a) D))
      (synWb (.classEq
          (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
          (.cv b))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      p0066 p0067
  have p0069 :=
    @gBitrd (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b))
      (.classEq (synCfv (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv a))
        (.cv b))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0059 p0068
  have p0070 :=
    @gBitrd (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (.classEq (synCuni (synCfv (.cv g) (synCsn (.cv a)))) (.cv b))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0047 p0069
  have p0071 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWb (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      p0017 p0070
  have p0072 :=
    @gBiimpd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0071
  have p0073 :=
    @gMpd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0005 p0072
  have p0074 :=
    @gEx (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0073
  have p0075 :=
    @gSimpr (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
  have p0076 :=
    @gSimpl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
  have p0078 :=
    @gBreldm (.cv a) (.cv b)
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
  have p0079 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      (.classMem (.cv a)
        (synCdm (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))))
      p0075 p0078
  have p0082 := @gF1odm D E (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
  have p0083 :=
    @gSyl (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWf1o (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) D E)
      (.classEq (synCdm (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))) D)
      p0061 p0082
  have p0084 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (.classEq (synCdm (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))) D)
      p0076 p0083
  have p0085 :=
    @gEleqtrd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (.cv a) (synCdm (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))) D
      p0079 p0084
  have p0086 :=
    @gJca
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D) p0076 p0085
  have p0140 :=
    @gSyl
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) (.classMem (.cv a) D))
      (synWb (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      p0086 p0070
  have p0141 :=
    @gBiimprd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0140
  have p0142 :=
    @gMpd
      (synWa (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
        (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))) p0075 p0141
  have p0143 :=
    @gEx (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b))) p0142
  have p0144 :=
    @gImpbid (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0074 p0143
  have p0145 :=
    @gBitrd (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (synWbr (.cv a)
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
      (synWbr (synCsn (.cv a)) (.cv g) (synCsn (.cv b)))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0004 p0144
  have p0146 :=
    @gBitrd (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (synWbr (.cv a)
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      p0002 p0145
  have p0147 :=
    (Nominal.biimpRefl
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b)))
  have p0148 :=
    @gA1i
      (synWb (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
          (.cv b)) (.classMem (synCop (.cv a) (.cv b))
          (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) p0147
  have p0149 :=
    @gBitrd (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (.classMem (synCop (.cv a) (.cv b))
        (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (synWbr (.cv a) (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) (.cv b))
      (.classMem (synCop (.cv a) (.cv b))
        (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))))
      p0146 p0148
  have p0150 :=
    @gEqrelrdv (synWf1o (.cv g) (synCpw1 D) (synCpw1 E)) a b
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      p0149
  exact p0150

/-- Checked nominal proof certificate identified upstream as `g_pw1isoexequivndv`. -/
@[expose]
noncomputable def gPw1isoexequivndv (D : Class) (R : Class) (S : Class) (f : Var)
    (g : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_g : g ∉ D.fv) (dv_E_f : f ∉ E.fv)
    (dv_E_g : g ∉ E.fv) (dv_R_f : f ∉ R.fv) (dv_R_g : g ∉ R.fv) (dv_S_f : f ∉ S.fv)
    (dv_S_g : g ∉ S.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (synWb (synWex f (synWiso (.cv f) R S D E)) (synWex g
          (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E)))) :=
  by
  let proofSupport : Finset Var :=
    D.fv ∪ R.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ ({ g } : Finset Var) ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_x : g ≠ x := Ne.symm fresh_x_ne_g
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_z_ne_g : z ≠ g := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_z : g ≠ z := Ne.symm fresh_z_ne_g
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : g ∉ ((synCsi (.cv f))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_f_g), not_false_eq_true])
  have dv_cache_0002 :
    g ∉
      ((synWiso (synCsi (.cv f)) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, dv_D_g, dv_E_g, (Ne.symm dv_f_g), dv_R_g, dv_S_g,
          or_false, not_false_eq_true])
  have dv_cache_0003 :
    f ∉
      ((synWex g (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_D_f, dv_E_f, dv_f_g, dv_R_f, dv_S_f,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0005 : z ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_E, not_false_eq_true])
  have dv_cache_0006 : g ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show g ≠ z from (by exact fresh_g_ne_z))
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0009 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0010 : y ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_E, not_false_eq_true])
  have dv_cache_0011 : g ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0012 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0016 :
    f ∉ ((synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, dv_f_g, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 :
    f ∉
      ((synWiso (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) R S
          D E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_f, dv_E_f, fresh_f_ne_x, fresh_f_ne_y, dv_f_g,
          dv_R_f, dv_S_f, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((synWex f (synWiso (.cv f) R S D E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_g, dv_E_g, (Ne.symm dv_f_g), dv_R_g, dv_S_g,
          or_false, and_false, not_false_eq_true])
  have p0000 := @gPw1raiseisomdv D R S f E
  have p0001 := @gVex f
  have p0002 := @gSiex (.cv f) p0001
  have p0003 :=
    @gIsoeq1 (synCpw1 D) (synCpw1 E) (synCsi R) (synCsi S) (synCsi (.cv f)) (.cv g)
  have p0004 :=
    @gSpcev (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWiso (synCsi (.cv f)) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E)) g
      (synCsi (.cv f)) dv_cache_0001 dv_cache_0002 p0002 p0003
  have p0005 :=
    @gSyl (synWiso (.cv f) R S D E)
      (synWiso (synCsi (.cv f)) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWex g (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E)))
      p0000 p0004
  have p0006 :=
    @gExlimiv (synWiso (.cv f) R S D E)
      (synWex g (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))) f
      dv_cache_0003 p0005
  have p0007 := @gPw1descentisomdv z D R S g E dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 := @gIsof1o (synCpw1 D) (synCpw1 E) (synCsi R) (synCsi S) (.cv g)
  have p0009 :=
    @gHndownmpteqdv x y z D g E dv_cache_0007 dv_cache_0008 dv_cache_0004 dv_cache_0009
      dv_cache_0010 dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0006 dv_cache_0013
      dv_cache_0014 dv_cache_0015
  have p0010 :=
    @gSyl (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWf1o (.cv g) (synCpw1 D) (synCpw1 E))
      (.classEq (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))))
      p0008 p0009
  have p0011 :=
    @gIsoeq1 D E R S (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z)))))
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
  have p0012 :=
    @gSyl (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (.classEq (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))))
      (synWb (synWiso (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) R
          S D E)
        (synWiso (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) R S D E))
      p0010 p0011
  have p0013 :=
    @gBiimprd (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWiso (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) R S D E)
      (synWiso (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) R S D E)
      p0012
  have p0014 :=
    @gMpd (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWiso (synCmpt z D (synCuni (synCfv (.cv g) (synCsn (.cv z))))) R S D E)
      (synWiso (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) R S D E)
      p0007 p0013
  have p0015 := @gHndownexndv x y g dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0016 :=
    @gIsoeq1 D E R S
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv f)
  have p0017 :=
    @gSpcev (synWiso (.cv f) R S D E)
      (synWiso (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) R S D E)
      f (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      dv_cache_0016 dv_cache_0017 p0015 p0016
  have p0018 :=
    @gSyl (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWiso (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) R S D E)
      (synWex f (synWiso (.cv f) R S D E)) p0014 p0017
  have p0019 :=
    @gExlimiv (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E))
      (synWex f (synWiso (.cv f) R S D E)) g dv_cache_0018 p0018
  have p0020 :=
    @gImpbii (synWex f (synWiso (.cv f) R S D E))
      (synWex g (synWiso (.cv g) (synCsi R) (synCsi S) (synCpw1 D) (synCpw1 E)))
      p0006 p0019
  exact p0020


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part070`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwnisodirectisobndv`. -/
@[expose]
noncomputable def gHwnisodirectisobndv (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))) :=
  by
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : h ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
  have dv_cache_0003 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show h ≠ u from (by exact dv_h_u))
  have dv_cache_0004 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ v from (by exact dv_h_v))
  have p0000 := @gHwnisohwisob v u A dv_cache_0001
  have p0001 :=
    @gA1i
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv v))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0000
  have p0002 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0003 :=
    @gA1i
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv v))) (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0002
  have p0004 :=
    @g_pm3_2 (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0005 :=
    @gImpbid (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0003 p0004
  have p0006 :=
    @gBitrd (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0001 p0005
  have p0007 := @gBrhwisoany v u A h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0008 :=
    @gA1i
      (synWb (synWbr (.cv u) (synChwiso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
          (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0007
  have p0009 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
  have p0010 :=
    @gA1i
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0009
  have p0011 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0012 := @gHwcnraw u A
  have p0013 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A)) p0011 p0012
  have p0014 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0015 := @gHwcnraw v A
  have p0016 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcodes A)) p0014 p0015
  have p0017 :=
    @gJca (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)) p0013
      p0016
  have p0018 :=
    @g_pm3_2
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
  have p0019 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (.imp (synWex h
          (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
          (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))))
      p0017 p0018
  have p0020 :=
    @gImpbid (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0010 p0019
  have p0021 :=
    @gBitrd (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0008 p0020
  have p0022 :=
    @gBitrd (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0006 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_hwnisodirectisobclndv`. -/
@[expose]
noncomputable def gHwnisodirectisobclndv (A : Class) (B : Class) (C : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (synWbr B (synChwniso A) C) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({ h } : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_h : v ≠ h := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_v : h ≠ v := Ne.symm fresh_v_ne_h
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_u_ne_h : u ≠ h := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_u : h ≠ u := Ne.symm fresh_u_ne_h
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : h ∉ ((Wff.classEq (.cv v) C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_v, dv_C_h, or_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((Wff.classEq (.cv u) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, dv_B_h, or_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
  have dv_cache_0004 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0005 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0006 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact fresh_u_ne_v))
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
  have dv_cache_0008 :
    u ∉
      ((Wff.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWb (synWbr B (synChwniso A) (.cv v)) (synWex h
              (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A,
          fresh_u_ne_v, fresh_u_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0010 :
    v ∉
      ((Wff.imp (.classMem B (synCvv))
          (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
            (synWb (synWbr B (synChwniso A) C) (synWex h
                (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
                  (synCfv (synC2nd) B) (synCfv (synC2nd) C))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A,
          fresh_v_not_C, fresh_v_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gSimpl (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0001 := @gElex B (synChwcn A)
  have p0002 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synChwcn A)) (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpr (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0004 := @gElex C (synChwcn A)
  have p0005 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A)) (.classMem C (synCvv)) p0003 p0004
  have p0006 := @gBiid (.classMem B (synCvv))
  have p0007 :=
    @gA1i (synWb (.classMem B (synCvv)) (.classMem B (synCvv))) (.classEq (.cv v) C)
      p0006
  have p0008 := @gBiid (.classMem B (synChwcn A))
  have p0009 :=
    @gA1i (synWb (.classMem B (synChwcn A)) (.classMem B (synChwcn A)))
      (.classEq (.cv v) C) p0008
  have p0010 := @gId (.classEq (.cv v) C)
  have p0011 := @gEleq1d (.classEq (.cv v) C) (.cv v) C (synChwcn A) p0010
  have p0012 :=
    @gAnbi12d (.classEq (.cv v) C) (.classMem B (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem C (synChwcn A)) p0009 p0011
  have p0014 := @gBreq2d (.classEq (.cv v) C) (.cv v) C B (synChwniso A) p0010
  have p0016 := @gFveq2d (.classEq (.cv v) C) (.cv v) C (synC1st) p0010
  have p0017 :=
    @gIsoeq3 (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) B)
      (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C) (.cv h)
  have p0018 :=
    @gSyl (.classEq (.cv v) C)
      (.classEq (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C))
      (synWb (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0016 p0017
  have p0020 := @gFveq2d (.classEq (.cv v) C) (.cv v) C (synC2nd) p0010
  have p0021 :=
    @gIsoeq5 (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C)
      (synCfv (synC1st) B) (synCfv (synC1st) C) (.cv h)
  have p0022 :=
    @gSyl (.classEq (.cv v) C)
      (.classEq (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C))
      (synWb (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      p0020 p0021
  have p0023 :=
    @gBitrd (.classEq (.cv v) C)
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
      p0018 p0022
  have p0024 :=
    @gExbidv (.classEq (.cv v) C)
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
        (synCfv (synC2nd) B) (synCfv (synC2nd) C))
      h dv_cache_0001 p0023
  have p0025 :=
    @gBibi12d (.classEq (.cv v) C) (synWbr B (synChwniso A) (.cv v))
      (synWbr B (synChwniso A) C)
      (synWex h (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
          (synCfv (synC2nd) B) (synCfv (synC2nd) C)))
      p0014 p0024
  have p0026 :=
    @gImbi12d (.classEq (.cv v) C)
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWb (synWbr B (synChwniso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))))
      (synWb (synWbr B (synChwniso A) C) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))))
      p0012 p0025
  have p0027 :=
    @gImbi12d (.classEq (.cv v) C) (.classMem B (synCvv)) (.classMem B (synCvv))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWb (synWbr B (synChwniso A) (.cv v)) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (synWbr B (synChwniso A) C) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C)))))
      p0007 p0026
  have p0028 := @gId (.classEq (.cv u) B)
  have p0029 := @gEleq1d (.classEq (.cv u) B) (.cv u) B (synChwcn A) p0028
  have p0030 := @gBiid (.classMem (.cv v) (synChwcn A))
  have p0031 :=
    @gA1i (synWb (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classEq (.cv u) B) p0030
  have p0032 :=
    @gAnbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv v) (synChwcn A)) p0029 p0031
  have p0034 := @gBreq1d (.classEq (.cv u) B) (.cv u) B (.cv v) (synChwniso A) p0028
  have p0036 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC1st) p0028
  have p0037 :=
    @gIsoeq2 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) B)
      (.cv h)
  have p0038 :=
    @gSyl (.classEq (.cv u) B)
      (.classEq (synCfv (synC1st) (.cv u)) (synCfv (synC1st) B))
      (synWb (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0036 p0037
  have p0040 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC2nd) p0028
  have p0041 :=
    @gIsoeq4 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC2nd) B) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v)) (.cv h)
  have p0042 :=
    @gSyl (.classEq (.cv u) B)
      (.classEq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B))
      (synWb (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0040 p0041
  have p0043 :=
    @gBitrd (.classEq (.cv u) B)
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      p0038 p0042
  have p0044 :=
    @gExbidv (.classEq (.cv u) B)
      (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))
      h dv_cache_0002 p0043
  have p0045 :=
    @gBibi12d (.classEq (.cv u) B) (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr B (synChwniso A) (.cv v))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))
      p0034 p0044
  have p0046 :=
    @gImbi12d (.classEq (.cv u) B)
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWb (synWbr B (synChwniso A) (.cv v)) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))))
      p0032 p0045
  have p0047 :=
    @gHwnisodirectisobndv v u A h dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0048 :=
    @gVtoclg
      (.imp (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWb (synWbr B (synChwniso A) (.cv v)) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v))))))
      u B (synCvv) dv_cache_0007 dv_cache_0008 p0046 p0047
  have p0049 :=
    @gVtoclg
      (.imp (.classMem B (synCvv))
        (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWb (synWbr B (synChwniso A) (.cv v)) (synWex h
              (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) (.cv v))
                (synCfv (synC2nd) B) (synCfv (synC2nd) (.cv v)))))))
      (.imp (.classMem B (synCvv))
        (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
          (synWb (synWbr B (synChwniso A) C) (synWex h
              (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
                (synCfv (synC2nd) B) (synCfv (synC2nd) C))))))
      v C (synCvv) dv_cache_0009 dv_cache_0010 p0027 p0048
  have p0050 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synCvv))
      (.imp (.classMem B (synCvv))
        (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
          (synWb (synWbr B (synChwniso A) C) (synWex h
              (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
                (synCfv (synC2nd) B) (synCfv (synC2nd) C))))))
      p0005 p0049
  have p0051 :=
    @gMpd (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synCvv))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (synWbr B (synChwniso A) C) (synWex h
            (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
              (synCfv (synC2nd) B) (synCfv (synC2nd) C)))))
      p0002 p0050
  have p0052 :=
    @gPm243i (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWb (synWbr B (synChwniso A) C) (synWex h
          (synWiso (.cv h) (synCfv (synC1st) B) (synCfv (synC1st) C)
            (synCfv (synC2nd) B) (synCfv (synC2nd) C))))
      p0051
  exact p0052


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part071`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemapkernelndv`. -/
@[expose]
noncomputable def gHnsicodemapkernelndv (A : Class) (r : Var) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_q_r : q ≠ r) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))
        (synWb (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
          (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
            (synCfv (synChnsicodemap A) (.cv r))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ r } : Finset Var) ∪ ({ q } : Finset Var)
  let g : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_ne_r : g ≠ r := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_q : g ≠ q := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_ne_r : f ≠ r := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_q : f ≠ q := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_f : g ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_g : f ≠ g := Ne.symm fresh_g_ne_f
  have dv_cache_0001 : q ∉ ((synChwcn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_q,
          not_false_eq_true])
  have dv_cache_0002 : r ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_r,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_q,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_r,
          not_false_eq_true])
  have dv_cache_0005 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact dv_q_r))
  have dv_cache_0006 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0007 : f ∉ ((synCuni (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_f_ne_q,
          not_false_eq_true])
  have dv_cache_0008 : f ∉ ((synCuni (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_f_ne_r,
          not_false_eq_true])
  have dv_cache_0009 : f ∉ ((synCfv (synC2nd) (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : g ∉ ((synCfv (synC2nd) (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : f ∉ ((synCfv (synC2nd) (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : g ∉ ((synCfv (synC2nd) (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : f ∉ ((synCfv (synC1st) (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 : g ∉ ((synCfv (synC1st) (synCuni (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : f ∉ ((synCfv (synC1st) (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : g ∉ ((synCfv (synC1st) (synCuni (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0017 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have dv_cache_0018 : g ∉ ((synCpw1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_g_not_A,
          not_false_eq_true])
  have dv_cache_0019 : g ∉ ((synCfv (synChnsicodemap A) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_q, fresh_g_not_A, or_false, not_false_eq_true])
  have dv_cache_0020 : g ∉ ((synCfv (synChnsicodemap A) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_r, fresh_g_not_A, or_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ (A).fv :=
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
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0022 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0023 :
    g ∉
      ((synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
          (.classMem (.cv r) (synCpw1 (synChwcn A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_q, fresh_g_not_A, fresh_g_ne_r, or_false,
          not_false_eq_true])
  have p0000 :=
    @gPw1typedbrndv (synChwcn A) (synChwniso A) r q dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
  have p0002 := @gHnwpw1argcl (synChwcn A) q
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synWa (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0001 p0002
  have p0004 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0005 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWa (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synChwcn A)) p0003 p0004
  have p0006 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
  have p0007 := @gHnwpw1argcl (synChwcn A) r
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      p0006 p0007
  have p0009 :=
    @gSimpl (.classMem (synCuni (.cv r)) (synChwcn A))
      (.classEq (.cv r) (synCsn (synCuni (.cv r))))
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWa (.classMem (synCuni (.cv r)) (synChwcn A))
        (.classEq (.cv r) (synCsn (synCuni (.cv r)))))
      (.classMem (synCuni (.cv r)) (synChwcn A)) p0008 p0009
  have p0011 :=
    @gJca
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (synCuni (.cv q)) (synChwcn A))
      (.classMem (synCuni (.cv r)) (synChwcn A)) p0005 p0010
  have p0012 :=
    @gHwnisodirectisobclndv A (synCuni (.cv q)) (synCuni (.cv r)) f dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWa (.classMem (synCuni (.cv q)) (synChwcn A))
        (.classMem (synCuni (.cv r)) (synChwcn A)))
      (synWb (synWbr (synCuni (.cv q)) (synChwniso A) (synCuni (.cv r))) (synWex f
          (synWiso (.cv f) (synCfv (synC1st) (synCuni (.cv q)))
            (synCfv (synC1st) (synCuni (.cv r))) (synCfv (synC2nd) (synCuni (.cv q)))
            (synCfv (synC2nd) (synCuni (.cv r))))))
      p0011 p0012
  have p0014 :=
    @gPw1isoexequivndv (synCfv (synC2nd) (synCuni (.cv q)))
      (synCfv (synC1st) (synCuni (.cv q))) (synCfv (synC1st) (synCuni (.cv r))) f g
      (synCfv (synC2nd) (synCuni (.cv r))) dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0015 :=
    @gA1i
      (synWb (synWex f (synWiso (.cv f) (synCfv (synC1st) (synCuni (.cv q)))
            (synCfv (synC1st) (synCuni (.cv r))) (synCfv (synC2nd) (synCuni (.cv q)))
            (synCfv (synC2nd) (synCuni (.cv r))))) (synWex g
          (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
            (synCsi (synCfv (synC1st) (synCuni (.cv r))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      p0014
  have p0016 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWbr (synCuni (.cv q)) (synChwniso A) (synCuni (.cv r)))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (synCuni (.cv q)))
          (synCfv (synC1st) (synCuni (.cv r))) (synCfv (synC2nd) (synCuni (.cv q)))
          (synCfv (synC2nd) (synCuni (.cv r)))))
      (synWex g (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0013 p0015
  have p0017 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
      (synWbr (synCuni (.cv q)) (synChwniso A) (synCuni (.cv r)))
      (synWex g (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0000 p0016
  have p0018 := @gHnsicodemapfndv A
  have p0019 :=
    @gA1i (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      p0018
  have p0021 :=
    @gJca
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (.classMem (.cv q) (synCpw1 (synChwcn A))) p0019 p0001
  have p0022 :=
    @gFfvelrn (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (.cv q)
      (synChnsicodemap A)
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (.classMem (.cv q) (synCpw1 (synChwcn A))))
      (.classMem (synCfv (synChnsicodemap A) (.cv q)) (synChwcn (synCpw1 A))) p0021
      p0022
  have p0027 :=
    @gJca
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (.classMem (.cv r) (synCpw1 (synChwcn A))) p0019 p0006
  have p0028 :=
    @gFfvelrn (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (.cv r)
      (synChnsicodemap A)
  have p0029 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (synCfv (synChnsicodemap A) (.cv r)) (synChwcn (synCpw1 A))) p0027
      p0028
  have p0030 :=
    @gJca
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (synCfv (synChnsicodemap A) (.cv q)) (synChwcn (synCpw1 A)))
      (.classMem (synCfv (synChnsicodemap A) (.cv r)) (synChwcn (synCpw1 A))) p0023
      p0029
  have p0031 :=
    @gHwnisodirectisobclndv (synCpw1 A) (synCfv (synChnsicodemap A) (.cv q))
      (synCfv (synChnsicodemap A) (.cv r)) g dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0032 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWa (.classMem (synCfv (synChnsicodemap A) (.cv q)) (synChwcn (synCpw1 A)))
        (.classMem (synCfv (synChnsicodemap A) (.cv r)) (synChwcn (synCpw1 A))))
      (synWb (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
          (synCfv (synChnsicodemap A) (.cv r))) (synWex g
          (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
            (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
            (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
            (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))))
      p0030 p0031
  have p0034 := @gHnsicodemapvalndv A q dv_cache_0021
  have p0035 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (.cv q))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
      p0001 p0034
  have p0036 :=
    @gFveq2d
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synChnsicodemap A) (.cv q))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      (synC1st) p0035
  have p0037 := @gFvex (synCuni (.cv q)) (synC1st)
  have p0038 := @gSiex (synCfv (synC1st) (synCuni (.cv q))) p0037
  have p0039 := @gFvex (synCuni (.cv q)) (synC2nd)
  have p0040 := @gPw1ex (synCfv (synC2nd) (synCuni (.cv q))) p0039
  have p0041 :=
    @gOpfv1st (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))) p0038 p0040
  have p0042 :=
    @gA1i
      (.classEq (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
        (synCsi (synCfv (synC1st) (synCuni (.cv q)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      p0041
  have p0043 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
      (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
      (synCsi (synCfv (synC1st) (synCuni (.cv q)))) p0036 p0042
  have p0044 :=
    @gIsoeq2 (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))
      (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
      (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
      (synCsi (synCfv (synC1st) (synCuni (.cv q)))) (.cv g)
  have p0045 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
        (synCsi (synCfv (synC1st) (synCuni (.cv q)))))
      (synWb (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
        (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))))
      p0043 p0044
  have p0047 := @gHnsicodemapvalndv A r dv_cache_0022
  have p0048 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classMem (.cv r) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (.cv r))
        (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0006 p0047
  have p0049 :=
    @gFveq2d
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synChnsicodemap A) (.cv r))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      (synC1st) p0048
  have p0050 := @gFvex (synCuni (.cv r)) (synC1st)
  have p0051 := @gSiex (synCfv (synC1st) (synCuni (.cv r))) p0050
  have p0052 := @gFvex (synCuni (.cv r)) (synC2nd)
  have p0053 := @gPw1ex (synCfv (synC2nd) (synCuni (.cv r))) p0052
  have p0054 :=
    @gOpfv1st (synCsi (synCfv (synC1st) (synCuni (.cv r))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))) p0051 p0053
  have p0055 :=
    @gA1i
      (.classEq (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      p0054
  have p0056 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
      (synCfv (synC1st) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (synCsi (synCfv (synC1st) (synCuni (.cv r)))) p0049 p0055
  have p0057 :=
    @gIsoeq3 (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))
      (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
      (synCsi (synCfv (synC1st) (synCuni (.cv r)))) (.cv g)
  have p0058 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
        (synCsi (synCfv (synC1st) (synCuni (.cv r)))))
      (synWb (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
        (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))))
      p0056 p0057
  have p0059 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      p0045 p0058
  have p0063 :=
    @gFveq2d
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synChnsicodemap A) (.cv q))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      (synC2nd) p0035
  have p0068 :=
    @gOpfv2nd (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))) p0038 p0040
  have p0069 :=
    @gA1i
      (.classEq (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      p0068
  have p0070 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))) p0063 p0069
  have p0071 :=
    @gIsoeq4 (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
      (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCsi (synCfv (synC1st) (synCuni (.cv r)))) (.cv g)
  have p0072 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q)))))
      (synWb (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
        (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))))
      p0070 p0071
  have p0073 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      p0059 p0072
  have p0077 :=
    @gFveq2d
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synChnsicodemap A) (.cv r))
      (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      (synC2nd) p0048
  have p0082 :=
    @gOpfv2nd (synCsi (synCfv (synC1st) (synCuni (.cv r))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))) p0051 p0053
  have p0083 :=
    @gA1i
      (.classEq (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
            (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      p0082
  have p0084 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))
      (synCfv (synC2nd) (synCop (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))) p0077 p0083
  have p0085 :=
    @gIsoeq5 (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))
      (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))
      (synCsi (synCfv (synC1st) (synCuni (.cv q))))
      (synCsi (synCfv (synC1st) (synCuni (.cv r)))) (.cv g)
  have p0086 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (.classEq (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      (synWb (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
        (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0084 p0085
  have p0087 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      p0073 p0086
  have p0088 :=
    @gExbidv
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r))))
      (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
        (synCsi (synCfv (synC1st) (synCuni (.cv r))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
        (synCpw1 (synCfv (synC2nd) (synCuni (.cv r)))))
      g dv_cache_0023 p0087
  have p0089 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (.cv r)))
      (synWex g (synWiso (.cv g) (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC1st) (synCfv (synChnsicodemap A) (.cv r)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv q)))
          (synCfv (synC2nd) (synCfv (synChnsicodemap A) (.cv r)))))
      (synWex g (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0032 p0088
  have p0090 :=
    @gBicomd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (.cv r)))
      (synWex g (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      p0089
  have p0091 :=
    @gBitrd
      (synWa (.classMem (.cv q) (synCpw1 (synChwcn A)))
        (.classMem (.cv r) (synCpw1 (synChwcn A))))
      (synWbr (.cv q) (synCsi (synChwniso A)) (.cv r))
      (synWex g (synWiso (.cv g) (synCsi (synCfv (synC1st) (synCuni (.cv q))))
          (synCsi (synCfv (synC1st) (synCuni (.cv r))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv q))))
          (synCpw1 (synCfv (synC2nd) (synCuni (.cv r))))))
      (synWbr (synCfv (synChnsicodemap A) (.cv q)) (synChwniso (synCpw1 A))
        (synCfv (synChnsicodemap A) (.cv r)))
      p0017 p0090
  exact p0091


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part072`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_siorreflectndv`. -/
@[expose]
noncomputable def gSiorreflectndv (D : Class) (R : Class)
    (hyp_siorreflectndv_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_siorreflectndv_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCsi R) (synCwe) (synCpw1 D)) (synWbr R (synCstrict) D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synWbr (synCsi R) (synCwe) (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0005 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWbr (synCsi R) (synCwe) (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synWbr (synCsi R) (synCwe) (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @gA1i (.classMem R (synCvv)) (synWbr (synCsi R) (synCwe) (synCpw1 D))
      hyp_siorreflectndv_1
  have p0001 :=
    @gA1i (.classMem D (synCvv)) (synWbr (synCsi R) (synCwe) (synCpw1 D))
      hyp_siorreflectndv_2
  have p0002 :=
    @gSimpl (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
  have p0003 := @gWppweref (synCpw1 D) (synCsi R)
  have p0004 :=
    @gSyl (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D))
      (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCref) (synCpw1 D)) p0002 p0003
  have p0005 :=
    @gSimpr (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
  have p0006 := @gSnelpw1 (.cv x) D
  have p0007 :=
    @gBiimpri (.classMem (synCsn (.cv x)) (synCpw1 D)) (.classMem (.cv x) D) p0006
  have p0008 :=
    @gSyl (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0005 p0007
  have p0009 :=
    @gRefd (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D))
      (synCpw1 D) (synCsi R) (synCsn (.cv x)) p0004 p0008
  have p0010 := @gVex x
  have p0012 := @gBrsnsi (.cv x) (.cv x) R p0010 p0010
  have p0013 :=
    @gBiimpi (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv x)))
      (synWbr (.cv x) R (.cv x)) p0012
  have p0014 :=
    @gSyl (synWa (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D))
      (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv x)))
      (synWbr (.cv x) R (.cv x)) p0009 p0013
  have p0015 :=
    @gRefrd (synWbr (synCsi R) (synCwe) (synCpw1 D)) x D R (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000 p0001 p0014
  have p0018 :=
    @gSimp1 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
  have p0019 := @gWppwepo (synCpw1 D) (synCsi R)
  have p0020 := @gPorta (synCpw1 D) (synCsi R)
  have p0021 :=
    @gSimp2bi (synWbr (synCsi R) (synCpartial) (synCpw1 D))
      (synWbr (synCsi R) (synCref) (synCpw1 D))
      (synWbr (synCsi R) (synCtrans) (synCpw1 D))
      (synWbr (synCsi R) (synCantisym) (synCpw1 D)) p0020
  have p0022 :=
    @gSyl (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCpartial) (synCpw1 D))
      (synWbr (synCsi R) (synCtrans) (synCpw1 D)) p0019 p0021
  have p0023 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCtrans) (synCpw1 D)) p0018 p0022
  have p0024 :=
    @gSimp2 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
  have p0025 := @gSimp1 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0026 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (.classMem (.cv x) D) p0024 p0025
  have p0029 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0026 p0007
  have p0031 := @gSimp2 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0032 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (.classMem (.cv y) D) p0024 p0031
  have p0033 := @gSnelpw1 (.cv y) D
  have p0034 :=
    @gBiimpri (.classMem (synCsn (.cv y)) (synCpw1 D)) (.classMem (.cv y) D) p0033
  have p0035 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (.classMem (.cv y) D) (.classMem (synCsn (.cv y)) (synCpw1 D)) p0032 p0034
  have p0037 := @gSimp3 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0038 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (.classMem (.cv z) D) p0024 p0037
  have p0039 := @gSnelpw1 (.cv z) D
  have p0040 :=
    @gBiimpri (.classMem (synCsn (.cv z)) (synCpw1 D)) (.classMem (.cv z) D) p0039
  have p0041 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (.classMem (.cv z) D) (.classMem (synCsn (.cv z)) (synCpw1 D)) p0038 p0040
  have p0042 :=
    @gSimp3 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
  have p0043 := @gSimpl (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))
  have p0044 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv x) R (.cv y)) p0042 p0043
  have p0046 := @gVex y
  have p0047 := @gBrsnsi (.cv x) (.cv y) R p0010 p0046
  have p0048 :=
    @gBiimpri (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0047
  have p0049 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synWbr (.cv x) R (.cv y))
      (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y))) p0044 p0048
  have p0051 := @gSimpr (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))
  have p0052 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv y) R (.cv z)) p0042 p0051
  have p0054 := @gVex z
  have p0055 := @gBrsnsi (.cv y) (.cv z) R p0046 p0054
  have p0056 :=
    @gBiimpri (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv z)))
      (synWbr (.cv y) R (.cv z)) p0055
  have p0057 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synWbr (.cv y) R (.cv z))
      (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv z))) p0052 p0056
  have p0058 :=
    @gTrd
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synCpw1 D) (synCsi R) (synCsn (.cv x)) (synCsn (.cv y)) (synCsn (.cv z)) p0023
      p0029 p0035 p0041 p0049 p0057
  have p0061 := @gBrsnsi (.cv x) (.cv z) R p0010 p0054
  have p0062 :=
    @gBiimpi (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv z)))
      (synWbr (.cv x) R (.cv z)) p0061
  have p0063 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z))))
      (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv z)))
      (synWbr (.cv x) R (.cv z)) p0058 p0062
  have p0064 :=
    @gTrrd (synWbr (synCsi R) (synCwe) (synCpw1 D)) x y z D R (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007
      dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      p0000 p0001 p0063
  have p0067 :=
    @gSimp1 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
  have p0068 := @gWppweantisym (synCpw1 D) (synCsi R)
  have p0069 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCantisym) (synCpw1 D)) p0067 p0068
  have p0070 :=
    @gSimp2 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
  have p0071 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0072 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0070
      p0071
  have p0073 := @gSnelpw1 (.cv x) D
  have p0074 :=
    @gBiimpri (.classMem (synCsn (.cv x)) (synCpw1 D)) (.classMem (.cv x) D) p0073
  have p0075 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0072 p0074
  have p0076 :=
    @gSimp2 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
  have p0077 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0078 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0076
      p0077
  have p0079 := @gSnelpw1 (.cv y) D
  have p0080 :=
    @gBiimpri (.classMem (synCsn (.cv y)) (synCpw1 D)) (.classMem (.cv y) D) p0079
  have p0081 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (.classMem (.cv y) D) (.classMem (synCsn (.cv y)) (synCpw1 D)) p0078 p0080
  have p0082 :=
    @gSimp3 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
  have p0083 := @gSimpl (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))
  have p0084 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv x) R (.cv y)) p0082 p0083
  have p0085 := @gVex x
  have p0086 := @gVex y
  have p0087 := @gBrsnsi (.cv x) (.cv y) R p0085 p0086
  have p0088 :=
    @gBiimpri (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0087
  have p0089 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWbr (.cv x) R (.cv y))
      (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y))) p0084 p0088
  have p0090 :=
    @gSimp3 (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
  have p0091 := @gSimpr (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))
  have p0092 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv y) R (.cv x)) p0090 p0091
  have p0095 := @gBrsnsi (.cv y) (.cv x) R p0046 p0010
  have p0096 :=
    @gBiimpri (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv x)))
      (synWbr (.cv y) R (.cv x)) p0095
  have p0097 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synWbr (.cv y) R (.cv x))
      (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv x))) p0092 p0096
  have p0098 :=
    @gAntid
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (synCpw1 D) (synCsi R) (synCsn (.cv x)) (synCsn (.cv y)) p0069 p0075 p0081 p0089
      p0097
  have p0099 := @gVex x
  have p0100 := @gSneqr (.cv x) (.cv y) p0099
  have p0101 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
        (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))))
      (.classEq (synCsn (.cv x)) (synCsn (.cv y))) (.classEq (.cv x) (.cv y)) p0098
      p0100
  have p0102_e02_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D))
          (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWbr synCop synCun synCnin synWnan synCcompl
          synWrex synWex synCphi synCsi synCopab synCwe synCin synCstrict
          synCfound synCpw1
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0101
  have p0102 :=
    @gAntird (synWbr (synCsi R) (synCwe) (synCpw1 D)) x y D R (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008
      dv_cache_0010 p0000 p0001 p0102_e02_recanon
  have p0103 :=
    @gN3jca (synWbr (synCsi R) (synCwe) (synCpw1 D)) (synWbr R (synCref) D)
      (synWbr R (synCtrans) D) (synWbr R (synCantisym) D) p0015 p0064 p0102
  have p0104 := @gPorta D R
  have p0105 :=
    @gBiimpri (synWbr R (synCpartial) D)
      (synW3a (synWbr R (synCref) D) (synWbr R (synCtrans) D) (synWbr R (synCantisym) D))
      p0104
  have p0106 :=
    @gSyl (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synW3a (synWbr R (synCref) D) (synWbr R (synCtrans) D) (synWbr R (synCantisym) D))
      (synWbr R (synCpartial) D) p0103 p0105
  have p0109 :=
    @gSimp1 (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
      (.classMem (.cv y) D)
  have p0110 := @gWppweconnex (synCpw1 D) (synCsi R)
  have p0111 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCconnex) (synCpw1 D)) p0109 p0110
  have p0112 :=
    @gSimp2 (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
      (.classMem (.cv y) D)
  have p0115 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0112 p0007
  have p0116 :=
    @gSimp3 (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
      (.classMem (.cv y) D)
  have p0119 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (.classMem (.cv y) D) (.classMem (synCsn (.cv y)) (synCpw1 D)) p0116 p0034
  have p0120 :=
    @gConnexd
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (synCpw1 D) (synCsi R) (synCsn (.cv x)) (synCsn (.cv y)) p0111 p0115 p0119
  have p0127 :=
    @gOrbi12i (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv x)))
      (synWbr (.cv y) R (.cv x)) p0047 p0095
  have p0128 :=
    @gBiimpi
      (synWo (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
        (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv x))))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) p0127
  have p0129 :=
    @gSyl
      (synW3a (synWbr (synCsi R) (synCwe) (synCpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (synWo (synWbr (synCsn (.cv x)) (synCsi R) (synCsn (.cv y)))
        (synWbr (synCsn (.cv y)) (synCsi R) (synCsn (.cv x))))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))) p0120 p0128
  have p0130 :=
    @gConnexrd (synWbr (synCsi R) (synCwe) (synCpw1 D)) x y D R (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008
      dv_cache_0010 p0000 p0001 p0129
  have p0131 :=
    @gJca (synWbr (synCsi R) (synCwe) (synCpw1 D)) (synWbr R (synCpartial) D)
      (synWbr R (synCconnex) D) p0106 p0130
  have p0132 := @gSopc D R
  have p0133 :=
    @gBiimpri (synWbr R (synCstrict) D)
      (synWa (synWbr R (synCpartial) D) (synWbr R (synCconnex) D)) p0132
  have p0134 :=
    @gSyl (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (synWbr R (synCpartial) D) (synWbr R (synCconnex) D))
      (synWbr R (synCstrict) D) p0131 p0133
  exact p0134


end NFChoice.DirectNominalPrf.WPPReplay

end
