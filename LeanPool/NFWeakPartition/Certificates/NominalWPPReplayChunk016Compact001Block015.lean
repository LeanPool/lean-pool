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

@[expose]
noncomputable def g_hnsicodemapexgndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnsicodemap A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnsicodemap A))
  have p0001 :=
    @g_a1i
      (.classEq (syn_chnsicodemap A) (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))))
      (.classMem A (syn_cvv)) p0000
  have p0002 := @g_hnsicodeliftfnexndv
  have p0003 :=
    @g_a1i (.classMem (syn_chnsicodeliftfn) (syn_cvv)) (.classMem A (syn_cvv)) p0002
  have p0004 := @g_hwcnexg A
  have p0005 := @g_pw1exg (syn_chwcn A) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chnsicodeliftfn) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_resexg (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chnsicodeliftfn) (syn_cvv))
        (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)))
      (.classMem (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv))
      p0007 p0008
  have p0010 :=
    @g_eqeltrd (.classMem A (syn_cvv)) (syn_chnsicodemap A)
      (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv) p0001 p0009
  exact p0010

@[expose]
noncomputable def g_hnsicodemapvalndv (A : Class) (q : Var) (_dv_A_q : q ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
          (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) :=
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
  have dv_cache_0001 : u ∉ ((syn_cuni (.cv q))).fv := by
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
      ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q))
            (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
              (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))).fv :=
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
      ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
          (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
            (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
              (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_chnsicodemap A))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_chnsicodemap A)
      (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
        (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0001
  have p0003 := @g_fvres (.cv q) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q))
      (syn_cfv (syn_chnsicodeliftfn) (.cv q)) p0002 p0003
  have p0005 := @g_hnwpw1argcl (syn_chwcn A) q
  have p0006 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0008 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0009 := @g_elex (syn_cuni (.cv q)) (syn_chwcn A)
  have p0010 := @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0011 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q))
      (syn_chwcn A) p0010
  have p0014 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c1st)
      p0010
  have p0016 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) (syn_c2nd)
      p0010
  have p0017 :=
    @g_opeq12d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0014 p0016
  have p0018 :=
    @g_eqeq12d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      p0010 p0017
  have p0019 :=
    @g_imbi12d (.classEq (.cv u) (syn_cuni (.cv q))) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0011 p0018
  have p0020 := @g_hwcnpair u A
  have p0021 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv u)
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) (.classEq (syn_cuni (.cv q))
          (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
            (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      u (syn_cuni (.cv q)) (syn_cvv) dv_cache_0001 dv_cache_0002 p0019 p0020
  have p0022 :=
    @g_mpcom (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0009 p0021
  have p0023 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0008 p0022
  have p0024 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_cuni (.cv q))
      (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      p0023
  have p0025 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q)
      (syn_csn (syn_cuni (.cv q)))
      (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0006 p0024
  have p0026 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q)
      (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_chnsicodeliftfn) p0025
  have p0038 :=
    @g_xpeq12d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0016 p0016
  have p0039 :=
    @g_sseq12d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      p0014 p0038
  have p0040 :=
    @g_imbi12d (.classEq (.cv u) (syn_cuni (.cv q))) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0011 p0039
  have p0041 := @g_hwcnsupp u A
  have p0042 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
            (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      u (syn_cuni (.cv q)) (syn_cvv) dv_cache_0001 dv_cache_0003 p0040 p0041
  have p0043 :=
    @g_mpcom (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0009 p0042
  have p0044 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0008 p0043
  have p0045 := @g_ssv (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
  have p0047 :=
    @g_pm3_2i (syn_wss (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv))
      (syn_wss (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv)) p0045 p0045
  have p0048 :=
    @g_xpss12 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv)
      (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cvv)
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @g_a1i
      (syn_wss (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) (syn_cxp (syn_cvv) (syn_cvv)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0049
  have p0051 :=
    @g_sstrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      (syn_cxp (syn_cvv) (syn_cvv)) p0044 p0050
  have p0052 := @g_fvex (syn_cuni (.cv q)) (syn_c1st)
  have p0053 := @g_fvex (syn_cuni (.cv q)) (syn_c2nd)
  have p0054 :=
    @g_hnsicodeliftfnvalgndv (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0052 p0053
  have p0055 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_wss (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cxp (syn_cvv) (syn_cvv)))
      (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn
            (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
              (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      p0051 p0054
  have p0056 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_chnsicodeliftfn) (.cv q))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
            (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0026 p0055
  have p0057 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (.cv q))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      p0004 p0056
  exact p0057

@[expose]
noncomputable def g_hnsicodemapfndv (A : Class) :
    Nominal.NPrf
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) :=
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
  have dv_cache_0002 : u ∉ ((syn_cuni (.cv q))).fv :=
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
      ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
          (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
            (syn_chwcn (syn_cpw1 A))))).fv :=
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
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
  have dv_cache_0005 : q ∉ ((syn_chwcn (syn_cpw1 A))).fv :=
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
  have dv_cache_0006 : q ∉ ((syn_chnsicodemap A)).fv :=
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
  have p0000 := @g_hnsicodeliftfnfnndv
  have p0001 := @g_ssv (syn_cpw1 (syn_chwcn A))
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodeliftfn) (syn_cvv))
      (syn_wss (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0000 p0001
  have p0003 := @g_fnssres (syn_cvv) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_chnsicodemap A))
  have p0006 :=
    @g_fneq1i (syn_cpw1 (syn_chwcn A)) (syn_chnsicodemap A)
      (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)))
      (syn_wfn (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A)))
        (syn_cpw1 (syn_chwcn A)))
      p0004 p0006
  have p0017 :=
    @g_fveq1i (.cv q) (syn_chnsicodemap A)
      (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) p0005
  have p0018 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
        (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0017
  have p0019 := @g_fvres (.cv q) (syn_cpw1 (syn_chwcn A)) (syn_chnsicodeliftfn)
  have p0020 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_cres (syn_chnsicodeliftfn) (syn_cpw1 (syn_chwcn A))) (.cv q))
      (syn_cfv (syn_chnsicodeliftfn) (.cv q)) p0018 p0019
  have p0021 := @g_hnwpw1argcl (syn_chwcn A) q
  have p0022 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0021
  have p0023 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q)
      (syn_csn (syn_cuni (.cv q))) (syn_chnsicodeliftfn) p0022
  have p0025 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0021
  have p0026 := @g_elex (syn_cuni (.cv q)) (syn_chwcn A)
  have p0027 := @g_id (.classEq (.cv u) (syn_cuni (.cv q)))
  have p0028 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q))
      (syn_chwcn A) p0027
  have p0030 :=
    @g_sneqd (.classEq (.cv u) (syn_cuni (.cv q))) (.cv u) (syn_cuni (.cv q)) p0027
  have p0031 :=
    @g_fveq2d (.classEq (.cv u) (syn_cuni (.cv q))) (syn_csn (.cv u))
      (syn_csn (syn_cuni (.cv q))) (syn_chnsicodeliftfn) p0030
  have p0032 :=
    @g_eleq1d (.classEq (.cv u) (syn_cuni (.cv q)))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u)))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
      (syn_chwcn (syn_cpw1 A)) p0031
  have p0033 :=
    @g_imbi12d (.classEq (.cv u) (syn_cuni (.cv q))) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
        (syn_chwcn (syn_cpw1 A)))
      p0028 p0032
  have p0034 := @g_hwcnpair u A
  have p0035 :=
    @g_sneqd (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0034
  have p0036 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_csn (.cv u))
      (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chnsicodeliftfn) p0035
  have p0037 := @g_hwcnsupp u A
  have p0038 := @g_ssv (syn_cfv (syn_c2nd) (.cv u))
  have p0040 :=
    @g_pm3_2i (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) p0038 p0038
  have p0041 :=
    @g_xpss12 (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cvv)
  have p0042 := Nominal.mp p0040 p0041
  have p0043 :=
    @g_a1i
      (syn_wss (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cxp (syn_cvv) (syn_cvv)))
      (.classMem (.cv u) (syn_chwcn A)) p0042
  have p0044 :=
    @g_sstrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cxp (syn_cvv) (syn_cvv)) p0037 p0043
  have p0045 := @g_fvex (.cv u) (syn_c1st)
  have p0046 := @g_fvex (.cv u) (syn_c2nd)
  have p0047 :=
    @g_hnsicodeliftfnvalgndv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      p0045 p0046
  have p0048 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cvv) (syn_cvv)))
      (.classEq (syn_cfv (syn_chnsicodeliftfn)
          (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      p0044 p0047
  have p0049 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u)))
      (syn_cfv (syn_chnsicodeliftfn)
        (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      p0036 p0048
  have p0050 := @g_hnsicodeliftcodeclndv u A dv_cache_0001
  have p0051 :=
    @g_eqeltrd (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u)))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chwcn (syn_cpw1 A)) p0049 p0050
  have p0052 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))))
      (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
          (syn_chwcn (syn_cpw1 A))))
      u (syn_cuni (.cv q)) (syn_cvv) dv_cache_0002 dv_cache_0003 p0033 p0051
  have p0053 :=
    @g_mpcom (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
        (syn_chwcn (syn_cpw1 A)))
      p0026 p0052
  have p0054 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classMem (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
        (syn_chwcn (syn_cpw1 A)))
      p0025 p0053
  have p0055 :=
    @g_eqeltrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_chnsicodeliftfn) (.cv q))
      (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cuni (.cv q))))
      (syn_chwcn (syn_cpw1 A)) p0023 p0054
  have p0056 :=
    @g_eqeltrd (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodeliftfn) (.cv q))
      (syn_chwcn (syn_cpw1 A)) p0020 p0055
  have p0057 :=
    @g_rgen (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))) q
      (syn_cpw1 (syn_chwcn A)) p0056
  have p0058 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)))
      (syn_wral q (syn_cpw1 (syn_chwcn A))
        (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))))
      p0007 p0057
  have p0059 :=
    @g_fnfvrnss q (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_chnsicodemap A)
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0060 := Nominal.mp p0058 p0059
  have p0061 :=
    @g_pm3_2i (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)))
      (syn_wss (syn_crn (syn_chnsicodemap A)) (syn_chwcn (syn_cpw1 A))) p0007 p0060
  have p0062 :=
    (Nominal.biimpRefl
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))))
  have p0063 :=
    @g_mpbir
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (syn_wfn (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)))
        (syn_wss (syn_crn (syn_chnsicodemap A)) (syn_chwcn (syn_cpw1 A))))
      p0061 p0062
  exact p0063

@[expose]
noncomputable def g_pw1typedbrndv (D : Class) (R : Class) (q : Var) (p : Var)
    (_dv_D_p : p ∉ D.fv) (_dv_D_q : q ∉ D.fv) (_dv_R_p : p ∉ R.fv) (_dv_R_q : q ∉ R.fv)
    (_dv_p_q : p ≠ q) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
        (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q))
          (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))))) :=
  by
  have p0000 := @g_simpl (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0001 := @g_hnwpw1argcl D p
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (.classMem (.cv p) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) D)
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0002 p0003
  have p0005 := @g_simpr (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0006 := @g_hnwpw1argcl D q
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0005 p0006
  have p0008 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) D)
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0007 p0008
  have p0010 :=
    @g_breq12d (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (.cv q) (syn_csn (syn_cuni (.cv q)))
      (syn_csi R) p0004 p0009
  have p0011 := @g_vex p
  have p0012 := @g_uniex (.cv p) p0011
  have p0013 := @g_vex q
  have p0014 := @g_uniex (.cv q) p0013
  have p0015 := @g_brsnsi (syn_cuni (.cv p)) (syn_cuni (.cv q)) R p0012 p0014
  have p0016 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi R) (syn_csn (syn_cuni (.cv q))))
        (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))) p0015
  have p0017 :=
    @g_bitrd (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (syn_wbr (.cv p) (syn_csi R) (.cv q))
      (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi R) (syn_csn (syn_cuni (.cv q))))
      (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))) p0010 p0016
  exact p0017

@[expose]
noncomputable def g_pw1argclcl (D : Class) (Q : Class) :
    Nominal.NPrf
      (.imp (.classMem Q (syn_cpw1 D))
        (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))))) :=
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
    z ∉ ((syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))))).fv :=
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
  have p0000 := @g_elpw1 z Q D dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem Q (syn_cpw1 D)) (syn_wrex z D (.classEq Q (syn_csn (.cv z))))
      p0000
  have p0002 := @g_simpr (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))
  have p0003 :=
    @g_unieqd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) Q
      (syn_csn (.cv z)) p0002
  have p0004 := @g_vex z
  have p0005 := @g_unisn (.cv z) p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cuni (syn_csn (.cv z))) (.cv z))
      (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) p0005
  have p0007 :=
    @g_eqtrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q)
      (syn_cuni (syn_csn (.cv z))) (.cv z) p0003 p0006
  have p0008 := @g_simpl (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))
  have p0009 :=
    @g_eqeltrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q)
      (.cv z) D p0007 p0008
  have p0017 :=
    @g_eqcomd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (syn_cuni Q)
      (.cv z) p0007
  have p0018 :=
    @g_sneqd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) (.cv z)
      (syn_cuni Q) p0017
  have p0019 :=
    @g_eqtrd (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z)))) Q
      (syn_csn (.cv z)) (syn_csn (syn_cuni Q)) p0002 p0018
  have p0020 :=
    @g_jca (syn_wa (.classMem (.cv z) D) (.classEq Q (syn_csn (.cv z))))
      (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))) p0009 p0019
  have p0021 :=
    @g_rexlimiva (.classEq Q (syn_csn (.cv z)))
      (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) z D
      dv_cache_0003 p0020
  have p0022 :=
    @g_syl (.classMem Q (syn_cpw1 D)) (syn_wrex z D (.classEq Q (syn_csn (.cv z))))
      (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) p0001 p0021
  exact p0022

@[expose]
noncomputable def g_pw1descentf1odv (x : Var) (D : Class) (g : Var) (E : Class)
    (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_g_x : g ≠ x) :
    Nominal.NPrf
      (.imp (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wf1o (syn_cmpt x D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) D E)) :=
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
  have dv_cache_0005 : y ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))).fv :=
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
    x ∉ ((syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
  have p0000 := @g_eqid (syn_cmpt x D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))
  have p0001 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)
  have p0002 := @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0003 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0001 p0002
  have p0004 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D)
  have p0005 := @g_snelpw1 (.cv x) D
  have p0006 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0004 p0005
  have p0007 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0003 p0006
  have p0008 := @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv x)) (.cv g)
  have p0009 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D))
      (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 D)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) p0007 p0008
  have p0010 := @g_pw1argclcl E (syn_cfv (.cv g) (syn_csn (.cv x)))
  have p0011 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E)
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x)))
        (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
  have p0012 :=
    @g_syl (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E))
      (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E)
        (.classEq (syn_cfv (.cv g) (syn_csn (.cv x)))
          (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))))
      (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) p0010 p0011
  have p0013 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv x) D))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E))
      (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E) p0009 p0012
  have p0014 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)
  have p0015 := @g_f1ocnv (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0016 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0014 p0015
  have p0017 := @g_f1of (syn_cpw1 E) (syn_cpw1 D) (syn_ccnv (.cv g))
  have p0018 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E))
      (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D))
      (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0016 p0017
  have p0019 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E)
  have p0020 := @g_snelpw1 (.cv y) E
  have p0021 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E))
      (.classMem (.cv y) E) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E))
      (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0018 p0021
  have p0023 := @g_ffvelrn (syn_cpw1 E) (syn_cpw1 D) (syn_csn (.cv y)) (syn_ccnv (.cv g))
  have p0024 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E))
      (syn_wa (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D))
        (.classMem (syn_csn (.cv y)) (syn_cpw1 E)))
      (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) p0022 p0023
  have p0025 := @g_pw1argclcl D (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
  have p0026 :=
    @g_simpl (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D)
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
        (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
  have p0027 :=
    @g_syl (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D)
        (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
          (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))))
      (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) p0025 p0026
  have p0028 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv y) E))
      (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D))
      (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D) p0024 p0027
  have p0029 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0032 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D))
      (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0015 p0017
  have p0033 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D)) p0029 p0032
  have p0034 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E))
  have p0035 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0036 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv y) E) p0034
      p0035
  have p0038 :=
    @g_sylibr
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (.cv y) E) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0036 p0020
  have p0039 :=
    @g_jca
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0033 p0038
  have p0041 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wa (syn_wf (syn_ccnv (.cv g)) (syn_cpw1 E) (syn_cpw1 D))
        (.classMem (syn_csn (.cv y)) (syn_cpw1 E)))
      (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D)) p0039 p0023
  have p0043 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D)
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
        (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
  have p0044 :=
    @g_syl (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) D)
        (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
          (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
        (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
      p0025 p0043
  have p0045 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_cpw1 D))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
        (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
      p0041 p0044
  have p0046 :=
    @g_eqeq1d
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))
      (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))
      (syn_csn (.cv x)) p0045
  have p0047 := @g_fvex (syn_csn (.cv y)) (syn_ccnv (.cv g))
  have p0048 := @g_uniex (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) p0047
  have p0049 :=
    @g_sneqb (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x) p0048
  have p0050 :=
    @g_a1i
      (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))
          (syn_csn (.cv x)))
        (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0049
  have p0051 :=
    @g_bitrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (.classEq (syn_csn (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))
        (syn_csn (.cv x)))
      (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)) p0046
      p0050
  have p0052 := @g_eqcom (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x)
  have p0053 :=
    @g_a1i
      (syn_wb (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x))
        (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0052
  have p0054 :=
    @g_bitrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (.classEq (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))) (.cv x))
      (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) p0051
      p0053
  have p0055 :=
    @g_bicomd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))) p0054
  have p0058 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) E)
  have p0059 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (.classMem (.cv x) D) p0034
      p0058
  have p0061 :=
    @g_sylibr
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0059 p0005
  have p0067 :=
    @g_n_3jca
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 E)) p0029 p0061 p0038
  have p0068 :=
    @g_f1ocnvfvb (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv g)
  have p0069 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_w3a (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (syn_csn (.cv y)) (syn_cpw1 E)))
      (syn_wb (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y)))
        (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))))
      p0067 p0068
  have p0070 :=
    @g_bicomd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x))) p0069
  have p0071 :=
    @g_bitrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))
      (.classEq (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y))) p0055 p0070
  have p0074 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0029 p0002
  have p0080 :=
    @g_jca
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0074 p0061
  have p0082 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 D)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E)) p0080 p0008
  have p0084 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E)
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x)))
        (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
  have p0085 :=
    @g_syl (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E))
      (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) E)
        (.classEq (syn_cfv (.cv g) (syn_csn (.cv x)))
          (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x)))
        (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
      p0010 p0084
  have p0086 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_cpw1 E))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x)))
        (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
      p0082 p0085
  have p0087 :=
    @g_eqeq1d
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (syn_cfv (.cv g) (syn_csn (.cv x)))
      (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) (syn_csn (.cv y)) p0086
  have p0088 := @g_fvex (syn_csn (.cv x)) (.cv g)
  have p0089 := @g_uniex (syn_cfv (.cv g) (syn_csn (.cv x))) p0088
  have p0090 := @g_sneqb (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y) p0089
  have p0091 :=
    @g_a1i
      (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))))
          (syn_csn (.cv y))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0090
  have p0092 :=
    @g_bitrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) (syn_csn (.cv y)))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)) p0087 p0091
  have p0093 := @g_eqcom (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y)
  have p0094 :=
    @g_a1i
      (syn_wb (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y))
        (.classEq (.cv y) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      p0093
  have p0095 :=
    @g_bitrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x)))) (.cv y))
      (.classEq (.cv y) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) p0092 p0094
  have p0096 :=
    @g_bitrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)))
      (.classEq (.cv x) (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y)))))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.classEq (.cv y) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) p0071 p0095
  have p0097 :=
    @g_f1o2d (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) x y D E
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))
      (syn_cuni (syn_cfv (syn_ccnv (.cv g)) (syn_csn (.cv y))))
      (syn_cmpt x D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv x))))) dv_cache_0001
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

@[expose]
noncomputable def g_pw1typedbrcldv (D : Class) (P : Class) (Q : Class) (R : Class)
    (hyp_pw1typedbrcldv_1 : Nominal.NPrf (.classMem P (syn_cvv)))
    (hyp_pw1typedbrcldv_2 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D)))
        (syn_wb (syn_wbr P (syn_csi R) Q) (syn_wbr (syn_cuni P) R (syn_cuni Q)))) :=
  by
  have p0000 := @g_simpl (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))
  have p0001 := @g_pw1argclcl D P
  have p0002 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D)))
      (.classMem P (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni P) D) (.classEq P (syn_csn (syn_cuni P)))) p0000 p0001
  have p0003 := @g_simpr (.classMem (syn_cuni P) D) (.classEq P (syn_csn (syn_cuni P)))
  have p0004 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni P) D) (.classEq P (syn_csn (syn_cuni P))))
      (.classEq P (syn_csn (syn_cuni P))) p0002 p0003
  have p0005 := @g_simpr (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))
  have p0006 := @g_pw1argclcl D Q
  have p0007 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D)))
      (.classMem Q (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))) p0005 p0006
  have p0008 := @g_simpr (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0009 :=
    @g_syl (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni Q) D) (.classEq Q (syn_csn (syn_cuni Q))))
      (.classEq Q (syn_csn (syn_cuni Q))) p0007 p0008
  have p0010 :=
    @g_breq12d (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) P
      (syn_csn (syn_cuni P)) Q (syn_csn (syn_cuni Q)) (syn_csi R) p0004 p0009
  have p0011 := @g_uniex P hyp_pw1typedbrcldv_1
  have p0012 := @g_uniex Q hyp_pw1typedbrcldv_2
  have p0013 := @g_brsnsi (syn_cuni P) (syn_cuni Q) R p0011 p0012
  have p0014 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni P)) (syn_csi R) (syn_csn (syn_cuni Q)))
        (syn_wbr (syn_cuni P) R (syn_cuni Q)))
      (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D))) p0013
  have p0015 :=
    @g_bitrd (syn_wa (.classMem P (syn_cpw1 D)) (.classMem Q (syn_cpw1 D)))
      (syn_wbr P (syn_csi R) Q)
      (syn_wbr (syn_csn (syn_cuni P)) (syn_csi R) (syn_csn (syn_cuni Q)))
      (syn_wbr (syn_cuni P) R (syn_cuni Q)) p0010 p0014
  exact p0015

@[expose]
noncomputable def g_pw1descentisomdv (z : Var) (D : Class) (R : Class) (S : Class)
    (g : Var) (E : Class) (dv_D_z : z ∉ D.fv) (dv_E_z : z ∉ E.fv) (dv_g_z : g ≠ z) :
    Nominal.NPrf
      (.imp (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)) :=
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
  have dv_cache_0005 : z ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))).fv :=
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
  have dv_cache_0007 : z ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))).fv :=
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
    a ∉ ((syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
    b ∉ ((syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
    a ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv :=
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
    b ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv :=
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
  have p0000 := @g_isof1o (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (.cv g)
  have p0001 := @g_pw1descentf1odv z D g E dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E) p0000
      p0001
  have p0003 := @g_vex a
  have p0004 := @g_vex b
  have p0005 := @g_brsnsi (.cv a) (.cv b) R p0003 p0004
  have p0006 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b)))
        (syn_wbr (.cv a) R (.cv b)))
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      p0005
  have p0007 :=
    @g_bicomd
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b)))
      (syn_wbr (.cv a) R (.cv b)) p0006
  have p0008 :=
    @g_simpl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0009 :=
    @g_simpr (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D))
  have p0010 := @g_simpl (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0011 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv a) D) p0009
      p0010
  have p0012 := @g_snelpw1 (.cv a) D
  have p0013 :=
    @g_sylibr
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0011 p0012
  have p0015 := @g_simpr (.classMem (.cv a) D) (.classMem (.cv b) D)
  have p0016 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)) (.classMem (.cv b) D) p0009
      p0015
  have p0017 := @g_snelpw1 (.cv b) D
  have p0018 :=
    @g_sylibr
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv b) D) (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0016 p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0013 p0018
  have p0020 :=
    @g_jca
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
        (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))
      p0008 p0019
  have p0021 :=
    @g_isorel (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_csi R)
      (syn_csi S) (.cv g)
  have p0022 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 D))
          (.classMem (syn_csn (.cv b)) (syn_cpw1 D))))
      (syn_wb (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b)))
        (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S)
          (syn_cfv (.cv g) (syn_csn (.cv b)))))
      p0020 p0021
  have p0023 :=
    @g_bitrd
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wbr (.cv a) R (.cv b))
      (syn_wbr (syn_csn (.cv a)) (syn_csi R) (syn_csn (.cv b)))
      (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S)
        (syn_cfv (.cv g) (syn_csn (.cv b))))
      p0007 p0022
  have p0026 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0008 p0000
  have p0027 := @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0028 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0026 p0027
  have p0034 :=
    @g_jca
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0028 p0013
  have p0035 := @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (.cv g)
  have p0036 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classMem (syn_csn (.cv a)) (syn_cpw1 D)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) p0034 p0035
  have p0047 :=
    @g_jca
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 D)) p0028 p0018
  have p0048 := @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv b)) (.cv g)
  have p0049 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classMem (syn_csn (.cv b)) (syn_cpw1 D)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv b))) (syn_cpw1 E)) p0047 p0048
  have p0050 :=
    @g_jca
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv b))) (syn_cpw1 E)) p0036 p0049
  have p0051 := @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0052 := @g_fvex (syn_csn (.cv b)) (.cv g)
  have p0053 :=
    @g_pw1typedbrcldv E (syn_cfv (.cv g) (syn_csn (.cv a)))
      (syn_cfv (.cv g) (syn_csn (.cv b))) S p0051 p0052
  have p0054 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wa (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E))
        (.classMem (syn_cfv (.cv g) (syn_csn (.cv b))) (syn_cpw1 E)))
      (syn_wb (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S)
          (syn_cfv (.cv g) (syn_csn (.cv b))))
        (syn_wbr (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) S
          (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))))
      p0050 p0053
  have p0055 :=
    @g_bitrd
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wbr (.cv a) R (.cv b))
      (syn_wbr (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csi S)
        (syn_cfv (.cv g) (syn_csn (.cv b))))
      (syn_wbr (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) S
        (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))))
      p0023 p0054
  have p0059 := @g_id (.classEq (.cv z) (.cv a))
  have p0060 := @g_sneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0059
  have p0061 :=
    @g_fveq2d (.classEq (.cv z) (.cv a)) (syn_csn (.cv z)) (syn_csn (.cv a)) (.cv g) p0060
  have p0062 :=
    @g_unieqd (.classEq (.cv z) (.cv a)) (syn_cfv (.cv g) (syn_csn (.cv z)))
      (syn_cfv (.cv g) (syn_csn (.cv a))) p0061
  have p0063 := @g_eqid (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0065 := @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0051
  have p0066 :=
    @g_fvmpt z (.cv a) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) D
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0004
      dv_cache_0005 dv_cache_0001 p0062 p0063 p0065
  have p0067 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv a) D)
      (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
        (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))
      p0011 p0066
  have p0068 :=
    @g_eqcomd
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) p0067
  have p0072 := @g_id (.classEq (.cv z) (.cv b))
  have p0073 := @g_sneqd (.classEq (.cv z) (.cv b)) (.cv z) (.cv b) p0072
  have p0074 :=
    @g_fveq2d (.classEq (.cv z) (.cv b)) (syn_csn (.cv z)) (syn_csn (.cv b)) (.cv g) p0073
  have p0075 :=
    @g_unieqd (.classEq (.cv z) (.cv b)) (syn_cfv (.cv g) (syn_csn (.cv z)))
      (syn_cfv (.cv g) (syn_csn (.cv b))) p0074
  have p0078 := @g_uniex (syn_cfv (.cv g) (syn_csn (.cv b))) p0052
  have p0079 :=
    @g_fvmpt z (.cv b) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))) D
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0075 p0063 p0078
  have p0080 :=
    @g_syl
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (.classMem (.cv b) D)
      (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
        (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))))
      p0016 p0079
  have p0081 :=
    @g_eqcomd
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))) p0080
  have p0082 :=
    @g_breq12d
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))
      (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b))))
      (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)) S
      p0068 p0081
  have p0083 :=
    @g_bitrd
      (syn_wa (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wa (.classMem (.cv a) D) (.classMem (.cv b) D)))
      (syn_wbr (.cv a) R (.cv b))
      (syn_wbr (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) S
        (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv b)))))
      (syn_wbr (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S
        (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      p0055 p0082
  have p0084 :=
    @g_ralrimivva (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr
          (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S
          (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))))
      a b D D dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0083
  have p0085 :=
    @g_jca (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E)
      (syn_wral a D (syn_wral b D (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr
              (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a)) S
              (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
                (.cv b))))))
      p0002 p0084
  have p0086 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso a b D E R S
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0012
      dv_cache_0008 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0011
  have p0087 :=
    @g_biimpri
      (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)
      (syn_wa (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E)
        (syn_wral a D (syn_wral b D (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr
                (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
                S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
                  (.cv b)))))))
      p0086
  have p0088 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E)
        (syn_wral a D (syn_wral b D (syn_wb (syn_wbr (.cv a) R (.cv b)) (syn_wbr
                (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
                S (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
                  (.cv b)))))))
      (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)
      p0085 p0087
  exact p0088

@[expose]
noncomputable def g_sifvalimpclndv (C : Class) (D : Class) (E : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf F D E) (.classMem C D))
        (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C)))) :=
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
          (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))))).fv :=
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
  have dv_cache_0003 : c ∉ ((syn_wa (syn_wf F D E) (.classMem C D))).fv :=
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
  have p0000 := @g_simpr (syn_wf F D E) (.classMem C D)
  have p0002 := @g_elex C D
  have p0003 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem C D)) (.classMem C D) (.classMem C (syn_cvv))
      p0000 p0002
  have p0004 := @g_simpr (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)
  have p0005 := @g_eleq1 (.cv c) C D
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (.classEq (.cv c) C) (syn_wb (.classMem (.cv c) D) (.classMem C D)) p0004 p0005
  have p0008 :=
    @g_sneqd (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C)) (.cv c)
      C p0004
  have p0009 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (syn_csn (.cv c)) (syn_csn C) (syn_csi F) p0008
  have p0011 :=
    @g_fveq2d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (.cv c) C F p0004
  have p0012 :=
    @g_sneqd (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (syn_cfv F (.cv c)) (syn_cfv F C) p0011
  have p0013 :=
    @g_eqeq12d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_cfv (syn_csi F) (syn_csn C))
      (syn_csn (syn_cfv F (.cv c))) (syn_csn (syn_cfv F C)) p0009 p0012
  have p0014 :=
    @g_imbi12d (syn_wa (syn_wa (syn_wf F D E) (.classMem C D)) (.classEq (.cv c) C))
      (.classMem (.cv c) D) (.classMem C D)
      (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))
      (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0006 p0013
  have p0015 := @g_simpl (syn_wf F D E) (.classMem C D)
  have p0016 := @g_simpl (syn_wf F D E) (.classMem (.cv c) D)
  have p0017 := @g_ffn D E F
  have p0018 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem (.cv c) D)) (syn_wf F D E) (syn_wfn F D)
      p0016 p0017
  have p0019 := @g_simpr (syn_wf F D E) (.classMem (.cv c) D)
  have p0020 :=
    @g_jca (syn_wa (syn_wf F D E) (.classMem (.cv c) D)) (syn_wfn F D)
      (.classMem (.cv c) D) p0018 p0019
  have p0021 := @g_sifnvalv c D F
  have p0022 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem (.cv c) D))
      (syn_wa (syn_wfn F D) (.classMem (.cv c) D))
      (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))
      p0020 p0021
  have p0023 :=
    @g_ex (syn_wf F D E) (.classMem (.cv c) D)
      (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c))))
      p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wf F D E) (.classMem C D)) (syn_wf F D E)
      (.imp (.classMem (.cv c) D)
        (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))))
      p0015 p0023
  have p0025 :=
    @g_vtocld (syn_wa (syn_wf F D E) (.classMem C D))
      (.imp (.classMem (.cv c) D)
        (.classEq (syn_cfv (syn_csi F) (syn_csn (.cv c))) (syn_csn (syn_cfv F (.cv c)))))
      (.imp (.classMem C D)
        (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))))
      c C (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0003 p0014 p0024
  have p0026 :=
    @g_mpd (syn_wa (syn_wf F D E) (.classMem C D)) (.classMem C D)
      (.classEq (syn_cfv (syn_csi F) (syn_csn C)) (syn_csn (syn_cfv F C))) p0000 p0025
  exact p0026

@[expose]
noncomputable def g_pw1sif1omapndv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wf1o F A B) (syn_wf1o (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  have p0000 := @g_f1of A B F
  have p0001 := @g_sifmap A B F
  have p0002 :=
    @g_syl (syn_wf1o F A B) (syn_wf F A B) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))
      p0000 p0001
  have p0003 := @g_ffn (syn_cpw1 A) (syn_cpw1 B) (syn_csi F)
  have p0004 :=
    @g_syl (syn_wf1o F A B) (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))
      (syn_wfn (syn_csi F) (syn_cpw1 A)) p0002 p0003
  have p0005 := @g_f1ocnv A B F
  have p0006 := @g_f1of B A (syn_ccnv F)
  have p0007 :=
    @g_syl (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) (syn_wf (syn_ccnv F) B A) p0005
      p0006
  have p0008 := @g_sifmap B A (syn_ccnv F)
  have p0009 :=
    @g_syl (syn_wf1o F A B) (syn_wf (syn_ccnv F) B A)
      (syn_wf (syn_csi (syn_ccnv F)) (syn_cpw1 B) (syn_cpw1 A)) p0007 p0008
  have p0010 := @g_ffn (syn_cpw1 B) (syn_cpw1 A) (syn_csi (syn_ccnv F))
  have p0011 :=
    @g_syl (syn_wf1o F A B) (syn_wf (syn_csi (syn_ccnv F)) (syn_cpw1 B) (syn_cpw1 A))
      (syn_wfn (syn_csi (syn_ccnv F)) (syn_cpw1 B)) p0009 p0010
  have p0012 := @g_cnvsi F
  have p0013 := @g_fneq1i (syn_cpw1 B) (syn_ccnv (syn_csi F)) (syn_csi (syn_ccnv F)) p0012
  have p0014 :=
    @g_sylibr (syn_wf1o F A B) (syn_wfn (syn_csi (syn_ccnv F)) (syn_cpw1 B))
      (syn_wfn (syn_ccnv (syn_csi F)) (syn_cpw1 B)) p0011 p0013
  have p0015 :=
    @g_jca (syn_wf1o F A B) (syn_wfn (syn_csi F) (syn_cpw1 A))
      (syn_wfn (syn_ccnv (syn_csi F)) (syn_cpw1 B)) p0004 p0014
  have p0016 := @g_dff1o4 (syn_cpw1 A) (syn_cpw1 B) (syn_csi F)
  have p0017 :=
    @g_sylibr (syn_wf1o F A B)
      (syn_wa (syn_wfn (syn_csi F) (syn_cpw1 A)) (syn_wfn (syn_ccnv (syn_csi F)) (syn_cpw1 B)))
      (syn_wf1o (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) p0015 p0016
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

@[expose]
noncomputable def g_pw1raiseisomdv (D : Class) (R : Class) (S : Class) (f : Var)
    (E : Class) :
    Nominal.NPrf
      (.imp (syn_wiso (.cv f) R S D E)
        (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))) :=
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
  have dv_cache_0006 : q ∉ ((syn_cpw1 D)).fv :=
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
  have dv_cache_0007 : p ∉ ((syn_wiso (.cv f) R S D E)).fv :=
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
  have dv_cache_0008 : q ∉ ((syn_wiso (.cv f) R S D E)).fv :=
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
  have dv_cache_0009 : p ∉ ((syn_cpw1 D)).fv :=
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
  have dv_cache_0010 : p ∉ ((syn_cpw1 E)).fv :=
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
  have dv_cache_0011 : q ∉ ((syn_cpw1 E)).fv :=
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
  have dv_cache_0012 : p ∉ ((syn_csi (.cv f))).fv :=
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
  have dv_cache_0013 : q ∉ ((syn_csi (.cv f))).fv :=
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
  have dv_cache_0014 : p ∉ ((syn_csi R)).fv :=
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
  have dv_cache_0015 : q ∉ ((syn_csi R)).fv :=
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
  have dv_cache_0016 : p ∉ ((syn_csi S)).fv :=
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
  have dv_cache_0017 : q ∉ ((syn_csi S)).fv :=
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
  have p0000 := @g_isof1o D E R S (.cv f)
  have p0001 := @g_pw1sif1omapndv D E (.cv f)
  have p0002 :=
    @g_syl (syn_wiso (.cv f) R S D E) (syn_wf1o (.cv f) D E)
      (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) p0000 p0001
  have p0003 :=
    @g_simpr (syn_wiso (.cv f) R S D E)
      (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0004 :=
    @g_pw1typedbrndv D R q p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0005 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q))
        (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q))))
      p0003 p0004
  have p0006 :=
    @g_simpl (syn_wiso (.cv f) R S D E)
      (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
  have p0008 := @g_simpl (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (.classMem (.cv p) (syn_cpw1 D)) p0003 p0008
  have p0010 := @g_hnwpw1argcl D p
  have p0011 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (.classMem (.cv p) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      p0009 p0010
  have p0012 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) D)
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classMem (syn_cuni (.cv p)) D) p0011 p0012
  have p0015 := @g_simpr (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cpw1 D)) p0003 p0015
  have p0017 := @g_hnwpw1argcl D q
  have p0018 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (.classMem (.cv q) (syn_cpw1 D))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0016 p0017
  have p0019 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) D)
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) D) p0018 p0019
  have p0021 :=
    @g_jca
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (.classMem (syn_cuni (.cv p)) D) (.classMem (syn_cuni (.cv q)) D) p0013 p0020
  have p0022 :=
    @g_jca
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wiso (.cv f) R S D E)
      (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classMem (syn_cuni (.cv q)) D)) p0006
      p0021
  have p0023 := @g_isorel D E (syn_cuni (.cv p)) (syn_cuni (.cv q)) R S (.cv f)
  have p0024 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classMem (syn_cuni (.cv q)) D)))
      (syn_wb (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q)))
        (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q)))))
      p0022 p0023
  have p0025 :=
    @g_bitrd
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wbr (.cv p) (syn_csi R) (.cv q))
      (syn_wbr (syn_cuni (.cv p)) R (syn_cuni (.cv q)))
      (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q))))
      p0005 p0024
  have p0031 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) D)
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0032 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (syn_cuni (.cv p)) D) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0011 p0031
  have p0033 :=
    @g_fveq2d
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csi (.cv f)) p0032
  have p0036 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wiso (.cv f) R S D E) (syn_wf1o (.cv f) D E) p0006 p0000
  have p0037 := @g_f1of D E (.cv f)
  have p0038 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wf1o (.cv f) D E) (syn_wf (.cv f) D E) p0036 p0037
  have p0046 :=
    @g_jca
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv p)) D) p0038 p0013
  have p0047 := @g_sifvalimpclndv (syn_cuni (.cv p)) D E (.cv f)
  have p0048 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv p)) D))
      (.classEq (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv p))))
        (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))))
      p0046 p0047
  have p0049 :=
    @g_eqtrd
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_cfv (syn_csi (.cv f)) (.cv p))
      (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv p))))
      (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) p0033 p0048
  have p0055 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) D)
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0056 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0018 p0055
  have p0057 :=
    @g_fveq2d
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_csi (.cv f)) p0056
  have p0070 :=
    @g_jca
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv q)) D) p0038 p0020
  have p0071 := @g_sifvalimpclndv (syn_cuni (.cv q)) D E (.cv f)
  have p0072 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wa (syn_wf (.cv f) D E) (.classMem (syn_cuni (.cv q)) D))
      (.classEq (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv q))))
        (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q)))))
      p0070 p0071
  have p0073 :=
    @g_eqtrd
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_cfv (syn_csi (.cv f)) (.cv q))
      (syn_cfv (syn_csi (.cv f)) (syn_csn (syn_cuni (.cv q))))
      (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q)))) p0057 p0072
  have p0074 :=
    @g_breq12d
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p))))
      (syn_cfv (syn_csi (.cv f)) (.cv q)) (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q))))
      (syn_csi S) p0049 p0073
  have p0075 := @g_fvex (syn_cuni (.cv p)) (.cv f)
  have p0076 := @g_fvex (syn_cuni (.cv q)) (.cv f)
  have p0077 :=
    @g_brsnsi (syn_cfv (.cv f) (syn_cuni (.cv p))) (syn_cfv (.cv f) (syn_cuni (.cv q))) S
      p0075 p0076
  have p0078 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) (syn_csi S)
          (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q)))))
        (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q)))))
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      p0077
  have p0079 :=
    @g_bitrd
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
        (syn_cfv (syn_csi (.cv f)) (.cv q)))
      (syn_wbr (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv p)))) (syn_csi S)
        (syn_csn (syn_cfv (.cv f) (syn_cuni (.cv q)))))
      (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q))))
      p0074 p0078
  have p0080 :=
    @g_bicomd
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
        (syn_cfv (syn_csi (.cv f)) (.cv q)))
      (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q))))
      p0079
  have p0081 :=
    @g_bitrd
      (syn_wa (syn_wiso (.cv f) R S D E)
        (syn_wa (.classMem (.cv p) (syn_cpw1 D)) (.classMem (.cv q) (syn_cpw1 D))))
      (syn_wbr (.cv p) (syn_csi R) (.cv q))
      (syn_wbr (syn_cfv (.cv f) (syn_cuni (.cv p))) S (syn_cfv (.cv f) (syn_cuni (.cv q))))
      (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
        (syn_cfv (syn_csi (.cv f)) (.cv q)))
      p0025 p0080
  have p0082 :=
    @g_ralrimivva (syn_wiso (.cv f) R S D E)
      (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q))
        (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
          (syn_cfv (syn_csi (.cv f)) (.cv q))))
      p q (syn_cpw1 D) (syn_cpw1 D) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0005 p0081
  have p0083 :=
    @g_jca (syn_wiso (.cv f) R S D E)
      (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wral p (syn_cpw1 D) (syn_wral q (syn_cpw1 D)
          (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q))
            (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
              (syn_cfv (syn_csi (.cv f)) (.cv q))))))
      p0002 p0082
  have p0084 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso p q (syn_cpw1 D)
      (syn_cpw1 E) (syn_csi R) (syn_csi S) (syn_csi (.cv f)) dv_cache_0009 dv_cache_0006
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0005
  have p0085 :=
    @g_biimpri
      (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wa (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) (syn_wral p (syn_cpw1 D)
          (syn_wral q (syn_cpw1 D) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q))
              (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
                (syn_cfv (syn_csi (.cv f)) (.cv q)))))))
      p0084
  have p0086 :=
    @g_syl (syn_wiso (.cv f) R S D E)
      (syn_wa (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 D) (syn_cpw1 E)) (syn_wral p (syn_cpw1 D)
          (syn_wral q (syn_cpw1 D) (syn_wb (syn_wbr (.cv p) (syn_csi R) (.cv q))
              (syn_wbr (syn_cfv (syn_csi (.cv f)) (.cv p)) (syn_csi S)
                (syn_cfv (syn_csi (.cv f)) (.cv q)))))))
      (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) p0083
      p0085
  exact p0086

@[expose]
noncomputable def g_hndownbrndv (x : Var) (y : Var) (g : Var) (a : Var) (b : Var)
    (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_b_x : b ≠ x) (dv_b_y : b ≠ y) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv a)
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))) :=
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
  have dv_cache_0005 : x ∉ ((syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))).fv :=
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
  have p0000 := @g_vex a
  have p0001 := @g_vex b
  have p0002 := @g_id (.classEq (.cv x) (.cv a))
  have p0003 := @g_sneqd (.classEq (.cv x) (.cv a)) (.cv x) (.cv a) p0002
  have p0004 :=
    @g_breq1d (.classEq (.cv x) (.cv a)) (syn_csn (.cv x)) (syn_csn (.cv a))
      (syn_csn (.cv y)) (.cv g) p0003
  have p0005 := @g_id (.classEq (.cv y) (.cv b))
  have p0006 := @g_sneqd (.classEq (.cv y) (.cv b)) (.cv y) (.cv b) p0005
  have p0007 :=
    @g_breq2d (.classEq (.cv y) (.cv b)) (syn_csn (.cv y)) (syn_csn (.cv b))
      (syn_csn (.cv a)) (.cv g) p0006
  have p0008 :=
    @g_eqid (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0009 :=
    @g_brab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) x y (.cv a) (.cv b)
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0000 p0001 p0004 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_hndownexndv (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (syn_cvv)) :=
  by
  have dv_cache_0001 : g ≠ x := by exact (show g ≠ x from (by exact dv_g_x))
  have dv_cache_0002 : g ≠ y := by
    clear dv_cache_0001
    exact (show g ≠ y from (by exact dv_g_y))
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_enpw1lem1 x y g dv_cache_0001 dv_cache_0002 dv_cache_0003
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

@[expose]
noncomputable def g_hndownmpteqdv (x : Var) (y : Var) (z : Var) (D : Class) (g : Var)
    (E : Class) (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (_dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv) (dv_E_z : z ∉ E.fv) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_g_z : g ≠ z) (dv_x_y : x ≠ y) (_dv_x_z : x ≠ z)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classEq (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
          (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))) :=
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
  have dv_cache_0009 : z ∉ ((syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))).fv :=
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
    a ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv :=
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
    b ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv :=
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
    a ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv :=
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
    b ∉ ((syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))).fv :=
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
  have dv_cache_0017 : a ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
  have dv_cache_0018 : b ∉ ((syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
    (Nominal.biimpRefl (syn_wbr (.cv a)
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)))
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv a)
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
        (.classMem (syn_cop (.cv a) (.cv b))
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0000
  have p0002 :=
    @g_bicomd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (.cv a)
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0001
  have p0003 :=
    @g_hndownbrndv x y g a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv a)
          (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0003
  have p0005 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
  have p0006 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
  have p0008 := @g_breldm (syn_csn (.cv a)) (syn_csn (.cv b)) (.cv g)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (.classMem (syn_csn (.cv a)) (syn_cdm (.cv g))) p0005 p0008
  have p0011 := @g_f1odm (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0012 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classEq (syn_cdm (.cv g)) (syn_cpw1 D)) p0006 p0011
  have p0013 :=
    @g_eleqtrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_csn (.cv a)) (syn_cdm (.cv g)) (syn_cpw1 D) p0009 p0012
  have p0014 := @g_snelpw1 (.cv a) D
  have p0015 :=
    @g_biimpi (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D) p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) (.classMem (.cv a) D) p0013 p0015
  have p0017 :=
    @g_jca
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D) p0006 p0016
  have p0018 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0019 := @g_f1ofn (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0020 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (syn_wfn (.cv g) (syn_cpw1 D)) p0018
      p0019
  have p0021 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)
  have p0023 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classMem (.cv a) D) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0021 p0014
  have p0024 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wfn (.cv g) (syn_cpw1 D)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0020
      p0023
  have p0025 := @g_fnbrfvb (syn_cpw1 D) (syn_csn (.cv a)) (syn_csn (.cv b)) (.cv g)
  have p0026 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wa (syn_wfn (.cv g) (syn_cpw1 D)) (.classMem (syn_csn (.cv a)) (syn_cpw1 D)))
      (syn_wb (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b)))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      p0024 p0025
  have p0027 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b)))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0026
  have p0029 := @g_f1of (syn_cpw1 D) (syn_cpw1 E) (.cv g)
  have p0030 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0018 p0029
  have p0034 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_csn (.cv a)) (syn_cpw1 D)) p0030 p0023
  have p0035 := @g_ffvelrn (syn_cpw1 D) (syn_cpw1 E) (syn_csn (.cv a)) (.cv g)
  have p0036 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wa (syn_wf (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (.classMem (syn_csn (.cv a)) (syn_cpw1 D)))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E)) p0034 p0035
  have p0037 := @g_pw1argclcl E (syn_cfv (.cv g) (syn_csn (.cv a)))
  have p0038 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classMem (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_cpw1 E))
      (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E)
        (.classEq (syn_cfv (.cv g) (syn_csn (.cv a)))
          (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))))
      p0036 p0037
  have p0039 :=
    @g_simpr (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E)
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv a)))
        (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))
  have p0040 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wa (.classMem (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) E)
        (.classEq (syn_cfv (.cv g) (syn_csn (.cv a)))
          (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv a)))
        (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))))
      p0038 p0039
  have p0041 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_cfv (.cv g) (syn_csn (.cv a)))
      (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b)) p0040
  have p0042 := @g_fvex (syn_csn (.cv a)) (.cv g)
  have p0043 := @g_uniex (syn_cfv (.cv g) (syn_csn (.cv a))) p0042
  have p0044 := @g_sneqb (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b) p0043
  have p0045 :=
    @g_a1i
      (syn_wb (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))
          (syn_csn (.cv b))) (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D)) p0044
  have p0046 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b)))
      (.classEq (syn_csn (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a))))) (syn_csn (.cv b)))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0041 p0045
  have p0047 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (.classEq (syn_cfv (.cv g) (syn_csn (.cv a))) (syn_csn (.cv b)))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0027 p0046
  have p0049 := @g_id (.classEq (.cv z) (.cv a))
  have p0050 := @g_sneqd (.classEq (.cv z) (.cv a)) (.cv z) (.cv a) p0049
  have p0051 :=
    @g_fveq2d (.classEq (.cv z) (.cv a)) (syn_csn (.cv z)) (syn_csn (.cv a)) (.cv g) p0050
  have p0052 :=
    @g_unieqd (.classEq (.cv z) (.cv a)) (syn_cfv (.cv g) (syn_csn (.cv z)))
      (syn_cfv (.cv g) (syn_csn (.cv a))) p0051
  have p0053 := @g_eqid (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0056 :=
    @g_fvmpt z (.cv a) (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) D
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0052 p0053 p0043
  have p0057 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classMem (.cv a) D)
      (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
        (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))))
      p0021 p0056
  have p0058 :=
    @g_eqeq1d (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
      (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b) p0057
  have p0059 :=
    @g_bicomd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
        (.cv b))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b)) p0058
  have p0061 := @g_pw1descentf1odv z D g E dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0062 := @g_f1ofn D E (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0063 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E)
      (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) p0061
      p0062
  have p0064 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D) p0018
      p0063
  have p0066 :=
    @g_jca (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D)
      (.classMem (.cv a) D) p0064 p0021
  have p0067 :=
    @g_fnbrfvb D (.cv a) (.cv b)
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0068 :=
    @g_syl (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wa (syn_wfn (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D)
        (.classMem (.cv a) D))
      (syn_wb (.classEq
          (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
          (.cv b))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      p0066 p0067
  have p0069 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b))
      (.classEq (syn_cfv (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv a))
        (.cv b))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0059 p0068
  have p0070 :=
    @g_bitrd (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (.classEq (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv a)))) (.cv b))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0047 p0069
  have p0071 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wb (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      p0017 p0070
  have p0072 :=
    @g_biimpd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0071
  have p0073 :=
    @g_mpd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0005 p0072
  have p0074 :=
    @g_ex (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0073
  have p0075 :=
    @g_simpr (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
  have p0076 :=
    @g_simpl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
  have p0078 :=
    @g_breldm (.cv a) (.cv b)
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0079 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      (.classMem (.cv a)
        (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))))
      p0075 p0078
  have p0082 := @g_f1odm D E (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
  have p0083 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) D E)
      (.classEq (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) D)
      p0061 p0082
  have p0084 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classEq (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) D)
      p0076 p0083
  have p0085 :=
    @g_eleqtrd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (.cv a) (syn_cdm (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))) D
      p0079 p0084
  have p0086 :=
    @g_jca
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D) p0076 p0085
  have p0140 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) (.classMem (.cv a) D))
      (syn_wb (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      p0086 p0070
  have p0141 :=
    @g_biimprd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0140
  have p0142 :=
    @g_mpd
      (syn_wa (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
        (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0075 p0141
  have p0143 :=
    @g_ex (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b))) p0142
  have p0144 :=
    @g_impbid (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0074 p0143
  have p0145 :=
    @g_bitrd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wbr (.cv a)
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
      (syn_wbr (syn_csn (.cv a)) (.cv g) (syn_csn (.cv b)))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0004 p0144
  have p0146 :=
    @g_bitrd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (syn_wbr (.cv a)
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      p0002 p0145
  have p0147 :=
    (Nominal.biimpRefl
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b)))
  have p0148 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
          (.cv b)) (.classMem (syn_cop (.cv a) (.cv b))
          (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) p0147
  have p0149 :=
    @g_bitrd (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (syn_wbr (.cv a) (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))
      p0146 p0148
  have p0150 :=
    @g_eqrelrdv (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E)) a b
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      p0149
  exact p0150

@[expose]
noncomputable def g_pw1isoexequivndv (D : Class) (R : Class) (S : Class) (f : Var)
    (g : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_g : g ∉ D.fv) (dv_E_f : f ∉ E.fv)
    (dv_E_g : g ∉ E.fv) (dv_R_f : f ∉ R.fv) (dv_R_g : g ∉ R.fv) (dv_S_f : f ∉ S.fv)
    (dv_S_g : g ∉ S.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (syn_wb (syn_wex f (syn_wiso (.cv f) R S D E)) (syn_wex g
          (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)))) :=
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
  have dv_cache_0001 : g ∉ ((syn_csi (.cv f))).fv := by
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
      ((syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))).fv :=
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
      ((syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)))).fv :=
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
    f ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv :=
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
      ((syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S
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
  have dv_cache_0018 : g ∉ ((syn_wex f (syn_wiso (.cv f) R S D E))).fv :=
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
  have p0000 := @g_pw1raiseisomdv D R S f E
  have p0001 := @g_vex f
  have p0002 := @g_siex (.cv f) p0001
  have p0003 :=
    @g_isoeq1 (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (syn_csi (.cv f)) (.cv g)
  have p0004 :=
    @g_spcev (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)) g
      (syn_csi (.cv f)) dv_cache_0001 dv_cache_0002 p0002 p0003
  have p0005 :=
    @g_syl (syn_wiso (.cv f) R S D E)
      (syn_wiso (syn_csi (.cv f)) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)))
      p0000 p0004
  have p0006 :=
    @g_exlimiv (syn_wiso (.cv f) R S D E)
      (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))) f
      dv_cache_0003 p0005
  have p0007 := @g_pw1descentisomdv z D R S g E dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 := @g_isof1o (syn_cpw1 D) (syn_cpw1 E) (syn_csi R) (syn_csi S) (.cv g)
  have p0009 :=
    @g_hndownmpteqdv x y z D g E dv_cache_0007 dv_cache_0008 dv_cache_0004 dv_cache_0009
      dv_cache_0010 dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0006 dv_cache_0013
      dv_cache_0014 dv_cache_0015
  have p0010 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wf1o (.cv g) (syn_cpw1 D) (syn_cpw1 E))
      (.classEq (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))
      p0008 p0009
  have p0011 :=
    @g_isoeq1 D E R S (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z)))))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0012 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (.classEq (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))))
      (syn_wb (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R
          S D E)
        (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E))
      p0010 p0011
  have p0013 :=
    @g_biimprd (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E)
      (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)
      p0012
  have p0014 :=
    @g_mpd (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wiso (syn_cmpt z D (syn_cuni (syn_cfv (.cv g) (syn_csn (.cv z))))) R S D E)
      (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E)
      p0007 p0013
  have p0015 := @g_hndownexndv x y g dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0016 :=
    @g_isoeq1 D E R S
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv f)
  have p0017 :=
    @g_spcev (syn_wiso (.cv f) R S D E)
      (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E)
      f (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      dv_cache_0016 dv_cache_0017 p0015 p0016
  have p0018 :=
    @g_syl (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wiso (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) R S D E)
      (syn_wex f (syn_wiso (.cv f) R S D E)) p0014 p0017
  have p0019 :=
    @g_exlimiv (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E))
      (syn_wex f (syn_wiso (.cv f) R S D E)) g dv_cache_0018 p0018
  have p0020 :=
    @g_impbii (syn_wex f (syn_wiso (.cv f) R S D E))
      (syn_wex g (syn_wiso (.cv g) (syn_csi R) (syn_csi S) (syn_cpw1 D) (syn_cpw1 E)))
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

@[expose]
noncomputable def g_hwnisodirectisobndv (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) :=
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
  have p0000 := @g_hwnisohwisob v u A dv_cache_0001
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv v))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0000
  have p0002 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0003 :=
    @g_a1i
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv v))) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0002
  have p0004 :=
    @g_pm3_2 (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0005 :=
    @g_impbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0003 p0004
  have p0006 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0001 p0005
  have p0007 := @g_brhwisoany v u A h dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
          (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0010 :=
    @g_a1i
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0009
  have p0011 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0012 := @g_hwcnraw u A
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) p0011 p0012
  have p0014 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0015 := @g_hwcnraw v A
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcodes A)) p0014 p0015
  have p0017 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)) p0013
      p0016
  have p0018 :=
    @g_pm3_2
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
  have p0019 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (.imp (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
          (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))
      p0017 p0018
  have p0020 :=
    @g_impbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0010 p0019
  have p0021 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0008 p0020
  have p0022 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0006 p0021
  exact p0022

@[expose]
noncomputable def g_hwnisodirectisobclndv (A : Class) (B : Class) (C : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) :=
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
      ((Wff.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))))).fv :=
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
      ((Wff.imp (.classMem B (syn_cvv))
          (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
            (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
                (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
                  (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))))).fv :=
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
  have p0000 := @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0001 := @g_elex B (syn_chwcn A)
  have p0002 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0004 := @g_elex C (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 := @g_biid (.classMem B (syn_cvv))
  have p0007 :=
    @g_a1i (syn_wb (.classMem B (syn_cvv)) (.classMem B (syn_cvv))) (.classEq (.cv v) C)
      p0006
  have p0008 := @g_biid (.classMem B (syn_chwcn A))
  have p0009 :=
    @g_a1i (syn_wb (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A)))
      (.classEq (.cv v) C) p0008
  have p0010 := @g_id (.classEq (.cv v) C)
  have p0011 := @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0010
  have p0012 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem B (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem C (syn_chwcn A)) p0009 p0011
  have p0014 := @g_breq2d (.classEq (.cv v) C) (.cv v) C B (syn_chwniso A) p0010
  have p0016 := @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0010
  have p0017 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (.cv h)
  have p0018 :=
    @g_syl (.classEq (.cv v) C)
      (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0016 p0017
  have p0020 := @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0010
  have p0021 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)
      (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (.cv h)
  have p0022 :=
    @g_syl (.classEq (.cv v) C)
      (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      p0020 p0021
  have p0023 :=
    @g_bitrd (.classEq (.cv v) C)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
      p0018 p0022
  have p0024 :=
    @g_exbidv (.classEq (.cv v) C)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
      h dv_cache_0001 p0023
  have p0025 :=
    @g_bibi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (.cv v))
      (syn_wbr B (syn_chwniso A) C)
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      p0014 p0024
  have p0026 :=
    @g_imbi12d (.classEq (.cv v) C)
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))
      p0012 p0025
  have p0027 :=
    @g_imbi12d (.classEq (.cv v) C) (.classMem B (syn_cvv)) (.classMem B (syn_cvv))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))
      p0007 p0026
  have p0028 := @g_id (.classEq (.cv u) B)
  have p0029 := @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0028
  have p0030 := @g_biid (.classMem (.cv v) (syn_chwcn A))
  have p0031 :=
    @g_a1i (syn_wb (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classEq (.cv u) B) p0030
  have p0032 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A)) p0029 p0031
  have p0034 := @g_breq1d (.classEq (.cv u) B) (.cv u) B (.cv v) (syn_chwniso A) p0028
  have p0036 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0028
  have p0037 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B)
      (.cv h)
  have p0038 :=
    @g_syl (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0036 p0037
  have p0040 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0028
  have p0041 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0042 :=
    @g_syl (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0040 p0041
  have p0043 :=
    @g_bitrd (.classEq (.cv u) B)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      p0038 p0042
  have p0044 :=
    @g_exbidv (.classEq (.cv u) B)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      h dv_cache_0002 p0043
  have p0045 :=
    @g_bibi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr B (syn_chwniso A) (.cv v))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0034 p0044
  have p0046 :=
    @g_imbi12d (.classEq (.cv u) B)
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))
      p0032 p0045
  have p0047 :=
    @g_hwnisodirectisobndv v u A h dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0048 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))))
      u B (syn_cvv) dv_cache_0007 dv_cache_0008 p0046 p0047
  have p0049 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cvv))
        (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wb (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
                (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))))
      (.imp (.classMem B (syn_cvv))
        (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
                (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))))
      v C (syn_cvv) dv_cache_0009 dv_cache_0010 p0027 p0048
  have p0050 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_cvv))
      (.imp (.classMem B (syn_cvv))
        (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
          (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
                (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))))
      p0005 p0049
  have p0051 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_cvv))
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))
      p0002 p0050
  have p0052 :=
    @g_pm2_43i (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wb (syn_wbr B (syn_chwniso A) C) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))
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

@[expose]
noncomputable def g_hnsicodemapkernelndv (A : Class) (r : Var) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_q_r : q ≠ r) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
        (syn_wb (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
          (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
            (syn_cfv (syn_chnsicodemap A) (.cv r))))) :=
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
  have dv_cache_0001 : q ∉ ((syn_chwcn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_q,
          not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_chwcn A)).fv :=
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
  have dv_cache_0003 : q ∉ ((syn_chwniso A)).fv :=
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
  have dv_cache_0004 : r ∉ ((syn_chwniso A)).fv :=
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
  have dv_cache_0007 : f ∉ ((syn_cuni (.cv q))).fv :=
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
  have dv_cache_0008 : f ∉ ((syn_cuni (.cv r))).fv :=
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
  have dv_cache_0009 : f ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv q)))).fv :=
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
  have dv_cache_0010 : g ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv q)))).fv :=
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
  have dv_cache_0011 : f ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv r)))).fv :=
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
  have dv_cache_0012 : g ∉ ((syn_cfv (syn_c2nd) (syn_cuni (.cv r)))).fv :=
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
  have dv_cache_0013 : f ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv q)))).fv :=
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
  have dv_cache_0014 : g ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv q)))).fv :=
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
  have dv_cache_0015 : f ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv r)))).fv :=
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
  have dv_cache_0016 : g ∉ ((syn_cfv (syn_c1st) (syn_cuni (.cv r)))).fv :=
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
  have dv_cache_0018 : g ∉ ((syn_cpw1 A)).fv :=
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
  have dv_cache_0019 : g ∉ ((syn_cfv (syn_chnsicodemap A) (.cv q))).fv :=
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
  have dv_cache_0020 : g ∉ ((syn_cfv (syn_chnsicodemap A) (.cv r))).fv :=
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
      ((syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
          (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))).fv :=
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
    @g_pw1typedbrndv (syn_chwcn A) (syn_chwniso A) r q dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0002 := @g_hnwpw1argcl (syn_chwcn A) q
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0001 p0002
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0005 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A)) p0003 p0004
  have p0006 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
  have p0007 := @g_hnwpw1argcl (syn_chwcn A) r
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      p0006 p0007
  have p0009 :=
    @g_simpl (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
      (.classEq (.cv r) (syn_csn (syn_cuni (.cv r))))
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wa (.classMem (syn_cuni (.cv r)) (syn_chwcn A))
        (.classEq (.cv r) (syn_csn (syn_cuni (.cv r)))))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0008 p0009
  have p0011 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
      (.classMem (syn_cuni (.cv r)) (syn_chwcn A)) p0005 p0010
  have p0012 :=
    @g_hwnisodirectisobclndv A (syn_cuni (.cv q)) (syn_cuni (.cv r)) f dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chwcn A))
        (.classMem (syn_cuni (.cv r)) (syn_chwcn A)))
      (syn_wb (syn_wbr (syn_cuni (.cv q)) (syn_chwniso A) (syn_cuni (.cv r))) (syn_wex f
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
            (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
            (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0011 p0012
  have p0014 :=
    @g_pw1isoexequivndv (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
      (syn_cfv (syn_c1st) (syn_cuni (.cv q))) (syn_cfv (syn_c1st) (syn_cuni (.cv r))) f g
      (syn_cfv (syn_c2nd) (syn_cuni (.cv r))) dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0015 :=
    @g_a1i
      (syn_wb (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
            (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
            (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))) (syn_wex g
          (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      p0014
  have p0016 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wbr (syn_cuni (.cv q)) (syn_chwniso A) (syn_cuni (.cv r)))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
          (syn_cfv (syn_c1st) (syn_cuni (.cv r))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0013 p0015
  have p0017 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
      (syn_wbr (syn_cuni (.cv q)) (syn_chwniso A) (syn_cuni (.cv r)))
      (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0000 p0016
  have p0018 := @g_hnsicodemapfndv A
  have p0019 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      p0018
  have p0021 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) p0019 p0001
  have p0022 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (.cv q)
      (syn_chnsicodemap A)
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A))) p0021
      p0022
  have p0027 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))) p0019 p0006
  have p0028 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (.cv r)
      (syn_chnsicodemap A)
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwcn (syn_cpw1 A))) p0027
      p0028
  have p0030 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwcn (syn_cpw1 A))) p0023
      p0029
  have p0031 :=
    @g_hwnisodirectisobclndv (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cfv (syn_chnsicodemap A) (.cv r)) g dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0032 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwcn (syn_cpw1 A)))
        (.classMem (syn_cfv (syn_chnsicodemap A) (.cv r)) (syn_chwcn (syn_cpw1 A))))
      (syn_wb (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
          (syn_cfv (syn_chnsicodemap A) (.cv r))) (syn_wex g
          (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
            (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
            (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
            (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))))
      p0030 p0031
  have p0034 := @g_hnsicodemapvalndv A q dv_cache_0021
  have p0035 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      p0001 p0034
  have p0036 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_c1st) p0035
  have p0037 := @g_fvex (syn_cuni (.cv q)) (syn_c1st)
  have p0038 := @g_siex (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0037
  have p0039 := @g_fvex (syn_cuni (.cv q)) (syn_c2nd)
  have p0040 := @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0039
  have p0041 :=
    @g_opfv1st (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0038 p0040
  have p0042 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      p0041
  have p0043 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) p0036 p0042
  have p0044 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (.cv g)
  have p0045 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q)))))
      (syn_wb (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
        (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      p0043 p0044
  have p0047 := @g_hnsicodemapvalndv A r dv_cache_0022
  have p0048 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classMem (.cv r) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (.cv r))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0006 p0047
  have p0049 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_chnsicodemap A) (.cv r))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (syn_c1st) p0048
  have p0050 := @g_fvex (syn_cuni (.cv r)) (syn_c1st)
  have p0051 := @g_siex (syn_cfv (syn_c1st) (syn_cuni (.cv r))) p0050
  have p0052 := @g_fvex (syn_cuni (.cv r)) (syn_c2nd)
  have p0053 := @g_pw1ex (syn_cfv (syn_c2nd) (syn_cuni (.cv r))) p0052
  have p0054 :=
    @g_opfv1st (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0051 p0053
  have p0055 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      p0054
  have p0056 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) p0049 p0055
  have p0057 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (.cv g)
  have p0058 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))))
      (syn_wb (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
        (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      p0056 p0057
  have p0059 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      p0045 p0058
  have p0063 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_chnsicodemap A) (.cv q))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_c2nd) p0035
  have p0068 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0038 p0040
  have p0069 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      p0068
  have p0070 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0063 p0069
  have p0071 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (.cv g)
  have p0072 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))
      (syn_wb (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
        (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      p0070 p0071
  have p0073 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      p0059 p0072
  have p0077 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_chnsicodemap A) (.cv r))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (syn_c2nd) p0048
  have p0082 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0051 p0053
  have p0083 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
            (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      p0082
  have p0084 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))) p0077 p0083
  have p0085 :=
    @g_isoeq5 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
      (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r)))) (.cv g)
  have p0086 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      (syn_wb (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
        (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0084 p0085
  have p0087 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      p0073 p0086
  have p0088 :=
    @g_exbidv
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r))))
      (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
        (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r)))))
      g dv_cache_0023 p0087
  have p0089 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_wex g (syn_wiso (.cv g) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (.cv r)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv q)))
          (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (.cv r)))))
      (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0032 p0088
  have p0090 :=
    @g_bicomd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (.cv r)))
      (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      p0089
  have p0091 :=
    @g_bitrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
        (.classMem (.cv r) (syn_cpw1 (syn_chwcn A))))
      (syn_wbr (.cv q) (syn_csi (syn_chwniso A)) (.cv r))
      (syn_wex g (syn_wiso (.cv g) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv q))))
          (syn_csi (syn_cfv (syn_c1st) (syn_cuni (.cv r))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (.cv r))))))
      (syn_wbr (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))
        (syn_cfv (syn_chnsicodemap A) (.cv r)))
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

@[expose]
noncomputable def g_siorreflectndv (D : Class) (R : Class)
    (hyp_siorreflectndv_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_siorreflectndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cstrict) D)) :=
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
  have dv_cache_0003 : x ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv :=
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
  have dv_cache_0009 : z ∉ ((syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))).fv :=
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
    @g_a1i (.classMem R (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      hyp_siorreflectndv_1
  have p0001 :=
    @g_a1i (.classMem D (syn_cvv)) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      hyp_siorreflectndv_2
  have p0002 :=
    @g_simpl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
  have p0003 := @g_wppweref (syn_cpw1 D) (syn_csi R)
  have p0004 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D))
      (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cref) (syn_cpw1 D)) p0002 p0003
  have p0005 :=
    @g_simpr (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
  have p0006 := @g_snelpw1 (.cv x) D
  have p0007 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0005 p0007
  have p0009 :=
    @g_refd (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D))
      (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) p0004 p0008
  have p0010 := @g_vex x
  have p0012 := @g_brsnsi (.cv x) (.cv x) R p0010 p0010
  have p0013 :=
    @g_biimpi (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv x)))
      (syn_wbr (.cv x) R (.cv x)) p0012
  have p0014 :=
    @g_syl (syn_wa (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D))
      (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv x)))
      (syn_wbr (.cv x) R (.cv x)) p0009 p0013
  have p0015 :=
    @g_refrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x D R (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000 p0001 p0014
  have p0018 :=
    @g_simp1 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0019 := @g_wppwepo (syn_cpw1 D) (syn_csi R)
  have p0020 := @g_porta (syn_cpw1 D) (syn_csi R)
  have p0021 :=
    @g_simp2bi (syn_wbr (syn_csi R) (syn_cpartial) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cref) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_ctrans) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cantisym) (syn_cpw1 D)) p0020
  have p0022 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cpartial) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_ctrans) (syn_cpw1 D)) p0019 p0021
  have p0023 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_ctrans) (syn_cpw1 D)) p0018 p0022
  have p0024 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0025 := @g_simp1 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0026 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (.classMem (.cv x) D) p0024 p0025
  have p0029 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0026 p0007
  have p0031 := @g_simp2 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0032 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (.classMem (.cv y) D) p0024 p0031
  have p0033 := @g_snelpw1 (.cv y) D
  have p0034 :=
    @g_biimpri (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) (.classMem (.cv y) D) p0033
  have p0035 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (.classMem (.cv y) D) (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) p0032 p0034
  have p0037 := @g_simp3 (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D)
  have p0038 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (.classMem (.cv z) D) p0024 p0037
  have p0039 := @g_snelpw1 (.cv z) D
  have p0040 :=
    @g_biimpri (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) (.classMem (.cv z) D) p0039
  have p0041 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (.classMem (.cv z) D) (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) p0038 p0040
  have p0042 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
  have p0043 := @g_simpl (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))
  have p0044 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv x) R (.cv y)) p0042 p0043
  have p0046 := @g_vex y
  have p0047 := @g_brsnsi (.cv x) (.cv y) R p0010 p0046
  have p0048 :=
    @g_biimpri (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0047
  have p0049 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) p0044 p0048
  have p0051 := @g_simpr (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))
  have p0052 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv y) R (.cv z)) p0042 p0051
  have p0054 := @g_vex z
  have p0055 := @g_brsnsi (.cv y) (.cv z) R p0046 p0054
  have p0056 :=
    @g_biimpri (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv z)))
      (syn_wbr (.cv y) R (.cv z)) p0055
  have p0057 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wbr (.cv y) R (.cv z))
      (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv z))) p0052 p0056
  have p0058 :=
    @g_trd
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_csn (.cv z)) p0023
      p0029 p0035 p0041 p0049 p0057
  have p0061 := @g_brsnsi (.cv x) (.cv z) R p0010 p0054
  have p0062 :=
    @g_biimpi (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv z)))
      (syn_wbr (.cv x) R (.cv z)) p0061
  have p0063 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (.classMem (.cv z) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z))))
      (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv z)))
      (syn_wbr (.cv x) R (.cv z)) p0058 p0062
  have p0064 :=
    @g_trrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x y z D R (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007
      dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      p0000 p0001 p0063
  have p0067 :=
    @g_simp1 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0068 := @g_wppweantisym (syn_cpw1 D) (syn_csi R)
  have p0069 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cantisym) (syn_cpw1 D)) p0067 p0068
  have p0070 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0071 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0072 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0070
      p0071
  have p0073 := @g_snelpw1 (.cv x) D
  have p0074 :=
    @g_biimpri (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) (.classMem (.cv x) D) p0073
  have p0075 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0072 p0074
  have p0076 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0077 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0078 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0076
      p0077
  have p0079 := @g_snelpw1 (.cv y) D
  have p0080 :=
    @g_biimpri (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) (.classMem (.cv y) D) p0079
  have p0081 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (.classMem (.cv y) D) (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) p0078 p0080
  have p0082 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0083 := @g_simpl (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))
  have p0084 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv x) R (.cv y)) p0082 p0083
  have p0085 := @g_vex x
  have p0086 := @g_vex y
  have p0087 := @g_brsnsi (.cv x) (.cv y) R p0085 p0086
  have p0088 :=
    @g_biimpri (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0087
  have p0089 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y))) p0084 p0088
  have p0090 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
  have p0091 := @g_simpr (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))
  have p0092 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) p0090 p0091
  have p0095 := @g_brsnsi (.cv y) (.cv x) R p0046 p0010
  have p0096 :=
    @g_biimpri (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) p0095
  have p0097 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_wbr (.cv y) R (.cv x))
      (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x))) p0092 p0096
  have p0098 :=
    @g_antid
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) (syn_csn (.cv y)) p0069 p0075 p0081 p0089
      p0097
  have p0099 := @g_vex x
  have p0100 := @g_sneqr (.cv x) (.cv y) p0099
  have p0101 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
        (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))
      (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (.classEq (.cv x) (.cv y)) p0098
      p0100
  have p0102_e02_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
          (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
          syn_wrex syn_wex syn_cphi syn_csi syn_copab syn_cwe syn_cin syn_cstrict
          syn_cfound syn_cpw1
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0101
  have p0102 :=
    @g_antird (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x y D R (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008
      dv_cache_0010 p0000 p0001 p0102_e02_recanon
  have p0103 :=
    @g_n_3jca (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cref) D)
      (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0015 p0064 p0102
  have p0104 := @g_porta D R
  have p0105 :=
    @g_biimpri (syn_wbr R (syn_cpartial) D)
      (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D))
      p0104
  have p0106 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D))
      (syn_wbr R (syn_cpartial) D) p0103 p0105
  have p0109 :=
    @g_simp1 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
      (.classMem (.cv y) D)
  have p0110 := @g_wppweconnex (syn_cpw1 D) (syn_csi R)
  have p0111 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cconnex) (syn_cpw1 D)) p0109 p0110
  have p0112 :=
    @g_simp2 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
      (.classMem (.cv y) D)
  have p0115 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0112 p0007
  have p0116 :=
    @g_simp3 (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
      (.classMem (.cv y) D)
  have p0119 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (.classMem (.cv y) D) (.classMem (syn_csn (.cv y)) (syn_cpw1 D)) p0116 p0034
  have p0120 :=
    @g_connexd
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (syn_cpw1 D) (syn_csi R) (syn_csn (.cv x)) (syn_csn (.cv y)) p0111 p0115 p0119
  have p0127 :=
    @g_orbi12i (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) p0047 p0095
  have p0128 :=
    @g_biimpi
      (syn_wo (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
        (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x))))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) p0127
  have p0129 :=
    @g_syl
      (syn_w3a (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (.classMem (.cv x) D)
        (.classMem (.cv y) D))
      (syn_wo (syn_wbr (syn_csn (.cv x)) (syn_csi R) (syn_csn (.cv y)))
        (syn_wbr (syn_csn (.cv y)) (syn_csi R) (syn_csn (.cv x))))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) p0120 p0128
  have p0130 :=
    @g_connexrd (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) x y D R (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008
      dv_cache_0010 p0000 p0001 p0129
  have p0131 :=
    @g_jca (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) (syn_wbr R (syn_cpartial) D)
      (syn_wbr R (syn_cconnex) D) p0106 p0130
  have p0132 := @g_sopc D R
  have p0133 :=
    @g_biimpri (syn_wbr R (syn_cstrict) D)
      (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0132
  have p0134 :=
    @g_syl (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D))
      (syn_wbr R (syn_cstrict) D) p0131 p0133
  exact p0134


end NFChoice.DirectNominalPrf.WPPReplay

end
