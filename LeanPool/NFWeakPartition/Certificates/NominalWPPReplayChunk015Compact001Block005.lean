/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncardmono (A : Class) (D : Class)
    (hyp_hncardmono_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hncardmono_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hncardmono_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((syn_chnqinc D A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          Finset.mem_union, fresh_f_not_A, fresh_f_not_D, or_false, not_false_eq_true])
  have dv_cache_0002 :
    f ∉ ((syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          fresh_f_not_D, fresh_f_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_chnord D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_f_not_D, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_f_not_A, not_false_eq_true])
  have p0000 := @g_hnqincf1 A D hyp_hncardmono_1 hyp_hncardmono_2 hyp_hncardmono_3
  have p0001 :=
    @g_pm3_2i (.classMem D (syn_cvv)) (.classMem A (syn_cvv)) hyp_hncardmono_2
      hyp_hncardmono_3
  have p0002 := @g_hnqincexg A D
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_f1eq1 (syn_chnord D) (syn_chnord A) (.cv f) (syn_chnqinc D A)
  have p0005 :=
    @g_spcegv (syn_wf1 (.cv f) (syn_chnord D) (syn_chnord A))
      (syn_wf1 (syn_chnqinc D A) (syn_chnord D) (syn_chnord A)) f (syn_chnqinc D A)
      (syn_cvv) dv_cache_0001 dv_cache_0002 p0004
  have p0006 := Nominal.mp p0003 p0005
  have p0007 := Nominal.mp p0000 p0006
  have p0008 := @g_hnordex D hyp_hncardmono_2
  have p0009 := @g_hnordex A hyp_hncardmono_3
  have p0010 :=
    @g_nclenc (syn_chnord D) (syn_chnord A) f dv_cache_0003 dv_cache_0004 p0008 p0009
  have p0011 :=
    @g_mpbir (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A)))
      (syn_wex f (syn_wf1 (.cv f) (syn_chnord D) (syn_chnord A))) p0007 p0010
  have p0012 := (Nominal.classEqRefl (syn_chncard D))
  have p0013 := (Nominal.classEqRefl (syn_chncard A))
  have p0014 :=
    @g_breq12i (syn_chncard D) (syn_cnc (syn_chnord D)) (syn_chncard A)
      (syn_cnc (syn_chnord A)) (syn_clec) p0012 p0013
  have p0015 :=
    @g_mpbir (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))
      (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) p0011 p0014
  exact p0015

@[expose]
noncomputable def g_hnwcutcodecnndv (x : Var) (D : Class) (R : Class)
    (hyp_hnwcutcodecnndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))) :=
  by
  have p0000 := @g_a1i (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) hyp_hnwcutcodecnndv_1
  have p0001 := @g_id (.classMem (.cv x) D)
  have p0002 :=
    @g_jca (.classMem (.cv x) D) (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0000 p0001
  have p0003 := @g_westrsegndv x D R
  have p0004 :=
    @g_syl (.classMem (.cv x) D) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0006 :=
    @g_biimpi
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe))
      p0005
  have p0007 :=
    @g_syl (.classMem (.cv x) D)
      (syn_wbr (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cwe) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe))
      p0004 p0006
  have p0008 := @g_brex R D (syn_cwe)
  have p0009 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0008
  have p0010 := Nominal.mp hyp_hnwcutcodecnndv_1 p0009
  have p0012 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0008
  have p0013 := Nominal.mp hyp_hnwcutcodecnndv_1 p0012
  have p0017 := @g_idex
  have p0018 := @g_difex R (syn_cid) p0010 p0017
  have p0019 := @g_cnvex (syn_cdif R (syn_cid)) p0018
  have p0020 := @g_snex (.cv x)
  have p0021 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0019 p0020
  have p0022 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0013 p0021
  have p0035 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0022
      p0022
  have p0036 :=
    @g_inex R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0010 p0035
  have p0037 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0050 :=
    @g_elpw (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D
      p0022
  have p0051 :=
    @g_mpbir
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cpw D))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      p0037 p0050
  have p0052 :=
    @g_pm3_2i
      (.classMem (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cpw D))
      p0036 p0051
  have p0053 :=
    @g_opelxp
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)
      (syn_cpw D)
  have p0054 :=
    @g_mpbir
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cxp (syn_cvv) (syn_cpw D)))
      (syn_wa (.classMem (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cvv)) (.classMem
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cpw D)))
      p0052 p0053
  have p0055 :=
    @g_a1i
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cxp (syn_cvv) (syn_cpw D)))
      (.classMem (.cv x) D) p0054
  have p0056 :=
    @g_jca (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cwe))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cxp (syn_cvv) (syn_cpw D)))
      p0007 p0055
  have p0057 :=
    @g_elin
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))
  have p0058 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))) (syn_wa (.classMem (syn_cop
              (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_cxp (syn_cvv) (syn_cpw D)))))
      (.classMem (.cv x) D) p0057
  have p0059 :=
    @g_mpbird (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cwe)) (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_cxp (syn_cvv) (syn_cpw D))))
      p0056 p0058
  have p0060 := (Nominal.classEqRefl (syn_chwcodes D))
  have p0061 :=
    @g_eleq2i (syn_chwcodes D) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D)))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0060
  have p0062 :=
    @g_sylibr (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw D))))
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcodes D))
      p0059 p0061
  have p0063 :=
    @g_inss2 R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0105 :=
    @g_opfv2nd
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0036
      p0022
  have p0148 :=
    @g_pm3_2i
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0105 p0105
  have p0149 :=
    @g_xpeq12
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  have p0150 := Nominal.mp p0148 p0149
  have p0151 :=
    @g_eqcomi
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0150
  have p0152 :=
    @g_sseq2
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0153 := Nominal.mp p0151 p0152
  have p0154 :=
    @g_mpbi
      (syn_wss (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wss (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0063 p0153
  have p0196 :=
    @g_opfv1st
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0036
      p0022
  have p0197 :=
    @g_sseq1
      (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0198 := Nominal.mp p0196 p0197
  have p0199 :=
    @g_mpbir
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wss (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0154 p0198
  have p0200 :=
    @g_a1i
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (.classMem (.cv x) D) p0199
  have p0201 :=
    @g_jca (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcodes D))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0062 p0200
  have p0243 :=
    @g_opex
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0036
      p0022
  have p0244 :=
    @g_elhwcncl D
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0245 := Nominal.mp p0243 p0244
  have p0246 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwcn D)) (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      (.classMem (.cv x) D) p0245
  have p0247 :=
    @g_mpbird (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcn D))
      (syn_wa (.classMem (syn_cop (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0201 p0246
  have p0248 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0249 :=
    @g_eleq1i (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_chwcn D) p0248
  have p0250 :=
    @g_sylibr (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0247 p0249
  exact p0250

@[expose]
noncomputable def g_hnwcutcodecnclndv (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutcodecnclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 :
    x ∉
      ((Wff.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @g_elex B D
  have p0001 := @g_eleq1 (.cv x) B D
  have p0002 := @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B)
      (syn_chwcn D) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0001 p0003
  have p0005 := @g_hnwcutcodecnndv x D R hyp_hnwcutcodecnclndv_1
  have p0006 :=
    @g_vtoclg
      (.imp (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)))
      (.imp (.classMem B D) (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))) x B
      (syn_cvv) dv_cache_0002 dv_cache_0003 p0004 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem B D)
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_hnwcutrelfndv (D : Class) (R : Class)
    (hyp_hnwcutrelfndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ ((syn_cpw1 D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_chwcn D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_q_not_D, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chnwcutrel R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have p0000 := @g_hnwcutrelfn D R hyp_hnwcutrelfndv_1
  have p0001 := @g_hnwpw1argcl D q
  have p0002 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D)
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0001
  have p0003 := @g_hnwcutcodecnclndv (syn_cuni (.cv q)) D R hyp_hnwcutrelfndv_1
  have p0004 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 D)) (.classMem (syn_cuni (.cv q)) D)
      (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0002 p0003
  have p0005 := @g_hnwcutrelval D R q hyp_hnwcutrelfndv_1
  have p0006 :=
    @g_eleq1d (.classMem (.cv q) (syn_cpw1 D)) (syn_cfv (syn_chnwcutrel R D) (.cv q))
      (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D) p0005
  have p0007 :=
    @g_mpbird (.classMem (.cv q) (syn_cpw1 D))
      (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (syn_cuni (.cv q))) (syn_chwcn D)) p0004 p0006
  have p0008 :=
    @g_rgen (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)) q
      (syn_cpw1 D) p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D))
      (syn_wral q (syn_cpw1 D) (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D)))
      p0000 p0008
  have p0010 :=
    @g_ffnfv q (syn_cpw1 D) (syn_chwcn D) (syn_chnwcutrel R D) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0011 :=
    @g_mpbir (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnwcutrel R D) (syn_cpw1 D)) (syn_wral q (syn_cpw1 D)
          (.classMem (syn_cfv (syn_chnwcutrel R D) (.cv q)) (syn_chwcn D))))
      p0009 p0010
  exact p0011

@[expose]
noncomputable def g_hnwcutsirelvalndv (D : Class) (R : Class) (q : Var)
    (hyp_hnwcutsirelvalndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q))
          (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))))) :=
  by
  have p0000 := @g_pw12argcl (.cv q) D
  have p0001 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.cv q)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csi (syn_chnwcutrel R D))
      p0001
  have p0004 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000
  have p0005 := @g_snelpw1 (syn_cuni (syn_cuni (.cv q))) D
  have p0006 :=
    @g_biimpri (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0005
  have p0007 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D)) p0004 p0006
  have p0008 := @g_hnwcutrelfndv D R hyp_hnwcutsirelvalndv_1
  have p0009 :=
    @g_sifvald (syn_cpw1 D) (syn_chwcn D) (syn_csn (syn_cuni (syn_cuni (.cv q))))
      (syn_chnwcutrel R D) p0008
  have p0010 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_cpw1 D))
      (.classEq (syn_cfv (syn_csi (syn_chnwcutrel R D))
          (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
        (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0007 p0009
  have p0011 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q))
      (syn_cfv (syn_csi (syn_chnwcutrel R D)) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0002 p0010
  have p0014 :=
    @g_hnwcutrelvalcld (syn_cuni (syn_cuni (.cv q))) D R hyp_hnwcutsirelvalndv_1
  have p0015 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
        (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))))
      p0004 p0014
  have p0016 :=
    @g_sneqd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) p0015
  have p0017 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_cfv (syn_csi (syn_chnwcutrel R D)) (.cv q))
      (syn_csn (syn_cfv (syn_chnwcutrel R D) (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q))))) p0011 p0016
  exact p0017

@[expose]
noncomputable def g_hnwcutclassltnendv (x : Var) (y : Var) (D : Class) (R : Class)
    (hyp_hnwcutclassltnendv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) (.neg
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))) :=
  by
  have p0000 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      hyp_hnwcutclassltnendv_1
  have p0001 :=
    @g_simpl (.classMem (.cv y) D)
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0002 :=
    @g_jca
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem (.cv y) D)
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0004 :=
    @g_jca
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0002 p0003
  have p0005 := @g_hnwcutcodeltnoiso x y D R
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)
          (syn_chnwcutcode R D (.cv y))))
      p0004 p0005
  have p0008 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
  have p0009 :=
    @g_ssel (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) D
      (.cv x)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv x) D) p0003 p0010
  have p0012 := @g_hnwcutcodecnclndv (.cv x) D R hyp_hnwcutclassltnendv_1
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv x) D) (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D)) p0011
      p0012
  have p0015 := @g_hnwcutcodecnclndv (.cv y) D R hyp_hnwcutclassltnendv_1
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) D) (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0001
      p0015
  have p0017 :=
    @g_jca
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)) p0013 p0016
  have p0018 := @g_brex R D (syn_cwe)
  have p0019 := @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0020 :=
    @g_syl (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) (.classMem D (syn_cvv))
      p0018 p0019
  have p0021 := Nominal.mp hyp_hnwcutclassltnendv_1 p0020
  have p0022 :=
    @g_hwnisoclasseqbcl D (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D (.cv y))
      p0021
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (.classMem (syn_chnwcutcode R D (.cv x)) (syn_chwcn D))
        (.classMem (syn_chnwcutcode R D (.cv y)) (syn_chwcn D)))
      (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
        (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y))))
      p0017 p0022
  have p0024 :=
    @g_biimpd
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      p0023
  have p0025 :=
    @g_con3d
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D) (syn_chnwcutcode R D (.cv y)))
      p0024
  have p0026 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.neg (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)
          (syn_chnwcutcode R D (.cv y))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0006 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutclassinjndv (x : Var) (y : Var) (D : Class) (R : Class)
    (hyp_hnwcutclassinjndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
          (.classEq (.cv x) (.cv y)))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wne (.cv x) (.cv y))
  have p0001 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      p0000 p0001
  have p0003 := @g_wppweconnex D R
  have p0004 := Nominal.mp hyp_hnwcutclassinjndv_1 p0003
  have p0005 :=
    @g_a1i (syn_wbr R (syn_cconnex) D)
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      p0004
  have p0007 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0008 := @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0007
      p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classMem (.cv x) D) p0000 p0009
  have p0013 := @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0007
      p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classMem (.cv y) D) p0000 p0014
  have p0016 :=
    @g_connexd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0005 p0010 p0015
  have p0017 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0017 p0010
  have p0024 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0026 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wne (.cv x) (.cv y))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv x) (.cv y)) p0017 p0026
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0024 p0027
  have p0029 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))
      p0023 p0028
  have p0030 := @g_elstrictseg y x D R
  have p0031 :=
    @g_biimpri
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0029 p0031
  have p0033 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0032
  have p0034 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0034 p0015
  have p0041 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
  have p0044 :=
    @g_necomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0026
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wne (.cv y) (.cv x)) p0034 p0044
  have p0046 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0041 p0045
  have p0047 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0040 p0046
  have p0048 := @g_elstrictseg x y D R
  have p0049 :=
    @g_biimpri
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0048
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
          (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0047 p0049
  have p0051 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0050
  have p0052 :=
    @g_orim12d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0033 p0051
  have p0053 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wo (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0016 p0052
  have p0059 := @g_hnwcutclassltnendv x y D R hyp_hnwcutclassinjndv_1
  have p0060 :=
    @g_ex (.classMem (.cv y) D)
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0059
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y) D)
      (.imp (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.neg
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))))
      p0015 p0060
  have p0067 := @g_hnwcutclassltnendv y x D R hyp_hnwcutclassinjndv_1
  have p0068 :=
    @g_ex (.classMem (.cv x) D)
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))))
      p0067
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x) D)
      (.imp (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.neg
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))))
      p0010 p0068
  have p0070 :=
    @g_eqcom (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
  have p0071 :=
    @g_biimpi
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))
      p0070
  have p0072 :=
    @g_con3i
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))
      p0071
  have p0073 :=
    @g_syl6
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0069 p0072
  have p0074 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0061 p0073
  have p0075 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (syn_wo (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      p0053 p0074
  have p0076 :=
    @g_pm2_21dd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.neg (syn_wne (.cv x) (.cv y))) p0002 p0075
  have p0077 :=
    @g_pm2_01da
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (syn_wne (.cv x) (.cv y)) p0076
  have p0078 := @g_nne (.cv x) (.cv y)
  have p0079 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))
      (.neg (syn_wne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0077 p0078
  have p0080 :=
    @g_ex (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (.cv x) (.cv y)) p0079
  exact p0080

@[expose]
noncomputable def g_hnwcutclassinjclndv (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_hnwcutclassinjclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0006 :
    y ∉
      ((Wff.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
            (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    x ∉
      ((Wff.imp (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp
            (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
              (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
            (.classEq B (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_R,
          or_false, not_false_eq_true])
  have p0000 := @g_simpl (.classMem B D) (.classMem C D)
  have p0001 := @g_elex B D
  have p0002 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D)
      (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpr (.classMem B D) (.classMem C D)
  have p0004 := @g_elex C D
  have p0005 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D)
      (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D)) (.classMem B (syn_cvv))
      (.classMem C (syn_cvv)) p0002 p0005
  have p0007 := @g_eleq1 (.cv x) B D
  have p0008 := @g_biid (.classMem (.cv y) D)
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (.cv y) D) (.classMem (.cv y) D) p0007 p0009
  have p0011 := @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0012 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwniso D)
  have p0013 :=
    @g_syl (.classEq (.cv x) B)
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)))
      p0011 p0012
  have p0014 :=
    @g_eqeq1d (.classEq (.cv x) B) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) p0013
  have p0015 := @g_id (.classEq (.cv x) B)
  have p0016 := @g_eqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv x) B)
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0014 p0016
  have p0018 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (syn_wa (.classMem B D) (.classMem (.cv y) D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y)))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y)))
      p0010 p0017
  have p0019 := @g_biid (.classMem B D)
  have p0020 := @g_a1i (syn_wb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0019
  have p0021 := @g_eleq1 (.cv y) C D
  have p0022 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D)
      (.classMem C D) p0020 p0021
  have p0023 := @g_hnwcutcodeeq3 (.cv y) C D R dv_cache_0002
  have p0024 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv y)) (syn_chnwcutcode R D C) (syn_chwniso D)
  have p0025 :=
    @g_syl (.classEq (.cv y) C)
      (.classEq (syn_chnwcutcode R D (.cv y)) (syn_chnwcutcode R D C))
      (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      p0023 p0024
  have p0026 :=
    @g_eqeq2d (.classEq (.cv y) C) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))
      (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) p0025
  have p0027 := @g_id (.classEq (.cv y) C)
  have p0028 := @g_eqeq2d (.classEq (.cv y) C) (.cv y) C B p0027
  have p0029 :=
    @g_imbi12d (.classEq (.cv y) C)
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      (.classEq B (.cv y)) (.classEq B C) p0026 p0028
  have p0030 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (.classMem B D) (.classMem (.cv y) D))
      (syn_wa (.classMem B D) (.classMem C D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y)))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))
      p0022 p0029
  have p0031 := @g_hnwcutclassinjndv x y D R hyp_hnwcutclassinjclndv_1
  have p0032 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
          (.classEq (.cv x) (.cv y))))
      (.imp (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y))))
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))
      x y B C (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0018 p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))
      p0006 p0032
  have p0034 :=
    @g_pm2_43i (syn_wa (.classMem B D) (.classMem C D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))
      p0033
  exact p0034

@[expose]
noncomputable def g_lnkereq (R : Class) (S : Class) :
    Nominal.NPrf (.imp (.classEq R S) (.classEq (syn_clnker R) (syn_clnker S))) :=
  by
  have p0000 := @g_id (.classEq R S)
  have p0001 := @g_cnveq R S
  have p0002 := @g_ineq12d (.classEq R S) R S (syn_ccnv R) (syn_ccnv S) p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_clnker R))
  have p0004 := (Nominal.classEqRefl (syn_clnker S))
  have p0005 :=
    @g_n_3eqtr4g (.classEq R S) (syn_cin R (syn_ccnv R)) (syn_cin S (syn_ccnv S))
      (syn_clnker R) (syn_clnker S) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_lnanbi12ni (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_lnanbi12ni_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_lnanbi12ni_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (syn_wb (syn_wa ph (.neg ch)) (syn_wa ps (.neg th))) :=
  by
  have p0000 := @g_notbii ch th hyp_lnanbi12ni_2
  have p0001 := @g_anbi12i ph ps (.neg ch) (.neg th) hyp_lnanbi12ni_1 p0000
  exact p0001

@[expose]
noncomputable def g_lndifopvalg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (.classEq (syn_co A (syn_clndifop) B) (syn_cdif A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cdif A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cdif A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cdif A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_elex A V
  have p0001 := @g_elex B W
  have p0002 := @g_difexg A B (syn_cvv) (syn_cvv)
  have p0003 := @g_difeq1 (.cv x) A (.cv y)
  have p0004 := @g_difeq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lndifop x y
      dv_cache_0001
  have p0006 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (syn_cdif (.cv x) (.cv y)) (syn_cdif A B)
      (syn_clndifop) (syn_cdif A (.cv y)) (syn_cvv) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @g_mpd3an3 (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cdif A B) (syn_cvv))
      (.classEq (syn_co A (syn_clndifop) B) (syn_cdif A B)) p0002 p0006
  have p0008 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classEq (syn_co A (syn_clndifop) B) (syn_cdif A B)) (.classMem B W) p0000 p0001
      p0007
  exact p0008

@[expose]
noncomputable def g_fnlndifop : Nominal.NPrf (syn_wfn (syn_clndifop) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lndifop x y
      dv_cache_0001
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_difex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_fnmpt2i x y (syn_cvv) (syn_cvv) (syn_cdif (.cv x) (.cv y)) (syn_clndifop)
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @g_xpvv
  have p0006 := @g_fneq2i (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) (syn_clndifop) p0005
  have p0007 :=
    @g_mpbi (syn_wfn (syn_clndifop) (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_clndifop) (syn_cvv)) p0004 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lndifopex : Nominal.NPrf (.classMem (syn_clndifop) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    y ∉ ((syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉ ((syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cdif (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lndifop x y
      dv_cache_0001
  have p0001 := @g_vex y
  have p0002 := @g_otelins3 (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) p0001
  have p0003 := @g_vex z
  have p0004 := @g_vex x
  have p0005 := @g_opelssetsn (.cv z) (.cv x) p0003 p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
      p0005
  have p0006 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0002
      p0006_e01_recanon
  have p0007 := @g_otelins2 (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) p0004
  have p0008 := @g_opelssetsn (.cv z) (.cv y) p0003 p0001
  have p0009_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
      p0008
  have p0009 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y) p0007
      p0009_e01_recanon
  have p0010 :=
    @g_lnanbi12ni
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)))
      (.objMem z x)
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.objMem z y) p0006 p0009
  have p0011 :=
    @g_eldif (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))
      (syn_cins2 (syn_csset))
  have p0012 := @g_eldif (.cv z) (.cv x) (.cv y)
  have p0013_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cdif (.cv x) (.cv y)))
        (syn_wa (.objMem z x) (.neg (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
          (syn_cins3 (syn_csset))) (.neg
          (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
            (syn_cins2 (syn_csset)))))
      (syn_wa (.objMem z x) (.neg (.objMem z y)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
        (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))
      (.classMem (.cv z) (syn_cdif (.cv x) (.cv y))) p0010 p0011 p0013_e02_recanon
  have p0014 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv)
      (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))
      (syn_cdif (.cv x) (.cv y)) dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008
      dv_cache_0009 p0013
  have p0015 :=
    @g_eqtr4i (syn_clndifop)
      (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cdif (.cv x) (.cv y)))
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))) (syn_c1c)))
      p0000 p0014
  have p0016 := @g_vvex
  have p0018 := @g_ssetex
  have p0019 := @g_ins3ex (syn_csset) p0018
  have p0021 := @g_ins2ex (syn_csset) p0018
  have p0022 := @g_difex (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)) p0019 p0021
  have p0023 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv)
      (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))) p0016 p0016 p0022
  have p0024 :=
    @g_eqeltri (syn_clndifop)
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))) (syn_c1c)))
      (syn_cvv) p0015 p0023
  exact p0024

@[expose]
noncomputable def g_ln1stfn : Nominal.NPrf (syn_wfn (syn_c1st) (syn_cvv)) :=
  by
  have p0000 := @g_n_1stfo
  have p0001 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ln2ndfn : Nominal.NPrf (syn_wfn (syn_c2nd) (syn_cvv)) :=
  by
  have p0000 := @g_n_2ndfo
  have p0001 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_lnpwasymfnfn : Nominal.NPrf (syn_wfn (syn_clnpwasymfn) (syn_cvv)) :=
  by
  have p0000 := @g_fnlndifop
  have p0001 := @g_n_1stfo
  have p0002 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_imageswapfn
  have p0008 := @g_fncovv (syn_cimage (syn_cswap)) (syn_c1st) p0004 p0003
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0003 p0008
  have p0010 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @g_inidm (syn_cvv)
  have p0013 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0012
  have p0014 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      p0011 p0013
  have p0015 :=
    @g_fncovv (syn_clndifop)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0000 p0014
  have p0016 := (Nominal.classEqRefl (syn_clnpwasymfn))
  have p0017 :=
    @g_fneq1i (syn_cvv) (syn_clnpwasymfn)
      (syn_ccom (syn_clndifop)
        (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
      p0016
  have p0018 :=
    @g_mpbir (syn_wfn (syn_clnpwasymfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop)
          (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv))
      p0015 p0017
  exact p0018

@[expose]
noncomputable def g_lnpwasymfnex : Nominal.NPrf (.classMem (syn_clnpwasymfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwasymfn))
  have p0001 := @g_lndifopex
  have p0002 := @g_n_1stex
  have p0003 := @g_swapex
  have p0004 := @g_imageex (syn_cswap) p0003
  have p0006 := @g_coex (syn_cimage (syn_cswap)) (syn_c1st) p0004 p0002
  have p0007 :=
    @g_txpex (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) p0002 p0006
  have p0008 :=
    @g_coex (syn_clndifop)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0001 p0007
  have p0009 :=
    @g_eqeltri (syn_clnpwasymfn)
      (syn_ccom (syn_clndifop)
        (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
      (syn_cvv) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_lnpwasymfnval (D : Class) (R : Class)
    (hyp_lnpwasymfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwasymfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwasymfn) (syn_cop R D)) (syn_cdif R (syn_ccnv R))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwasymfn))
  have p0001 :=
    @g_fveq1i (syn_cop R D) (syn_clnpwasymfn)
      (syn_ccom (syn_clndifop)
        (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
      p0000
  have p0002 := @g_n_1stfo
  have p0003 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_imageswapfn
  have p0009 := @g_fncovv (syn_cimage (syn_cswap)) (syn_c1st) p0005 p0004
  have p0010 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0004 p0009
  have p0011 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_inidm (syn_cvv)
  have p0014 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0013
  have p0015 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      p0012 p0014
  have p0016 := @g_opex R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0017 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv))
      (.classMem (syn_cop R D) (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_fvco2 (syn_cvv) (syn_cop R D) (syn_clndifop)
      (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0019 := Nominal.mp p0017 p0018
  have p0029 :=
    @g_fvtxpvv (syn_cop R D) (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
      p0004 p0009 p0016
  have p0030 := @g_opfv1st R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0035 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0004
      p0016
  have p0036 := @g_fvco2 (syn_cvv) (syn_cop R D) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0037 := Nominal.mp p0035 p0036
  have p0039 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop R D)) R (syn_cimage (syn_cswap)) p0030
  have p0040 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_c1st) (syn_cop R D)))
      (syn_cfv (syn_cimage (syn_cswap)) R) p0037 p0039
  have p0041 := @g_eqid (syn_cima (syn_cswap) R)
  have p0042 := @g_swapex
  have p0043 := @g_imaex (syn_cswap) R p0042 hyp_lnpwasymfnval_1
  have p0044 :=
    @g_brimage R (syn_cima (syn_cswap) R) (syn_cswap) hyp_lnpwasymfnval_1 p0043
  have p0045 :=
    @g_mpbir (syn_wbr R (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) R))
      (.classEq (syn_cima (syn_cswap) R) (syn_cima (syn_cswap) R)) p0041 p0044
  have p0047 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (.classMem R (syn_cvv)) p0005
      hyp_lnpwasymfnval_1
  have p0048 := @g_fnbrfvb (syn_cvv) R (syn_cima (syn_cswap) R) (syn_cimage (syn_cswap))
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_cima (syn_cswap) R))
      (syn_wbr R (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) R)) p0045 p0049
  have p0051 := @g_dfcnv2 R
  have p0052 :=
    @g_eqtr4i (syn_cfv (syn_cimage (syn_cswap)) R) (syn_cima (syn_cswap) R) (syn_ccnv R)
      p0050 p0051
  have p0053 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D))
      (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R) p0040 p0052
  have p0054 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop R D)) R
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D)) (syn_ccnv R)
      p0030 p0053
  have p0055 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
        (syn_cop R D))
      (syn_cop (syn_cfv (syn_c1st) (syn_cop R D))
        (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D)))
      (syn_cop R (syn_ccnv R)) p0029 p0054
  have p0056 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
        (syn_cop R D))
      (syn_cop R (syn_ccnv R)) (syn_clndifop) p0055
  have p0057 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clndifop)
          (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D))
      (syn_cfv (syn_clndifop)
        (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
          (syn_cop R D)))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_ccnv R))) p0019 p0056
  have p0058 := (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_ccnv R)))
  have p0059 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_ccnv R))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_ccnv R))) p0058
  have p0060 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clndifop)
          (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_ccnv R)))
      (syn_co R (syn_clndifop) (syn_ccnv R)) p0057 p0059
  have p0061 := @g_cnvex R hyp_lnpwasymfnval_1
  have p0062 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv))
      hyp_lnpwasymfnval_1 p0061
  have p0063 := @g_lndifopvalg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0064 := Nominal.mp p0062 p0063
  have p0065 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clndifop)
          (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D))
      (syn_co R (syn_clndifop) (syn_ccnv R)) (syn_cdif R (syn_ccnv R)) p0060 p0064
  have p0066 :=
    @g_eqtri (syn_cfv (syn_clnpwasymfn) (syn_cop R D))
      (syn_cfv (syn_ccom (syn_clndifop)
          (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D))
      (syn_cdif R (syn_ccnv R)) p0001 p0065
  exact p0066

@[expose]
noncomputable def g_tc3lecan (M : Class) (N : Class)
    (hyp_tc3lecb_1 : Nominal.NPrf (.classMem M (syn_cncs)))
    (hyp_tc3lecb_2 : Nominal.NPrf (.classMem N (syn_cncs))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
        (syn_wbr M (syn_clec) N)) :=
  by
  have p0000 :=
    @g_pm3_2i (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) hyp_tc3lecb_1
      hyp_tc3lecb_2
  have p0001 := @g_tlecg M N
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_tccl M
  have p0004 := Nominal.mp hyp_tc3lecb_1 p0003
  have p0005 := @g_tccl N
  have p0006 := Nominal.mp hyp_tc3lecb_2 p0005
  have p0007 :=
    @g_pm3_2i (.classMem (syn_ctc M) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0004
      p0006
  have p0008 := @g_tlecg (syn_ctc M) (syn_ctc N)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))
      (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) p0002 p0009
  have p0013 := @g_tccl (syn_ctc M)
  have p0014 := Nominal.mp p0004 p0013
  have p0017 := @g_tccl (syn_ctc N)
  have p0018 := Nominal.mp p0006 p0017
  have p0019 :=
    @g_pm3_2i (.classMem (syn_ctc (syn_ctc M)) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0014 p0018
  have p0020 := @g_tlecg (syn_ctc (syn_ctc M)) (syn_ctc (syn_ctc N))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @g_bitri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N)))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
      p0010 p0021
  have p0023 :=
    @g_biimpri (syn_wbr M (syn_clec) N)
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))
      p0022
  exact p0023

@[expose]
noncomputable def g_fdifssa (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv) : Nominal.NPrf (syn_wss (syn_cfdif R A B) A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
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
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0013 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0014 : d ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdif x y A B R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_ssrab2
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))) d
      A dv_cache_0003
  have p0002 :=
    @g_eqsstri (syn_cfdif R A B)
      (syn_crab d A
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fdordwe2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv) (hyp_fdordwe2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdordwe2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdordwe2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (syn_wbr (syn_cfdord R A B) (syn_cwe) (syn_cfdif R A B))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 := @g_id (syn_wbr R (syn_cwe) A)
  have p0001 := @g_fdifssa A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 := @g_a1i (syn_wss (syn_cfdif R A B) A) (syn_wbr R (syn_cwe) A) p0001
  have p0003 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdordwe2_1
      hyp_fdordwe2_2 hyp_fdordwe2_3
  have p0004 :=
    @g_werestrndv (syn_wbr R (syn_cwe) A) (syn_cfdif R A B) A R p0000 p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cfdord R A B))
  have p0006 :=
    @g_breq1i (syn_cfdord R A B) (syn_cin R (syn_cxp (syn_cfdif R A B) (syn_cfdif R A B)))
      (syn_cfdif R A B) (syn_cwe) p0005
  have p0007 :=
    @g_sylibr (syn_wbr R (syn_cwe) A)
      (syn_wbr (syn_cin R (syn_cxp (syn_cfdif R A B) (syn_cfdif R A B))) (syn_cwe)
        (syn_cfdif R A B))
      (syn_wbr (syn_cfdord R A B) (syn_cwe) (syn_cfdif R A B)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_ncpw1pw2 (A : Class)
    (hyp_ncpw1pw2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw A))))
        (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 A))))) :=
  by
  have p0000 := @g_pwex A hyp_ncpw1pw2_1
  have p0001 := @g_enpw1pw (syn_cpw A) p0000
  have p0002 := @g_enpw1pw A hyp_ncpw1pw2_1
  have p0003 := @g_enpw (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_pm3_2i
      (syn_wbr (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cen) (syn_cpw (syn_cpw1 (syn_cpw A))))
      (syn_wbr (syn_cpw (syn_cpw1 (syn_cpw A))) (syn_cen) (syn_cpw (syn_cpw (syn_cpw1 A))))
      p0001 p0004
  have p0006 :=
    @g_entr (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cpw (syn_cpw1 (syn_cpw A)))
      (syn_cpw (syn_cpw (syn_cpw1 A)))
  have p0007 := Nominal.mp p0005 p0006
  have p0009 := @g_pwex (syn_cpw A) p0000
  have p0010 := @g_pw1ex (syn_cpw (syn_cpw A)) p0009
  have p0011 :=
    @g_eqnc (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cpw (syn_cpw (syn_cpw1 A))) p0010
  have p0012 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw A))))
        (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 A)))))
      (syn_wbr (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cen) (syn_cpw (syn_cpw (syn_cpw1 A))))
      p0007 p0011
  exact p0012

@[expose]
noncomputable def g_tc3nc (A : Class)
    (hyp_tc3nc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_cnc A))))
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))) :=
  by
  have p0000 := @g_tc2nc A hyp_tc3nc_1
  have p0001 := @g_tceq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_pw1ex A hyp_tc3nc_1
  have p0004 := @g_pw1ex (syn_cpw1 A) p0003
  have p0005 := @g_tcnc (syn_cpw1 (syn_cpw1 A)) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_cnc A))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 A))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_kqlefintcb (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wb (syn_wbr M (syn_ckqrel (syn_clefin)) N)
          (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N)))) :=
  by
  have p0000 := @g_kqlefinbr M N (syn_cnnc) (syn_cnnc)
  have p0001 := @g_tfinlefin M N
  have p0002 :=
    @g_bitrd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wbr M (syn_ckqrel (syn_clefin)) N) (.classMem (syn_copk M N) (syn_clefin))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) p0000 p0001
  have p0003 := @g_simpl (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
  have p0004 := @g_nntctfin M
  have p0005 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem M (syn_cnnc)) (.classEq (syn_ctc M) (syn_ctfin M)) p0003 p0004
  have p0006 := @g_simpr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
  have p0007 := @g_nntctfin N
  have p0008 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem N (syn_cnnc)) (.classEq (syn_ctc N) (syn_ctfin N)) p0006 p0007
  have p0009 :=
    @g_opkeq12d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_ctc M)
      (syn_ctfin M) (syn_ctc N) (syn_ctfin N) p0005 p0008
  have p0010 :=
    @g_eleq1d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_copk (syn_ctc M) (syn_ctc N)) (syn_copk (syn_ctfin M) (syn_ctfin N))
      (syn_clefin) p0009
  have p0011 :=
    @g_bicomd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) p0010
  have p0012 :=
    @g_bitrd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wbr M (syn_ckqrel (syn_clefin)) N)
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin))
      (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)) p0002 p0011
  have p0014 := @g_nntccl M
  have p0015 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem M (syn_cnnc)) (.classMem (syn_ctc M) (syn_cnnc)) p0003 p0014
  have p0017 := @g_nntccl N
  have p0018 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem N (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)) p0006 p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_ctc M) (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)) p0015 p0018
  have p0020 := @g_kqlefinbr (syn_ctc M) (syn_ctc N) (syn_cnnc) (syn_cnnc)
  have p0021 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (.classMem (syn_ctc M) (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)))
      (syn_wb (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N))
        (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)))
      p0019 p0020
  have p0022 :=
    @g_bicomd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N))
      (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)) p0021
  have p0023 :=
    @g_bitrd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wbr M (syn_ckqrel (syn_clefin)) N)
      (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin))
      (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N)) p0012 p0022
  exact p0023

@[expose]
noncomputable def g_tcnnresfn :
    Nominal.NPrf
      (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))) :=
  by
  have p0000 := @g_fntcfn
  have p0001 := @g_pw1ss1c (syn_cnnc)
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (syn_wss (syn_cpw1 (syn_cnnc)) (syn_c1c))
      p0000 p0001
  have p0003 := @g_fnssres (syn_c1c) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0004 := Nominal.mp p0002 p0003
  exact p0004

@[expose]
noncomputable def g_tcnnex : Nominal.NPrf (.classMem (syn_ctcnn) (syn_cvv)) :=
  by
  have p0000 := @g_tcfnex
  have p0001 := @g_nncex
  have p0002 := @g_pw1ex (syn_cnnc) p0001
  have p0003 := @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0000 p0002
  have p0004 := @g_rnex (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0003
  have p0005 := (Nominal.classEqRefl (syn_ctcnn))
  have p0006 :=
    @g_eleq1i (syn_ctcnn) (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cvv)
      p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_ctcnn) (syn_cvv))
      (.classMem (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cvv)) p0004
      p0006
  exact p0007

@[expose]
noncomputable def g_eltcnn (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_ctcnn)) (syn_wrex q (syn_cpw1 (syn_cnnc))
          (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))) :=
  by
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_ctcnn))
  have p0001 :=
    @g_eleq2i (syn_ctcnn) (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) A p0000
  have p0002 := @g_fntcfn
  have p0003 := @g_pw1ss1c (syn_cnnc)
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (syn_wss (syn_cpw1 (syn_cnnc)) (syn_c1c))
      p0002 p0003
  have p0005 := @g_fnssres (syn_c1c) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_fvelrnb q (syn_cpw1 (syn_cnnc)) A (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_bitri (.classMem A (syn_ctcnn))
      (.classMem A (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      p0001 p0008
  exact p0009

@[expose]
noncomputable def g_tcfnfvcl (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc B))) :=
  by
  let proofSupport : Finset Var := B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 :
    x ∉ ((Wff.classEq (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_x_not_B, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_sneq (.cv x) B
  have p0001 :=
    @g_fveq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ctcfn) p0000
  have p0002 := @g_tceq (.cv x) B
  have p0003 :=
    @g_eqeq12d (.classEq (.cv x) B) (syn_cfv (syn_ctcfn) (syn_csn (.cv x)))
      (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc (.cv x)) (syn_ctc B) p0001 p0002
  have p0004 := @g_vex x
  have p0005 := @g_tcfnfv (.cv x) p0004
  have p0006 :=
    @g_vtoclg (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv x))) (syn_ctc (.cv x)))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc B)) x B (syn_cvv) dv_cache_0001
      dv_cache_0002 p0003 p0005
  exact p0006

@[expose]
noncomputable def g_tcnnssnn : Nominal.NPrf (syn_wss (syn_ctcnn) (syn_cnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_q_ne_p : q ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : p ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Wff.classMem (.cv q) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_ctcnn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_eltcnn (.cv q) p dv_cache_0001
  have p0001 :=
    @g_biimpi (.classMem (.cv q) (syn_ctcnn))
      (syn_wrex p (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      p0000
  have p0002 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))
  have p0003 := @g_hnwpw1argcl (syn_cnnc) p
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cnnc))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0005 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv p)) (syn_cnnc))
      p0002 p0005
  have p0007 := @g_nntccl (syn_cuni (.cv p))
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (.classMem (syn_cuni (.cv p)) (syn_cnnc))
      (.classMem (syn_ctc (syn_cuni (.cv p))) (syn_cnnc)) p0006 p0007
  have p0010 := @g_fvres (.cv p) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0012 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cnnc))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0013 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0003 p0012
  have p0014 :=
    @g_fveq2d (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.cv p)
      (syn_csn (syn_cuni (.cv p))) (syn_ctcfn) p0013
  have p0015 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_cfv (syn_ctcfn) (.cv p)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p))))
      p0010 p0014
  have p0019 := @g_elex (syn_cuni (.cv p)) (syn_cnnc)
  have p0020 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
      p0005 p0019
  have p0021 := @g_tcfnfvcl (syn_cuni (.cv p))
  have p0022 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classMem (syn_cuni (.cv p)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p))))
      p0020 p0021
  have p0023 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p)))
      p0015 p0022
  have p0024 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
        (syn_ctc (syn_cuni (.cv p))))
      p0002 p0023
  have p0025 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))
  have p0026 :=
    @g_eqtr3d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_ctc (syn_cuni (.cv p))) (.cv q) p0024 p0025
  have p0027 :=
    @g_eleq1d
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (syn_ctc (syn_cuni (.cv p))) (.cv q) (syn_cnnc) p0026
  have p0028 :=
    @g_mpbid
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (.classMem (syn_ctc (syn_cuni (.cv p))) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))
      p0008 p0027
  have p0029 :=
    @g_rexlimiva
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))
      (.classMem (.cv q) (syn_cnnc)) p (syn_cpw1 (syn_cnnc)) dv_cache_0002 p0028
  have p0030 :=
    @g_syl (.classMem (.cv q) (syn_ctcnn))
      (syn_wrex p (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)))
      (.classMem (.cv q) (syn_cnnc)) p0001 p0029
  have p0031 := @g_ssriv q (syn_ctcnn) (syn_cnnc) dv_cache_0003 dv_cache_0004 p0030
  exact p0031

@[expose]
noncomputable def g_nntcsuc (N : Class) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc))
        (.classEq (syn_ctc (syn_cplc N (syn_c1c))) (syn_cplc (syn_ctc N) (syn_c1c)))) :=
  by
  have p0000 := @g_nnnc N
  have p0001 := @g_n_1cnc
  have p0002 := @g_a1i (.classMem (syn_c1c) (syn_cncs)) (.classMem N (syn_cnnc)) p0001
  have p0003 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem N (syn_cncs))
      (.classMem (syn_c1c) (syn_cncs)) p0000 p0002
  have p0004 := @g_tcdi N (syn_c1c)
  have p0005 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wa (.classMem N (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)))
      (.classEq (syn_ctc (syn_cplc N (syn_c1c))) (syn_cplc (syn_ctc N) (syn_ctc (syn_c1c))))
      p0003 p0004
  have p0006 := @g_tc1c
  have p0007 :=
    @g_a1i (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) (.classMem N (syn_cnnc)) p0006
  have p0008 :=
    @g_addceq2d (.classMem N (syn_cnnc)) (syn_ctc (syn_c1c)) (syn_c1c) (syn_ctc N) p0007
  have p0009 :=
    @g_eqtrd (.classMem N (syn_cnnc)) (syn_ctc (syn_cplc N (syn_c1c)))
      (syn_cplc (syn_ctc N) (syn_ctc (syn_c1c))) (syn_cplc (syn_ctc N) (syn_c1c)) p0005
      p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nntctcnn (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem (syn_ctc N) (syn_ctcnn))) :=
  by
  let proofSupport : Finset Var := N.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ ((syn_csn N)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_q_not_N,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    q ∉
      ((Wff.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N))
          (syn_ctc N))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_q_not_N, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_ctc N)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_q_not_N,
          not_false_eq_true])
  have p0000 := @g_snelpw1 N (syn_cnnc)
  have p0001 :=
    @g_biimpri (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classMem N (syn_cnnc))
      p0000
  have p0004 := @g_fvres (syn_csn N) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0005 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N))
        (syn_cfv (syn_ctcfn) (syn_csn N)))
      p0001 p0004
  have p0006 := @g_id (.classMem N (syn_cnnc))
  have p0007 := @g_elex N (syn_cnnc)
  have p0008 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem N (syn_cvv)) p0006
      p0007
  have p0009 := @g_tcfnfvcl N
  have p0010 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem N (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn N)) (syn_ctc N)) p0008 p0009
  have p0011 :=
    @g_eqtrd (.classMem N (syn_cnnc))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N))
      (syn_cfv (syn_ctcfn) (syn_csn N)) (syn_ctc N) p0005 p0010
  have p0012 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N))
      p0001 p0011
  have p0013 := @g_id (.classEq (.cv q) (syn_csn N))
  have p0014 :=
    @g_fveq2d (.classEq (.cv q) (syn_csn N)) (.cv q) (syn_csn N)
      (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0013
  have p0015 :=
    @g_eqeq1d (.classEq (.cv q) (syn_csn N))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N) p0014
  have p0016 :=
    @g_rspcev
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N)) (syn_ctc N))
      q (syn_csn N) (syn_cpw1 (syn_cnnc)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wa (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_csn N))
          (syn_ctc N)))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N)))
      p0012 p0016
  have p0018 := @g_eltcnn (syn_ctc N) q dv_cache_0004
  have p0019 :=
    @g_biimpri (.classMem (syn_ctc N) (syn_ctcnn))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N)))
      p0018
  have p0020 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc N)))
      (.classMem (syn_ctc N) (syn_ctcnn)) p0017 p0019
  exact p0020

@[expose]
noncomputable def g_tcnnsuc (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_ctcnn)) (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn))) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Wff.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union,
          fresh_q_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_eltcnn A q dv_cache_0001
  have p0001 :=
    @g_biimpi (.classMem A (syn_ctcnn))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      p0000
  have p0002 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0003 := @g_hnwpw1argcl (syn_cnnc) q
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0005 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      p0002 p0005
  have p0007 := @g_peano2 (syn_cuni (.cv q))
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cuni (.cv q)) (syn_c1c)) (syn_cnnc)) p0006 p0007
  have p0009 := @g_nntctcnn (syn_cplc (syn_cuni (.cv q)) (syn_c1c))
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (syn_cplc (syn_cuni (.cv q)) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_ctcnn)) p0008
      p0009
  have p0016 := @g_nntcsuc (syn_cuni (.cv q))
  have p0017 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c)))
        (syn_cplc (syn_ctc (syn_cuni (.cv q))) (syn_c1c)))
      p0006 p0016
  have p0019 := @g_fvres (.cv q) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0020 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
        (syn_cfv (syn_ctcfn) (.cv q)))
      p0002 p0019
  have p0023 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0024 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0003 p0023
  have p0025 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.cv q)
      (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0024
  have p0026 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_ctcfn) (.cv q))
        (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))))
      p0002 p0025
  have p0027 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q))))
      p0020 p0026
  have p0032 := @g_elex (syn_cuni (.cv q)) (syn_cnnc)
  have p0033 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
      p0005 p0032
  have p0034 := @g_tcfnfvcl (syn_cuni (.cv q))
  have p0035 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))))
      p0033 p0034
  have p0036 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))))
      p0002 p0035
  have p0037 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))
      p0027 p0036
  have p0038 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
  have p0039 :=
    @g_eqtr3d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_ctc (syn_cuni (.cv q))) A p0037 p0038
  have p0040 :=
    @g_addceq1d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (syn_ctc (syn_cuni (.cv q))) A (syn_c1c) p0039
  have p0041 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c)))
      (syn_cplc (syn_ctc (syn_cuni (.cv q))) (syn_c1c)) (syn_cplc A (syn_c1c)) p0017 p0040
  have p0042 :=
    @g_eleq1d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_cplc A (syn_c1c)) (syn_ctcnn)
      p0041
  have p0043 :=
    @g_mpbid
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (syn_ctc (syn_cplc (syn_cuni (.cv q)) (syn_c1c))) (syn_ctcnn))
      (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn)) p0010 p0042
  have p0044 :=
    @g_rexlimiva
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)
      (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn)) q (syn_cpw1 (syn_cnnc)) dv_cache_0002
      p0043
  have p0045 :=
    @g_syl (.classMem A (syn_ctcnn))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))
      (.classMem (syn_cplc A (syn_c1c)) (syn_ctcnn)) p0001 p0044
  exact p0045

@[expose]
noncomputable def g_nntcnn (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_ctcnn))) :=
  by
  let proofSupport : Finset Var := N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ctcnn)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_N, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (.cv y) (syn_ctcnn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) (syn_ctcnn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_c0c) (syn_ctcnn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem N (syn_ctcnn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union,
          fresh_x_not_N, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_tcnnex
  have p0001 := @g_abid2 x (syn_ctcnn) dv_cache_0001
  have p0002 :=
    @g_eleq1i (.cab x (.classMem (.cv x) (syn_ctcnn))) (syn_ctcnn) (syn_cvv) p0001
  have p0003 :=
    @g_mpbir (.classMem (.cab x (.classMem (.cv x) (syn_ctcnn))) (syn_cvv))
      (.classMem (syn_ctcnn) (syn_cvv)) p0000 p0002
  have p0004 := @g_id (.classEq (.cv x) (syn_c0c))
  have p0005 := @g_eleq1d (.classEq (.cv x) (syn_c0c)) (.cv x) (syn_c0c) (syn_ctcnn) p0004
  have p0006 := @g_id (.classEq (.cv x) (.cv y))
  have p0007 := @g_eleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) (syn_ctcnn) p0006
  have p0008 := @g_id (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0009 :=
    @g_eleq1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.cv x)
      (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn) p0008
  have p0010 := @g_id (.classEq (.cv x) N)
  have p0011 := @g_eleq1d (.classEq (.cv x) N) (.cv x) N (syn_ctcnn) p0010
  have p0012 := @g_peano1
  have p0013 := @g_nntctcnn (syn_c0c)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @g_tc0c
  have p0016 := @g_eleq1i (syn_ctc (syn_c0c)) (syn_c0c) (syn_ctcnn) p0015
  have p0017 :=
    @g_mpbi (.classMem (syn_ctc (syn_c0c)) (syn_ctcnn)) (.classMem (syn_c0c) (syn_ctcnn))
      p0014 p0016
  have p0018 := @g_tcnnsuc (.cv y)
  have p0019 :=
    @g_a1i
      (.imp (.classMem (.cv y) (syn_ctcnn))
        (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn)))
      (.classMem (.cv y) (syn_cnnc)) p0018
  have p0020_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y)
        (syn_wb (.classMem (.cv x) (syn_ctcnn)) (.classMem (.cv y) (syn_ctcnn)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctcnn syn_crn syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop
          syn_cun syn_cnin syn_wnan syn_ccompl syn_cvv syn_cres syn_cin syn_cxp syn_copab
          syn_ctcfn syn_cmpt syn_c1c syn_ctc syn_cio syn_cuni syn_csn syn_cpw1 syn_cnnc
          syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0020 :=
    @g_finds (.classMem (.cv x) (syn_ctcnn)) (.classMem (syn_c0c) (syn_ctcnn))
      (.classMem (.cv y) (syn_ctcnn)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_ctcnn))
      (.classMem N (syn_ctcnn)) x y N dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0003 p0005
      p0020_e02_recanon p0009 p0011 p0017 p0019
  exact p0020

@[expose]
noncomputable def g_tcnnfo :
    Nominal.NPrf
      (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  have dv_cache_0001 : q ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_ctcnn)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_tcnnresfn
  have p0001 := (Nominal.classEqRefl (syn_ctcnn))
  have p0002 :=
    @g_eqcomi (syn_ctcnn) (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) p0001
  have p0003 := @g_tcnnssnn
  have p0004 := @g_nntcnn (.cv q)
  have p0005 := @g_ssriv q (syn_cnnc) (syn_ctcnn) dv_cache_0001 dv_cache_0002 p0004
  have p0006 := @g_eqssi (syn_ctcnn) (syn_cnnc) p0003 p0005
  have p0007 :=
    @g_eqtri (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_ctcnn) (syn_cnnc)
      p0002 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cnnc)) p0000
      p0007
  have p0009 :=
    (Nominal.biimpRefl
      (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)))
  have p0010 :=
    @g_mpbir
      (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (syn_wa (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)))
        (.classEq (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cnnc)))
      p0008 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_tcnnf1 :
    Nominal.NPrf
      (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : q ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cnnc)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 := @g_tcnnfo
  have p0001 :=
    @g_fof (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
        (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0004 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
      (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) p0003 p0004
  have p0006 := @g_hnwpw1argcl (syn_cnnc) p
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      p0005 p0006
  have p0008 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cnnc))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0007 p0008
  have p0013 := @g_fvres (.cv p) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
        (syn_cfv (syn_ctcfn) (.cv p)))
      p0005 p0013
  have p0022 :=
    @g_fveq2d
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_ctcfn) p0009
  have p0023 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_cfv (syn_ctcfn) (.cv p)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p))))
      p0014 p0022
  have p0029 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cnnc))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0007 p0029
  have p0031 := @g_elex (syn_cuni (.cv p)) (syn_cnnc)
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
      p0030 p0031
  have p0033 := @g_tcfnfvcl (syn_cuni (.cv p))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p))))
      p0032 p0033
  have p0035 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p)))
      p0023 p0034
  have p0036 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_ctc (syn_cuni (.cv p))) p0035
  have p0037 :=
    @g_simpr
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
        (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0038 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_ctc (syn_cuni (.cv p)))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) p0036 p0037
  have p0040 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) p0003 p0040
  have p0042 := @g_fvres (.cv q) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
        (syn_cfv (syn_ctcfn) (.cv q)))
      p0041 p0042
  have p0047 := @g_hnwpw1argcl (syn_cnnc) q
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0041 p0047
  have p0049 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0048 p0049
  have p0051 :=
    @g_fveq2d
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0050
  have p0052 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q))))
      p0043 p0051
  have p0058 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0048 p0058
  have p0060 := @g_elex (syn_cuni (.cv q)) (syn_cnnc)
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
      p0059 p0060
  have p0062 := @g_tcfnfvcl (syn_cuni (.cv q))
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))))
      p0061 p0062
  have p0064 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))
      p0052 p0063
  have p0065 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_ctc (syn_cuni (.cv p)))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_ctc (syn_cuni (.cv q))) p0038 p0064
  have p0073 := @g_nnnc (syn_cuni (.cv p))
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_cuni (.cv p)) (syn_cncs))
      p0030 p0073
  have p0082 := @g_nnnc (syn_cuni (.cv q))
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cncs))
      p0059 p0082
  have p0084 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cncs))
      p0074 p0083
  have p0085 := @g_tc11 (syn_cuni (.cv p)) (syn_cuni (.cv q))
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs))
        (.classMem (syn_cuni (.cv q)) (syn_cncs)))
      (syn_wb (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))))
        (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))))
      p0084 p0085
  have p0087 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))))
      (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0065 p0086
  have p0088 :=
    @g_sneqd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0087
  have p0089 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cuni (.cv q))) p0009 p0088
  have p0097 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) p0050
  have p0098 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
          (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
        (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.cv p) (syn_csn (syn_cuni (.cv q))) (.cv q) p0089 p0097
  have p0099 :=
    @g_ex
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
        (.classMem (.cv q) (syn_cpw1 (syn_cnnc))))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
        (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
      (.classEq (.cv p) (.cv q)) p0098
  have p0100 :=
    @g_ex (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
        (.classEq (.cv p) (.cv q)))
      p0099
  have p0101 :=
    @g_ralrimiv (.classMem (.cv p) (syn_cpw1 (syn_cnnc)))
      (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
          (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
        (.classEq (.cv p) (.cv q)))
      q (syn_cpw1 (syn_cnnc)) dv_cache_0001 p0100
  have p0102 :=
    @g_rgen
      (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp
          (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
            (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
          (.classEq (.cv p) (.cv q))))
      p (syn_cpw1 (syn_cnnc)) p0101
  have p0103 :=
    @g_pm3_2i
      (syn_wf (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (syn_wral p (syn_cpw1 (syn_cnnc)) (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp
            (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
              (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
            (.classEq (.cv p) (.cv q)))))
      p0002 p0102
  have p0104 :=
    @g_dff13 p q (syn_cpw1 (syn_cnnc)) (syn_cnnc)
      (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0105_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))
          (syn_cnnc)) (syn_wa
          (syn_wf (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
          (syn_wral p (syn_cpw1 (syn_cnnc)) (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp
                (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
                  (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
                (.classEq (.cv p) (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cres syn_ctcfn syn_cmpt
          syn_c1c syn_ctc syn_cio syn_cuni syn_csn syn_cpw1 syn_cnnc syn_cint
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0104
  have p0105 :=
    @g_mpbir
      (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (syn_wa (syn_wf (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))
          (syn_cnnc)) (syn_wral p (syn_cpw1 (syn_cnnc)) (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp
              (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p))
                (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
              (.classEq (.cv p) (.cv q))))))
      p0103 p0105_e01_recanon
  exact p0105

@[expose]
noncomputable def g_tcnnf1o :
    Nominal.NPrf
      (syn_wf1o (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))
        (syn_cnnc)) :=
  by
  have p0000 := @g_tcnnf1
  have p0001 := @g_tcnnfo
  have p0002 :=
    @g_pm3_2i
      (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      p0000 p0001
  have p0003 :=
    (Nominal.biimpRefl
      (syn_wf1o (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)))
  have p0004 :=
    @g_mpbir
      (syn_wf1o (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (syn_wa (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))
          (syn_cnnc))
        (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)))
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_nntcpreim (x : Var) (P : Class) (dv_P_x : x ∉ P.fv) :
    Nominal.NPrf
      (.imp (.classMem P (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ P.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have fresh_q_not_P : q ∉ P.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : q ∉ (P).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_P, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cuni (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_q,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (syn_ctc (syn_cuni (.cv q))) P)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, dv_P_x, or_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_P, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_tcnnfo
  have p0001 :=
    @g_a1i
      (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (.classMem P (syn_cnnc)) p0000
  have p0002 := @g_id (.classMem P (syn_cnnc))
  have p0003 :=
    @g_jca (.classMem P (syn_cnnc))
      (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))
      (.classMem P (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_foelrn q (syn_cpw1 (syn_cnnc)) (syn_cnnc) P
      (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_syl (.classMem P (syn_cnnc))
      (syn_wa (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))
          (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      p0003 p0004
  have p0006 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0007 := @g_hnwpw1argcl (syn_cnnc) q
  have p0008 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0007 p0008
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      p0006 p0009
  have p0011 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0013 := @g_fvres (.cv q) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0014 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
        (syn_cfv (syn_ctcfn) (.cv q)))
      p0006 p0013
  have p0017 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0018 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0007 p0017
  have p0019 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0006 p0018
  have p0020 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0019
  have p0021 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q))))
      p0014 p0020
  have p0027 := @g_elex (syn_cuni (.cv q)) (syn_cnnc)
  have p0028 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
      p0010 p0027
  have p0029 := @g_tcfnfvcl (syn_cuni (.cv q))
  have p0030 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))))
      p0028 p0029
  have p0031 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))
      p0021 p0030
  have p0032 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))
      (syn_ctc (syn_cuni (.cv q))) p0011 p0031
  have p0033 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      P (syn_ctc (syn_cuni (.cv q))) p0032
  have p0034 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (syn_ctc (syn_cuni (.cv q))) P)
      p0010 p0033
  have p0035 := @g_tceq (.cv x) (syn_cuni (.cv q))
  have p0036 :=
    @g_eqeq1d (.classEq (.cv x) (syn_cuni (.cv q))) (syn_ctc (.cv x))
      (syn_ctc (syn_cuni (.cv q))) P p0035
  have p0037 :=
    @g_rspcev (.classEq (syn_ctc (.cv x)) P) (.classEq (syn_ctc (syn_cuni (.cv q))) P) x
      (syn_cuni (.cv q)) (syn_cnnc) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0036
  have p0038 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc))
        (.classEq (syn_ctc (syn_cuni (.cv q))) P))
      (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P)) p0034 p0037
  have p0039 :=
    @g_rexlimiva
      (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
      (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P)) q (syn_cpw1 (syn_cnnc))
      dv_cache_0008 p0038
  have p0040 :=
    @g_syl (.classMem P (syn_cnnc))
      (syn_wrex q (syn_cpw1 (syn_cnnc))
        (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))))
      (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P)) p0005 p0039
  exact p0040

@[expose]
noncomputable def g_pwpullex (R : Class) (F : Class)
    (hyp_pwpullex_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_pwpullex_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpwpull F R) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cpwpull F R))
  have p0001 := @g_cnvex F hyp_pwpullex_1
  have p0002 := @g_coex (syn_ccnv F) R p0001 hyp_pwpullex_2
  have p0003 := @g_coex (syn_ccom (syn_ccnv F) R) F p0002 hyp_pwpullex_1
  have p0004 :=
    @g_eqeltri (syn_cpwpull F R) (syn_ccom (syn_ccom (syn_ccnv F) R) F) (syn_cvv) p0000
      p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ellntpcndv (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv)
    (hyp_ellntpcndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ellntpcndv_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_ellntpcndv_3 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop R D) (syn_clntpc A)) (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
              (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classEq D A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((syn_cop R D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_u_not_R, fresh_u_not_D, or_false, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((syn_wb (.classMem (syn_cop R D) (syn_chwrels))
          (syn_wss (syn_cfv (syn_c1st) (syn_cop R D))
            (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D))
              (syn_cfv (syn_c2nd) (syn_cop R D)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_R, fresh_u_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_clntpc A))
  have p0001 :=
    @g_eleq2i (syn_clntpc A)
      (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A)))
      (syn_cop R D) p0000
  have p0002 :=
    @g_elin (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels))
      (syn_cxp (syn_cvv) (syn_csn A))
  have p0003 := @g_elin (syn_cop R D) (syn_clntp) (syn_chwrels)
  have p0004 := (Nominal.classEqRefl (syn_clntp))
  have p0005 :=
    @g_eleq2i (syn_clntp) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex))
      (syn_cop R D) p0004
  have p0006 := @g_elin (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)
  have p0007 := @g_elin (syn_cop R D) (syn_cref) (syn_ctrans)
  have p0008 := (Nominal.biimpRefl (syn_wbr R (syn_cref) D))
  have p0009 :=
    @g_bicomi (syn_wbr R (syn_cref) D) (.classMem (syn_cop R D) (syn_cref)) p0008
  have p0010 := (Nominal.biimpRefl (syn_wbr R (syn_ctrans) D))
  have p0011 :=
    @g_bicomi (syn_wbr R (syn_ctrans) D) (.classMem (syn_cop R D) (syn_ctrans)) p0010
  have p0012 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cref)) (syn_wbr R (syn_cref) D)
      (.classMem (syn_cop R D) (syn_ctrans)) (syn_wbr R (syn_ctrans) D) p0009 p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans)))
      (syn_wa (.classMem (syn_cop R D) (syn_cref)) (.classMem (syn_cop R D) (syn_ctrans)))
      (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)) p0007 p0012
  have p0014 := (Nominal.biimpRefl (syn_wbr R (syn_cconnex) D))
  have p0015 :=
    @g_bicomi (syn_wbr R (syn_cconnex) D) (.classMem (syn_cop R D) (syn_cconnex)) p0014
  have p0016 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans)))
      (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
      (.classMem (syn_cop R D) (syn_cconnex)) (syn_wbr R (syn_cconnex) D) p0013 p0015
  have p0017 :=
    @g_bitri
      (.classMem (syn_cop R D) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)))
      (syn_wa (.classMem (syn_cop R D) (syn_cin (syn_cref) (syn_ctrans)))
        (.classMem (syn_cop R D) (syn_cconnex)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
        (syn_wbr R (syn_cconnex) D))
      p0006 p0016
  have p0018 :=
    @g_bitri (.classMem (syn_cop R D) (syn_clntp))
      (.classMem (syn_cop R D) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cconnex)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
        (syn_wbr R (syn_cconnex) D))
      p0005 p0017
  have p0019 := @g_opex R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0020 := @g_eleq1 (.cv u) (syn_cop R D) (syn_chwrels)
  have p0021 := @g_fveq2 (.cv u) (syn_cop R D) (syn_c1st)
  have p0022 := @g_fveq2 (.cv u) (syn_cop R D) (syn_c2nd)
  have p0024 :=
    @g_xpeq12d (.classEq (.cv u) (syn_cop R D)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cop R D)) p0022 p0022
  have p0025 :=
    @g_sseq12d (.classEq (.cv u) (syn_cop R D)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c1st) (syn_cop R D))
      (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D)))
      p0021 p0024
  have p0026 :=
    @g_bibi12d (.classEq (.cv u) (syn_cop R D)) (.classMem (.cv u) (syn_chwrels))
      (.classMem (syn_cop R D) (syn_chwrels))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop R D))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D))))
      p0020 p0025
  have p0027 := @g_elhwrrels u
  have p0028 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv u) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wb (.classMem (syn_cop R D) (syn_chwrels))
        (syn_wss (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D))
            (syn_cfv (syn_c2nd) (syn_cop R D)))))
      u (syn_cop R D) (syn_cvv) dv_cache_0001 dv_cache_0002 p0026 p0027
  have p0029 := Nominal.mp p0019 p0028
  have p0030 := @g_opfv1st R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0031 := @g_opfv2nd R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0033 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop R D)) D (syn_cfv (syn_c2nd) (syn_cop R D)) D
      p0031 p0031
  have p0034 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop R D)) R
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D)))
      (syn_cxp D D) p0030 p0033
  have p0035 :=
    @g_bitri (.classMem (syn_cop R D) (syn_chwrels))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop R D))
        (syn_cxp (syn_cfv (syn_c2nd) (syn_cop R D)) (syn_cfv (syn_c2nd) (syn_cop R D))))
      (syn_wss R (syn_cxp D D)) p0029 p0034
  have p0036 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_clntp))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
        (syn_wbr R (syn_cconnex) D))
      (.classMem (syn_cop R D) (syn_chwrels)) (syn_wss R (syn_cxp D D)) p0018 p0035
  have p0037 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels)))
      (syn_wa (.classMem (syn_cop R D) (syn_clntp)) (.classMem (syn_cop R D) (syn_chwrels)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
          (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D)))
      p0003 p0036
  have p0038 := @g_opelxp R D (syn_cvv) (syn_csn A)
  have p0039 :=
    @g_biantrur (.classMem R (syn_cvv)) (.classMem D (syn_csn A)) hyp_ellntpcndv_2
  have p0040 :=
    @g_bicomi (.classMem D (syn_csn A))
      (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_csn A))) p0039
  have p0041 := @g_elsnc2 D A hyp_ellntpcndv_1
  have p0042 :=
    @g_bitri (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_csn A)))
      (.classMem D (syn_csn A)) (.classEq D A) p0040 p0041
  have p0043 :=
    @g_bitri (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_csn A)))
      (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_csn A))) (.classEq D A) p0038
      p0042
  have p0044 :=
    @g_anbi12i (.classMem (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
          (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D)))
      (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_csn A))) (.classEq D A) p0037 p0043
  have p0045 :=
    @g_bitri
      (.classMem (syn_cop R D)
        (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A))))
      (syn_wa (.classMem (syn_cop R D) (syn_cin (syn_clntp) (syn_chwrels)))
        (.classMem (syn_cop R D) (syn_cxp (syn_cvv) (syn_csn A))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
            (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classEq D A))
      p0002 p0044
  have p0046 :=
    @g_bitri (.classMem (syn_cop R D) (syn_clntpc A))
      (.classMem (syn_cop R D)
        (syn_cin (syn_cin (syn_clntp) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_csn A))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D))
            (syn_wbr R (syn_cconnex) D)) (syn_wss R (syn_cxp D D))) (.classEq D A))
      p0001 p0045
  exact p0046

@[expose]
noncomputable def g_ellnpwcndv (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv)
    (hyp_ellnpwcndv_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_ellnpwcndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop R D) (syn_clnpwc A))
        (syn_wa (.classMem (syn_cop R D) (syn_clntpc A))
          (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_r_ne_d : r ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r := Ne.symm fresh_r_ne_d
  have dv_cache_0001 : d ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0003 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0004 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0005 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0006 : r ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_D, not_false_eq_true])
  have dv_cache_0007 : d ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, Finset.mem_union,
          fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : d ∉ ((syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, Finset.mem_union,
          fresh_d_not_R, fresh_d_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : r ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ d from (by exact fresh_r_ne_d))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lnpwc A r d
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2i (syn_clnpwc A)
      (syn_cin (syn_clntpc A) (syn_copab r d
          (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
      (syn_cop R D) p0000
  have p0002 :=
    @g_elin (syn_cop R D) (syn_clntpc A)
      (syn_copab r d (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))
  have p0003 := @g_id (.classEq (.cv r) R)
  have p0005 := @g_cnveqd (.classEq (.cv r) R) (.cv r) R p0003
  have p0006 :=
    @g_difeq12d (.classEq (.cv r) R) (.cv r) R (syn_ccnv (.cv r)) (syn_ccnv R) p0003 p0005
  have p0007 :=
    @g_breq1d (.classEq (.cv r) R) (syn_cdif (.cv r) (syn_ccnv (.cv r)))
      (syn_cdif R (syn_ccnv R)) (.cv d) (syn_cfound) p0006
  have p0008 := @g_breq2 (.cv d) D (syn_cdif R (syn_ccnv R)) (syn_cfound)
  have p0009 :=
    @g_opelopabg (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) (.cv d))
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D) r d R D (syn_cvv) (syn_cvv)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0007 p0008
  have p0010 :=
    @g_mp2an (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      (syn_wb (.classMem (syn_cop R D) (syn_copab r d
            (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
        (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D))
      hyp_ellnpwcndv_1 hyp_ellnpwcndv_2 p0009
  have p0011 :=
    @g_anbi2i
      (.classMem (syn_cop R D) (syn_copab r d
          (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d))))
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D)
      (.classMem (syn_cop R D) (syn_clntpc A)) p0010
  have p0012 :=
    @g_n_3bitri (.classMem (syn_cop R D) (syn_clnpwc A))
      (.classMem (syn_cop R D) (syn_cin (syn_clntpc A) (syn_copab r d
            (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))))
      (syn_wa (.classMem (syn_cop R D) (syn_clntpc A)) (.classMem (syn_cop R D) (syn_copab r d
            (syn_wbr (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cfound) (.cv d)))))
      (syn_wa (.classMem (syn_cop R D) (syn_clntpc A))
        (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) D))
      p0001 p0002 p0011
  exact p0012

@[expose]
noncomputable def g_lnpwkerfnfn : Nominal.NPrf (syn_wfn (syn_clnpwkerfn) (syn_cvv)) :=
  by
  have p0000 := @g_fnlndifop
  have p0001 := @g_ln1stfn
  have p0002 := @g_lnpwasymfnfn
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnpwasymfn) (syn_cvv)) p0001
      p0002
  have p0004 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnpwasymfn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_inidm (syn_cvv)
  have p0007 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0006
  have p0008 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cvv)) p0005 p0007
  have p0009 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0000 p0008
  have p0010 := (Nominal.classEqRefl (syn_clnpwkerfn))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnpwkerfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnpwkerfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) (syn_cvv))
      p0009 p0011
  exact p0012

@[expose]
noncomputable def g_lnpwkerfnex : Nominal.NPrf (.classMem (syn_clnpwkerfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwkerfn))
  have p0001 := @g_lndifopex
  have p0002 := @g_n_1stex
  have p0003 := @g_lnpwasymfnex
  have p0004 := @g_txpex (syn_c1st) (syn_clnpwasymfn) p0002 p0003
  have p0005 := @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_clnpwkerfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) (syn_cvv) p0000
      p0005
  exact p0006

@[expose]
noncomputable def g_lnpwkerfnval (D : Class) (R : Class)
    (hyp_lnpwkerfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwkerfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_clnker R)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwkerfn))
  have p0001 :=
    @g_fveq1i (syn_cop R D) (syn_clnpwkerfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) p0000
  have p0002 := @g_ln1stfn
  have p0003 := @g_lnpwasymfnfn
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnpwasymfn) (syn_cvv)) p0002
      p0003
  have p0005 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnpwasymfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) p0007
  have p0009 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cvv)) p0006 p0008
  have p0010 := @g_opex R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cvv))
      (.classMem (syn_cop R D) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fvco2 (syn_cvv) (syn_cop R D) (syn_clndifop)
      (syn_ctxp (syn_c1st) (syn_clnpwasymfn))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D))
      (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clnpwasymfn))) (syn_cop R D))
      (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D)))
      p0001 p0013
  have p0018 := @g_fvtxpvv (syn_cop R D) (syn_c1st) (syn_clnpwasymfn) p0002 p0003 p0010
  have p0019 := @g_opfv1st R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0020 := @g_lnpwasymfnval D R hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0021 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop R D)) R
      (syn_cfv (syn_clnpwasymfn) (syn_cop R D)) (syn_cdif R (syn_ccnv R)) p0019 p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D))
      (syn_cop (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cfv (syn_clnpwasymfn) (syn_cop R D)))
      (syn_cop R (syn_cdif R (syn_ccnv R))) p0018 p0021
  have p0023 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D))
      (syn_cop R (syn_cdif R (syn_ccnv R))) (syn_clndifop) p0022
  have p0024 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D))
      (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clnpwasymfn)) (syn_cop R D)))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R)))) p0014 p0023
  have p0025 := (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_cdif R (syn_ccnv R))))
  have p0026 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_cdif R (syn_ccnv R)))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R)))) p0025
  have p0027 := @g_cnvex R hyp_lnpwkerfnval_1
  have p0028 := @g_difex R (syn_ccnv R) hyp_lnpwkerfnval_1 p0027
  have p0029 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_cdif R (syn_ccnv R)) (syn_cvv))
      hyp_lnpwkerfnval_1 p0028
  have p0030 := @g_lndifopvalg R (syn_cdif R (syn_ccnv R)) (syn_cvv) (syn_cvv)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R))))
      (syn_co R (syn_clndifop) (syn_cdif R (syn_ccnv R)))
      (syn_cdif R (syn_cdif R (syn_ccnv R))) p0026 p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_cdif R (syn_ccnv R))))
      (syn_cdif R (syn_cdif R (syn_ccnv R))) p0024 p0032
  have p0034 := (Nominal.classEqRefl (syn_clnker R))
  have p0035 := @g_dfin4 R (syn_ccnv R)
  have p0036 :=
    @g_eqtri (syn_clnker R) (syn_cin R (syn_ccnv R))
      (syn_cdif R (syn_cdif R (syn_ccnv R))) p0034 p0035
  have p0037 := @g_eqcomi (syn_clnker R) (syn_cdif R (syn_cdif R (syn_ccnv R))) p0036
  have p0038 :=
    @g_eqtri (syn_cfv (syn_clnpwkerfn) (syn_cop R D))
      (syn_cdif R (syn_cdif R (syn_ccnv R))) (syn_clnker R) p0033 p0037
  exact p0038

@[expose]
noncomputable def g_lninteropfn : Nominal.NPrf (syn_wfn (syn_clninterop) (syn_cvv)) :=
  by
  have p0000 := @g_fnlndifop
  have p0001 := @g_ln1stfn
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0001
      p0000
  have p0004 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_inidm (syn_cvv)
  have p0007 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop))
      p0006
  have p0008 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0005 p0007
  have p0009 := @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0000 p0008
  have p0010 := (Nominal.classEqRefl (syn_clninterop))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv))
      p0009 p0011
  exact p0012

@[expose]
noncomputable def g_lninteropex : Nominal.NPrf (.classMem (syn_clninterop) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clninterop))
  have p0001 := @g_lndifopex
  have p0002 := @g_n_1stex
  have p0004 := @g_txpex (syn_c1st) (syn_clndifop) p0002 p0001
  have p0005 := @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_lninteropval (A : Class) (B : Class)
    (hyp_lninteropval_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_lninteropval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cin A B)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clninterop))
  have p0001 :=
    @g_fveq1i (syn_cop A B) (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0000
  have p0002 := @g_ln1stfn
  have p0003 := @g_fnlndifop
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0002
      p0003
  have p0005 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop))
      p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0006 p0008
  have p0010 := @g_opex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv))
      (.classMem (syn_cop A B) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fvco2 (syn_cvv) (syn_cop A B) (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B))
      (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cop A B))
      (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B)))
      p0001 p0013
  have p0018 := @g_fvtxpvv (syn_cop A B) (syn_c1st) (syn_clndifop) p0002 p0003 p0010
  have p0019 := @g_opfv1st A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0020 := (Nominal.classEqRefl (syn_co A (syn_clndifop) B))
  have p0021 :=
    @g_eqcomi (syn_co A (syn_clndifop) B) (syn_cfv (syn_clndifop) (syn_cop A B)) p0020
  have p0022 :=
    @g_pm3_2i (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) hyp_lninteropval_1
      hyp_lninteropval_2
  have p0023 := @g_lndifopvalg A B (syn_cvv) (syn_cvv)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop A B)) (syn_co A (syn_clndifop) B)
      (syn_cdif A B) p0021 p0024
  have p0026 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop A B)) A (syn_cfv (syn_clndifop) (syn_cop A B))
      (syn_cdif A B) p0019 p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B))
      (syn_cop (syn_cfv (syn_c1st) (syn_cop A B)) (syn_cfv (syn_clndifop) (syn_cop A B)))
      (syn_cop A (syn_cdif A B)) p0018 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B))
      (syn_cop A (syn_cdif A B)) (syn_clndifop) p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B))
      (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cop A B)))
      (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) p0014 p0028
  have p0030 := (Nominal.classEqRefl (syn_co A (syn_clndifop) (syn_cdif A B)))
  have p0031 :=
    @g_eqcomi (syn_co A (syn_clndifop) (syn_cdif A B))
      (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) p0030
  have p0032 := @g_difex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0033 :=
    @g_pm3_2i (.classMem A (syn_cvv)) (.classMem (syn_cdif A B) (syn_cvv))
      hyp_lninteropval_1 p0032
  have p0034 := @g_lndifopvalg A (syn_cdif A B) (syn_cvv) (syn_cvv)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B)))
      (syn_co A (syn_clndifop) (syn_cdif A B)) (syn_cdif A (syn_cdif A B)) p0031 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B))
      (syn_cfv (syn_clndifop) (syn_cop A (syn_cdif A B))) (syn_cdif A (syn_cdif A B))
      p0029 p0036
  have p0038 := @g_dfin4 A B
  have p0039 := @g_eqcomi (syn_cin A B) (syn_cdif A (syn_cdif A B)) p0038
  have p0040 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cop A B)) (syn_cdif A (syn_cdif A B))
      (syn_cin A B) p0037 p0039
  exact p0040

@[expose]
noncomputable def g_lnimagecrossfnval (B : Class) (R : Class)
    (hyp_lnimagecrossfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnimagecrossfnval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cxp B (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0001 :=
    @g_fveq1i (syn_cop R B) (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      p0000
  have p0002 := @g_ln2ndfn
  have p0003 := @g_vvex
  have p0004 := @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0009
  have p0011 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv))
      p0008 p0010
  have p0012 := @g_opex R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0013 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv))
      (.classMem (syn_cop R B) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_fvco2 (syn_cvv) (syn_cop R B) (syn_ccross)
      (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_clnimagecrossfn) (syn_cop R B))
      (syn_cfv (syn_ccom (syn_ccross)
          (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cop R B))
      (syn_cfv (syn_ccross)
        (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B)))
      p0001 p0015
  have p0022 :=
    @g_fvtxpvv (syn_cop R B) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) p0002
      p0005 p0012
  have p0023 := @g_opfv2nd R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0026 := @g_fvconst2 (syn_cvv) (syn_cvv) (syn_cop R B) p0003
  have p0027 := Nominal.mp p0012 p0026
  have p0028 :=
    @g_opeq12i (syn_cfv (syn_c2nd) (syn_cop R B)) B
      (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cop R B)) (syn_cvv) p0023
      p0027
  have p0029 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B))
      (syn_cop (syn_cfv (syn_c2nd) (syn_cop R B))
        (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cop R B)))
      (syn_cop B (syn_cvv)) p0022 p0028
  have p0030 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B))
      (syn_cop B (syn_cvv)) (syn_ccross) p0029
  have p0031 :=
    @g_eqtri (syn_cfv (syn_clnimagecrossfn) (syn_cop R B))
      (syn_cfv (syn_ccross)
        (syn_cfv (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cop R B)))
      (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) p0016 p0030
  have p0032 := (Nominal.classEqRefl (syn_co B (syn_ccross) (syn_cvv)))
  have p0033 :=
    @g_eqcomi (syn_co B (syn_ccross) (syn_cvv))
      (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) p0032
  have p0035 :=
    @g_pm3_2i (.classMem B (syn_cvv)) (.classMem (syn_cvv) (syn_cvv))
      hyp_lnimagecrossfnval_2 p0003
  have p0036 := @g_ovcross B (syn_cvv) (syn_cvv) (syn_cvv)
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @g_eqtri (syn_cfv (syn_ccross) (syn_cop B (syn_cvv)))
      (syn_co B (syn_ccross) (syn_cvv)) (syn_cxp B (syn_cvv)) p0033 p0037
  have p0039 :=
    @g_eqtri (syn_cfv (syn_clnimagecrossfn) (syn_cop R B))
      (syn_cfv (syn_ccross) (syn_cop B (syn_cvv))) (syn_cxp B (syn_cvv)) p0031 p0038
  exact p0039

@[expose]
noncomputable def g_lnimageresfnfn :
    Nominal.NPrf (syn_wfn (syn_clnimageresfn) (syn_cvv)) :=
  by
  have p0000 := @g_fnlndifop
  have p0001 := @g_ln1stfn
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0001
      p0000
  have p0004 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_inidm (syn_cvv)
  have p0007 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop))
      p0006
  have p0008 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0005 p0007
  have p0009 := @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0000 p0008
  have p0010 := (Nominal.classEqRefl (syn_clninterop))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv))
      p0009 p0011
  have p0014 := @g_fncross
  have p0015 := @g_ln2ndfn
  have p0016 := @g_vvex
  have p0017 := @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0015 p0018
  have p0020 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0021 := Nominal.mp p0019 p0020
  have p0023 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0006
  have p0024 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv))
      p0021 p0023
  have p0025 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
      p0014 p0024
  have p0026 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0027 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      p0026
  have p0028 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross)
          (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv))
      p0025 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      p0001 p0028
  have p0030 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0033 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0006
  have p0034 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0031 p0033
  have p0035 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0012 p0034
  have p0036 := (Nominal.classEqRefl (syn_clnimageresfn))
  have p0037 :=
    @g_fneq1i (syn_cvv) (syn_clnimageresfn)
      (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0036
  have p0038 :=
    @g_mpbir (syn_wfn (syn_clnimageresfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)))
        (syn_cvv))
      p0035 p0037
  exact p0038

@[expose]
noncomputable def g_lnimageresfnex :
    Nominal.NPrf (.classMem (syn_clnimageresfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnimageresfn))
  have p0001 := (Nominal.classEqRefl (syn_clninterop))
  have p0002 := @g_lndifopex
  have p0003 := @g_n_1stex
  have p0005 := @g_txpex (syn_c1st) (syn_clndifop) p0003 p0002
  have p0006 := @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0002 p0005
  have p0007 :=
    @g_eqeltri (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv) p0001 p0006
  have p0009 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0010 := @g_crossex
  have p0011 := @g_n_2ndex
  have p0012 := @g_vvex
  have p0013 := @g_snex (syn_cvv)
  have p0014 := @g_xpex (syn_cvv) (syn_csn (syn_cvv)) p0012 p0013
  have p0015 := @g_txpex (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) p0011 p0014
  have p0016 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
      p0010 p0015
  have p0017 :=
    @g_eqeltri (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      (syn_cvv) p0009 p0016
  have p0018 := @g_txpex (syn_c1st) (syn_clnimagecrossfn) p0003 p0017
  have p0019 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0007 p0018
  have p0020 :=
    @g_eqeltri (syn_clnimageresfn)
      (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv)
      p0000 p0019
  exact p0020

@[expose]
noncomputable def g_lnimageresfnval (B : Class) (R : Class)
    (hyp_lnimageresfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnimageresfnval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cres R B)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnimageresfn))
  have p0001 :=
    @g_fveq1i (syn_cop R B) (syn_clnimageresfn)
      (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0000
  have p0002 := @g_ln1stfn
  have p0003 := @g_fncross
  have p0004 := @g_ln2ndfn
  have p0005 := @g_vvex
  have p0006 := @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_inidm (syn_cvv)
  have p0012 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0011
  have p0013 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv))
      p0010 p0012
  have p0014 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
      p0003 p0013
  have p0015 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0016 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      p0015
  have p0017 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross)
          (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv))
      p0014 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      p0002 p0017
  have p0019 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0020 := Nominal.mp p0018 p0019
  have p0022 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0011
  have p0023 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0020 p0022
  have p0024 := @g_opex R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv))
      (.classMem (syn_cop R B) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_fvco2 (syn_cvv) (syn_cop R B) (syn_clninterop)
      (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B))
      (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)))
        (syn_cop R B))
      (syn_cfv (syn_clninterop)
        (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B)))
      p0001 p0027
  have p0046 :=
    @g_fvtxpvv (syn_cop R B) (syn_c1st) (syn_clnimagecrossfn) p0002 p0017 p0024
  have p0047 := @g_opfv1st R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0048 := @g_lnimagecrossfnval B R hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0049 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop R B)) R
      (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)) (syn_cxp B (syn_cvv)) p0047 p0048
  have p0050 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B))
      (syn_cop (syn_cfv (syn_c1st) (syn_cop R B)) (syn_cfv (syn_clnimagecrossfn) (syn_cop R B)))
      (syn_cop R (syn_cxp B (syn_cvv))) p0046 p0049
  have p0051 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B))
      (syn_cop R (syn_cxp B (syn_cvv))) (syn_clninterop) p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B))
      (syn_cfv (syn_clninterop)
        (syn_cfv (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cop R B)))
      (syn_cfv (syn_clninterop) (syn_cop R (syn_cxp B (syn_cvv)))) p0028 p0051
  have p0054 := @g_xpex B (syn_cvv) hyp_lnimageresfnval_2 p0005
  have p0055 := @g_lninteropval R (syn_cxp B (syn_cvv)) hyp_lnimageresfnval_1 p0054
  have p0056 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B))
      (syn_cfv (syn_clninterop) (syn_cop R (syn_cxp B (syn_cvv))))
      (syn_cin R (syn_cxp B (syn_cvv))) p0052 p0055
  have p0057 := (Nominal.classEqRefl (syn_cres R B))
  have p0058 := @g_eqcomi (syn_cres R B) (syn_cin R (syn_cxp B (syn_cvv))) p0057
  have p0059 :=
    @g_eqtri (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cin R (syn_cxp B (syn_cvv)))
      (syn_cres R B) p0056 p0058
  exact p0059

@[expose]
noncomputable def g_lnimageopfn : Nominal.NPrf (syn_wfn (syn_clnimageop) (syn_cvv)) :=
  by
  have p0000 := @g_ranfnfn
  have p0001 := @g_fnlndifop
  have p0002 := @g_ln1stfn
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0002
      p0001
  have p0005 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop))
      p0007
  have p0009 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0006 p0008
  have p0010 := @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0001 p0009
  have p0011 := (Nominal.classEqRefl (syn_clninterop))
  have p0012 :=
    @g_fneq1i (syn_cvv) (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0011
  have p0013 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv))
      p0010 p0012
  have p0015 := @g_fncross
  have p0016 := @g_ln2ndfn
  have p0017 := @g_vvex
  have p0018 := @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0016 p0019
  have p0021 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0022 := Nominal.mp p0020 p0021
  have p0024 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0007
  have p0025 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv))
      p0022 p0024
  have p0026 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
      p0015 p0025
  have p0027 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross)
          (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv))
      p0026 p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      p0002 p0029
  have p0031 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0032 := Nominal.mp p0030 p0031
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0007
  have p0035 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0013 p0035
  have p0037 := (Nominal.classEqRefl (syn_clnimageresfn))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_clnimageresfn)
      (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_clnimageresfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)))
        (syn_cvv))
      p0036 p0038
  have p0040 := @g_fncovv (syn_cranfn) (syn_clnimageresfn) p0000 p0039
  have p0041 := (Nominal.classEqRefl (syn_clnimageop))
  have p0042 :=
    @g_fneq1i (syn_cvv) (syn_clnimageop) (syn_ccom (syn_cranfn) (syn_clnimageresfn)) p0041
  have p0043 :=
    @g_mpbir (syn_wfn (syn_clnimageop) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cranfn) (syn_clnimageresfn)) (syn_cvv)) p0040 p0042
  exact p0043

@[expose]
noncomputable def g_lnimageopex : Nominal.NPrf (.classMem (syn_clnimageop) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnimageop))
  have p0001 := @g_ranfnex
  have p0002 := (Nominal.classEqRefl (syn_clnimageresfn))
  have p0003 := (Nominal.classEqRefl (syn_clninterop))
  have p0004 := @g_lndifopex
  have p0005 := @g_n_1stex
  have p0007 := @g_txpex (syn_c1st) (syn_clndifop) p0005 p0004
  have p0008 := @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0004 p0007
  have p0009 :=
    @g_eqeltri (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv) p0003 p0008
  have p0011 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0012 := @g_crossex
  have p0013 := @g_n_2ndex
  have p0014 := @g_vvex
  have p0015 := @g_snex (syn_cvv)
  have p0016 := @g_xpex (syn_cvv) (syn_csn (syn_cvv)) p0014 p0015
  have p0017 := @g_txpex (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) p0013 p0016
  have p0018 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
      p0012 p0017
  have p0019 :=
    @g_eqeltri (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      (syn_cvv) p0011 p0018
  have p0020 := @g_txpex (syn_c1st) (syn_clnimagecrossfn) p0005 p0019
  have p0021 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0009 p0020
  have p0022 :=
    @g_eqeltri (syn_clnimageresfn)
      (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv)
      p0002 p0021
  have p0023 := @g_coex (syn_cranfn) (syn_clnimageresfn) p0001 p0022
  have p0024 :=
    @g_eqeltri (syn_clnimageop) (syn_ccom (syn_cranfn) (syn_clnimageresfn)) (syn_cvv)
      p0000 p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end
