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

/-- Checked nominal proof certificate identified upstream as `g_hncardmono`. -/
@[expose]
noncomputable def gHncardmono (A : Class) (D : Class)
    (hyp_hncardmono_1 : Nominal.NPrf (synWss D A))
    (hyp_hncardmono_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hncardmono_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWbr (synChncard D) (synClec) (synChncard A)) :=
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
  have dv_cache_0001 : f ∉ ((synChnqinc D A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          Finset.mem_union, fresh_f_not_A, fresh_f_not_D, or_false, not_false_eq_true])
  have dv_cache_0002 :
    f ∉ ((synWf1 (synChnqinc D A) (synChnord D) (synChnord A))).fv :=
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
  have dv_cache_0003 : f ∉ ((synChnord D)).fv :=
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
  have dv_cache_0004 : f ∉ ((synChnord A)).fv :=
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
  have p0000 := @gHnqincf1 A D hyp_hncardmono_1 hyp_hncardmono_2 hyp_hncardmono_3
  have p0001 :=
    @gPm32i (.classMem D (synCvv)) (.classMem A (synCvv)) hyp_hncardmono_2
      hyp_hncardmono_3
  have p0002 := @gHnqincexg A D
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gF1eq1 (synChnord D) (synChnord A) (.cv f) (synChnqinc D A)
  have p0005 :=
    @gSpcegv (synWf1 (.cv f) (synChnord D) (synChnord A))
      (synWf1 (synChnqinc D A) (synChnord D) (synChnord A)) f (synChnqinc D A)
      (synCvv) dv_cache_0001 dv_cache_0002 p0004
  have p0006 := Nominal.mp p0003 p0005
  have p0007 := Nominal.mp p0000 p0006
  have p0008 := @gHnordex D hyp_hncardmono_2
  have p0009 := @gHnordex A hyp_hncardmono_3
  have p0010 :=
    @gNclenc (synChnord D) (synChnord A) f dv_cache_0003 dv_cache_0004 p0008 p0009
  have p0011 :=
    @gMpbir (synWbr (synCnc (synChnord D)) (synClec) (synCnc (synChnord A)))
      (synWex f (synWf1 (.cv f) (synChnord D) (synChnord A))) p0007 p0010
  have p0012 := (Nominal.classEqRefl (synChncard D))
  have p0013 := (Nominal.classEqRefl (synChncard A))
  have p0014 :=
    @gBreq12i (synChncard D) (synCnc (synChnord D)) (synChncard A)
      (synCnc (synChnord A)) (synClec) p0012 p0013
  have p0015 :=
    @gMpbir (synWbr (synChncard D) (synClec) (synChncard A))
      (synWbr (synCnc (synChnord D)) (synClec) (synCnc (synChnord A))) p0011 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodecnndv`. -/
@[expose]
noncomputable def gHnwcutcodecnndv (x : Var) (D : Class) (R : Class)
    (hyp_hnwcutcodecnndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))) :=
  by
  have p0000 := @gA1i (synWbr R (synCwe) D) (.classMem (.cv x) D) hyp_hnwcutcodecnndv_1
  have p0001 := @gId (.classMem (.cv x) D)
  have p0002 :=
    @gJca (.classMem (.cv x) D) (synWbr R (synCwe) D) (.classMem (.cv x) D) p0000 p0001
  have p0003 := @gWestrsegndv x D R
  have p0004 :=
    @gSyl (.classMem (.cv x) D) (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0006 :=
    @gBiimpi
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCwe))
      p0005
  have p0007 :=
    @gSyl (.classMem (.cv x) D)
      (synWbr (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCwe) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCwe))
      p0004 p0006
  have p0008 := @gBrex R D (synCwe)
  have p0009 :=
    @gSimpld (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0008
  have p0010 := Nominal.mp hyp_hnwcutcodecnndv_1 p0009
  have p0012 :=
    @gSimprd (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0008
  have p0013 := Nominal.mp hyp_hnwcutcodecnndv_1 p0012
  have p0017 := @gIdex
  have p0018 := @gDifex R (synCid) p0010 p0017
  have p0019 := @gCnvex (synCdif R (synCid)) p0018
  have p0020 := @gSnex (.cv x)
  have p0021 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0019 p0020
  have p0022 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0013 p0021
  have p0035 :=
    @gXpex (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0022
      p0022
  have p0036 :=
    @gInex R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0010 p0035
  have p0037 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0050 :=
    @gElpw (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D
      p0022
  have p0051 :=
    @gMpbir
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCpw D))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      p0037 p0050
  have p0052 :=
    @gPm32i
      (.classMem (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCpw D))
      p0036 p0051
  have p0053 :=
    @gOpelxp
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)
      (synCpw D)
  have p0054 :=
    @gMpbir
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCxp (synCvv) (synCpw D)))
      (synWa (.classMem (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCvv)) (.classMem
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCpw D)))
      p0052 p0053
  have p0055 :=
    @gA1i
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCxp (synCvv) (synCpw D)))
      (.classMem (.cv x) D) p0054
  have p0056 :=
    @gJca (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synCwe))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCxp (synCvv) (synCpw D)))
      p0007 p0055
  have p0057 :=
    @gElin
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCwe) (synCxp (synCvv) (synCpw D))
  have p0058 :=
    @gA1i
      (synWb (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCin (synCwe) (synCxp (synCvv) (synCpw D)))) (synWa (.classMem (synCop
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synCwe)) (.classMem (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synCxp (synCvv) (synCpw D)))))
      (.classMem (.cv x) D) p0057
  have p0059 :=
    @gMpbird (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin (synCwe) (synCxp (synCvv) (synCpw D))))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCwe)) (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synCxp (synCvv) (synCpw D))))
      p0056 p0058
  have p0060 := (Nominal.classEqRefl (synChwcodes D))
  have p0061 :=
    @gEleq2i (synChwcodes D) (synCin (synCwe) (synCxp (synCvv) (synCpw D)))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0060
  have p0062 :=
    @gSylibr (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synCin (synCwe) (synCxp (synCvv) (synCpw D))))
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcodes D))
      p0059 p0061
  have p0063 :=
    @gInss2 R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0105 :=
    @gOpfv2nd
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0036
      p0022
  have p0148 :=
    @gPm32i
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0105 p0105
  have p0149 :=
    @gXpeq12
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv (synC2nd) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
  have p0150 := Nominal.mp p0148 p0149
  have p0151 :=
    @gEqcomi
      (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0150
  have p0152 :=
    @gSseq2
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0153 := Nominal.mp p0151 p0152
  have p0154 :=
    @gMpbi
      (synWss (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWss (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0063 p0153
  have p0196 :=
    @gOpfv1st
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0036
      p0022
  have p0197 :=
    @gSseq1
      (synCfv (synC1st) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCfv (synC2nd) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0198 := Nominal.mp p0196 p0197
  have p0199 :=
    @gMpbir
      (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWss (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0154 p0198
  have p0200 :=
    @gA1i
      (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (.classMem (.cv x) D) p0199
  have p0201 :=
    @gJca (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcodes D))
      (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0062 p0200
  have p0243 :=
    @gOpex
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0036
      p0022
  have p0244 :=
    @gElhwcncl D
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0245 := Nominal.mp p0243 p0244
  have p0246 :=
    @gA1i
      (synWb (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwcn D)) (synWa (.classMem (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (synChwcodes D)) (synWss (synCfv (synC1st) (synCop (synCin R (synCxp
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.classMem (.cv x) D) p0245
  have p0247 :=
    @gMpbird (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcn D))
      (synWa (.classMem (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwcodes D)) (synWss (synCfv (synC1st) (synCop (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCxp (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCfv (synC2nd) (synCop (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0201 p0246
  have p0248 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0249 :=
    @gEleq1i (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synChwcn D) p0248
  have p0250 :=
    @gSylibr (.classMem (.cv x) D)
      (.classMem (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D)) p0247 p0249
  exact p0250

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodecnclndv`. -/
@[expose]
noncomputable def gHnwcutcodecnclndv (B : Class) (D : Class) (R : Class)
    (hyp_hnwcutcodecnclndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D) (.classMem (synChnwcutcode R D B) (synChwcn D))) :=
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
      ((Wff.imp (.classMem B D) (.classMem (synChnwcutcode R D B) (synChwcn D)))).fv :=
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
  have p0000 := @gElex B D
  have p0001 := @gEleq1 (.cv x) B D
  have p0002 := @gHnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @gEleq1d (.classEq (.cv x) B) (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B)
      (synChwcn D) p0002
  have p0004 :=
    @gImbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synChnwcutcode R D B) (synChwcn D)) p0001 p0003
  have p0005 := @gHnwcutcodecnndv x D R hyp_hnwcutcodecnclndv_1
  have p0006 :=
    @gVtoclg
      (.imp (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D)))
      (.imp (.classMem B D) (.classMem (synChnwcutcode R D B) (synChwcn D))) x B
      (synCvv) dv_cache_0002 dv_cache_0003 p0004 p0005
  have p0007 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B D)
      (.classMem (synChnwcutcode R D B) (synChwcn D)) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelfndv`. -/
@[expose]
noncomputable def gHnwcutrelfndv (D : Class) (R : Class)
    (hyp_hnwcutrelfndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D)) :=
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
  have dv_cache_0001 : q ∉ ((synCpw1 D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synChwcn D)).fv :=
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
  have dv_cache_0003 : q ∉ ((synChnwcutrel R D)).fv :=
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
  have p0000 := @gHnwcutrelfn D R hyp_hnwcutrelfndv_1
  have p0001 := @gHnwpw1argcl D q
  have p0002 :=
    @gSimpld (.classMem (.cv q) (synCpw1 D)) (.classMem (synCuni (.cv q)) D)
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0001
  have p0003 := @gHnwcutcodecnclndv (synCuni (.cv q)) D R hyp_hnwcutrelfndv_1
  have p0004 :=
    @gSyl (.classMem (.cv q) (synCpw1 D)) (.classMem (synCuni (.cv q)) D)
      (.classMem (synChnwcutcode R D (synCuni (.cv q))) (synChwcn D)) p0002 p0003
  have p0005 := @gHnwcutrelval D R q hyp_hnwcutrelfndv_1
  have p0006 :=
    @gEleq1d (.classMem (.cv q) (synCpw1 D)) (synCfv (synChnwcutrel R D) (.cv q))
      (synChnwcutcode R D (synCuni (.cv q))) (synChwcn D) p0005
  have p0007 :=
    @gMpbird (.classMem (.cv q) (synCpw1 D))
      (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D))
      (.classMem (synChnwcutcode R D (synCuni (.cv q))) (synChwcn D)) p0004 p0006
  have p0008 :=
    @gRgen (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D)) q
      (synCpw1 D) p0007
  have p0009 :=
    @gPm32i (synWfn (synChnwcutrel R D) (synCpw1 D))
      (synWral q (synCpw1 D) (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D)))
      p0000 p0008
  have p0010 :=
    @gFfnfv q (synCpw1 D) (synChwcn D) (synChnwcutrel R D) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0011 :=
    @gMpbir (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWa (synWfn (synChnwcutrel R D) (synCpw1 D)) (synWral q (synCpw1 D)
          (.classMem (synCfv (synChnwcutrel R D) (.cv q)) (synChwcn D))))
      p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hnwcutsirelvalndv`. -/
@[expose]
noncomputable def gHnwcutsirelvalndv (D : Class) (R : Class) (q : Var)
    (hyp_hnwcutsirelvalndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classEq (synCfv (synCsi (synChnwcutrel R D)) (.cv q))
          (synCsn (synChnwcutcode R D (synCuni (synCuni (.cv q))))))) :=
  by
  have p0000 := @gPw12argcl (.cv q) D
  have p0001 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0000
  have p0002 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.cv q)
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) (synCsi (synChnwcutrel R D))
      p0001
  have p0004 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0000
  have p0005 := @gSnelpw1 (synCuni (synCuni (.cv q))) D
  have p0006 :=
    @gBiimpri (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D))
      (.classMem (synCuni (synCuni (.cv q))) D) p0005
  have p0007 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D)) p0004 p0006
  have p0008 := @gHnwcutrelfndv D R hyp_hnwcutsirelvalndv_1
  have p0009 :=
    @gSifvald (synCpw1 D) (synChwcn D) (synCsn (synCuni (synCuni (.cv q))))
      (synChnwcutrel R D) p0008
  have p0010 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCsn (synCuni (synCuni (.cv q)))) (synCpw1 D))
      (.classEq (synCfv (synCsi (synChnwcutrel R D))
          (synCsn (synCsn (synCuni (synCuni (.cv q))))))
        (synCsn (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))))
      p0007 p0009
  have p0011 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synChnwcutrel R D)) (.cv q))
      (synCfv (synCsi (synChnwcutrel R D)) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
      (synCsn (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q))))))
      p0002 p0010
  have p0014 :=
    @gHnwcutrelvalcld (synCuni (synCuni (.cv q))) D R hyp_hnwcutsirelvalndv_1
  have p0015 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))
        (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      p0004 p0014
  have p0016 :=
    @gSneqd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q)))))
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) p0015
  have p0017 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synCfv (synCsi (synChnwcutrel R D)) (.cv q))
      (synCsn (synCfv (synChnwcutrel R D) (synCsn (synCuni (synCuni (.cv q))))))
      (synCsn (synChnwcutcode R D (synCuni (synCuni (.cv q))))) p0011 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassltnendv`. -/
@[expose]
noncomputable def gHnwcutclassltnendv (x : Var) (y : Var) (D : Class) (R : Class)
    (hyp_hnwcutclassltnendv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) D) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (.neg
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))) :=
  by
  have p0000 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      hyp_hnwcutclassltnendv_1
  have p0001 :=
    @gSimpl (.classMem (.cv y) D)
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0002 :=
    @gJca
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr R (synCwe) D) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @gSimpr (.classMem (.cv y) D)
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0004 :=
    @gJca
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0002 p0003
  have p0005 := @gHnwcutcodeltnoiso x y D R
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D)
          (synChnwcutcode R D (.cv y))))
      p0004 p0005
  have p0008 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))
  have p0009 :=
    @gSsel (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) D
      (.cv x)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv x) D) p0003 p0010
  have p0012 := @gHnwcutcodecnclndv (.cv x) D R hyp_hnwcutclassltnendv_1
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D)) p0011
      p0012
  have p0015 := @gHnwcutcodecnclndv (.cv y) D R hyp_hnwcutclassltnendv_1
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) D) (.classMem (synChnwcutcode R D (.cv y)) (synChwcn D)) p0001
      p0015
  have p0017 :=
    @gJca
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv y)) (synChwcn D)) p0013 p0016
  have p0018 := @gBrex R D (synCwe)
  have p0019 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0020 :=
    @gSyl (synWbr R (synCwe) D)
      (synWa (.classMem R (synCvv)) (.classMem D (synCvv))) (.classMem D (synCvv))
      p0018 p0019
  have p0021 := Nominal.mp hyp_hnwcutclassltnendv_1 p0020
  have p0022 :=
    @gHwnisoclasseqbcl D (synChnwcutcode R D (.cv x)) (synChnwcutcode R D (.cv y))
      p0021
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
        (.classMem (synChnwcutcode R D (.cv y)) (synChwcn D)))
      (synWb (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
        (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y))))
      p0017 p0022
  have p0024 :=
    @gBiimpd
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      p0023
  have p0025 :=
    @gCon3d
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      p0024
  have p0026 :=
    @gMpd
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D)
          (synChnwcutcode R D (.cv y))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassinjndv`. -/
@[expose]
noncomputable def gHnwcutclassinjndv (x : Var) (y : Var) (D : Class) (R : Class)
    (hyp_hnwcutclassinjndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
          (.classEq (.cv x) (.cv y)))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWne (.cv x) (.cv y))
  have p0001 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      p0000 p0001
  have p0003 := @gWppweconnex D R
  have p0004 := Nominal.mp hyp_hnwcutclassinjndv_1 p0003
  have p0005 :=
    @gA1i (synWbr R (synCconnex) D)
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      p0004
  have p0007 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
  have p0008 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0007
      p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classMem (.cv x) D) p0000 p0009
  have p0013 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0007
      p0013
  have p0015 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classMem (.cv y) D) p0000 p0014
  have p0016 :=
    @gConnexd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0005 p0010 p0015
  have p0017 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0017 p0010
  have p0024 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0026 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWne (.cv x) (.cv y))
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWne (.cv x) (.cv y)) p0017 p0026
  have p0028 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)) p0024 p0027
  have p0029 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)))
      p0023 p0028
  have p0030 := @gElstrictseg y x D R
  have p0031 :=
    @gBiimpri
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0029 p0031
  have p0033 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0032
  have p0034 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0034 p0015
  have p0041 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
  have p0044 :=
    @gNecomd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0026
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWne (.cv y) (.cv x)) p0034 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)) p0041 p0045
  have p0047 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
      p0040 p0046
  have p0048 := @gElstrictseg x y D R
  have p0049 :=
    @gBiimpri
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0048
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0047 p0049
  have p0051 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0050
  have p0052 :=
    @gOrim12d
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0033 p0051
  have p0053 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWo (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0016 p0052
  have p0059 := @gHnwcutclassltnendv x y D R hyp_hnwcutclassinjndv_1
  have p0060 :=
    @gEx (.classMem (.cv y) D)
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0059
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv y) D)
      (.imp (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (.neg
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))))
      p0015 p0060
  have p0067 := @gHnwcutclassltnendv y x D R hyp_hnwcutclassinjndv_1
  have p0068 :=
    @gEx (.classMem (.cv x) D)
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))))
      p0067
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) D)
      (.imp (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.neg
          (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)))))
      p0010 p0068
  have p0070 :=
    @gEqcom (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
      (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
  have p0071 :=
    @gBiimpi
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)))
      p0070
  have p0072 :=
    @gCon3i
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)))
      p0071
  have p0073 :=
    @gSyl6
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0069 p0072
  have p0074 :=
    @gJaod
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0061 p0073
  have p0075 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWo (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0053 p0074
  have p0076 :=
    @gPm221dd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.neg (synWne (.cv x) (.cv y))) p0002 p0075
  have p0077 :=
    @gPm201da
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWne (.cv x) (.cv y)) p0076
  have p0078 := @gNne (.cv x) (.cv y)
  have p0079 :=
    @gSylib
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.neg (synWne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0077 p0078
  have p0080 :=
    @gEx (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (.cv x) (.cv y)) p0079
  exact p0080

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassinjclndv`. -/
@[expose]
noncomputable def gHnwcutclassinjclndv (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_hnwcutclassinjclndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))) :=
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
      ((Wff.imp (synWa (.classMem B D) (.classMem C D)) (.imp
            (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
              (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C)))).fv :=
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
      ((Wff.imp (synWa (.classMem B D) (.classMem (.cv y) D)) (.imp
            (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
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
  have p0000 := @gSimpl (.classMem B D) (.classMem C D)
  have p0001 := @gElex B D
  have p0002 :=
    @gSyl (synWa (.classMem B D) (.classMem C D)) (.classMem B D)
      (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpr (.classMem B D) (.classMem C D)
  have p0004 := @gElex C D
  have p0005 :=
    @gSyl (synWa (.classMem B D) (.classMem C D)) (.classMem C D)
      (.classMem C (synCvv)) p0003 p0004
  have p0006 :=
    @gJca (synWa (.classMem B D) (.classMem C D)) (.classMem B (synCvv))
      (.classMem C (synCvv)) p0002 p0005
  have p0007 := @gEleq1 (.cv x) B D
  have p0008 := @gBiid (.classMem (.cv y) D)
  have p0009 :=
    @gA1i (synWb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (.cv y) D) (.classMem (.cv y) D) p0007 p0009
  have p0011 := @gHnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0012 :=
    @gEceq1 (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B) (synChwniso D)
  have p0013 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D B) (synChwniso D)))
      p0011 p0012
  have p0014 :=
    @gEqeq1d (.classEq (.cv x) B) (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
      (synCec (synChnwcutcode R D B) (synChwniso D))
      (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)) p0013
  have p0015 := @gId (.classEq (.cv x) B)
  have p0016 := @gEqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0015
  have p0017 :=
    @gImbi12d (.classEq (.cv x) B)
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0014 p0016
  have p0018 :=
    @gImbi12d (.classEq (.cv x) B) (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem B D) (.classMem (.cv y) D))
      (.imp (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq (.cv x) (.cv y)))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq B (.cv y)))
      p0010 p0017
  have p0019 := @gBiid (.classMem B D)
  have p0020 := @gA1i (synWb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0019
  have p0021 := @gEleq1 (.cv y) C D
  have p0022 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D)
      (.classMem C D) p0020 p0021
  have p0023 := @gHnwcutcodeeq3 (.cv y) C D R dv_cache_0002
  have p0024 :=
    @gEceq1 (synChnwcutcode R D (.cv y)) (synChnwcutcode R D C) (synChwniso D)
  have p0025 :=
    @gSyl (.classEq (.cv y) C)
      (.classEq (synChnwcutcode R D (.cv y)) (synChnwcutcode R D C))
      (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      p0023 p0024
  have p0026 :=
    @gEqeq2d (.classEq (.cv y) C) (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
      (synCec (synChnwcutcode R D C) (synChwniso D))
      (synCec (synChnwcutcode R D B) (synChwniso D)) p0025
  have p0027 := @gId (.classEq (.cv y) C)
  have p0028 := @gEqeq2d (.classEq (.cv y) C) (.cv y) C B p0027
  have p0029 :=
    @gImbi12d (.classEq (.cv y) C)
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      (.classEq B (.cv y)) (.classEq B C) p0026 p0028
  have p0030 :=
    @gImbi12d (.classEq (.cv y) C) (synWa (.classMem B D) (.classMem (.cv y) D))
      (synWa (.classMem B D) (.classMem C D))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq B (.cv y)))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))
      p0022 p0029
  have p0031 := @gHnwcutclassinjndv x y D R hyp_hnwcutclassinjclndv_1
  have p0032 :=
    @gVtocl2g
      (.imp (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
          (.classEq (.cv x) (.cv y))))
      (.imp (synWa (.classMem B D) (.classMem (.cv y) D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq B (.cv y))))
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C)))
      x y B C (synCvv) (synCvv) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0018 p0030 p0031
  have p0033 :=
    @gSyl (synWa (.classMem B D) (.classMem C D))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C)))
      p0006 p0032
  have p0034 :=
    @gPm243i (synWa (.classMem B D) (.classMem C D))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))
      p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_lnkereq`. -/
@[expose]
noncomputable def gLnkereq (R : Class) (S : Class) :
    Nominal.NPrf (.imp (.classEq R S) (.classEq (synClnker R) (synClnker S))) :=
  by
  have p0000 := @gId (.classEq R S)
  have p0001 := @gCnveq R S
  have p0002 := @gIneq12d (.classEq R S) R S (synCcnv R) (synCcnv S) p0000 p0001
  have p0003 := (Nominal.classEqRefl (synClnker R))
  have p0004 := (Nominal.classEqRefl (synClnker S))
  have p0005 :=
    @gN3eqtr4g (.classEq R S) (synCin R (synCcnv R)) (synCin S (synCcnv S))
      (synClnker R) (synClnker S) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_lnanbi12ni`. -/
@[expose]
noncomputable def gLnanbi12ni (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_lnanbi12ni_1 : Nominal.NPrf (synWb ph ps))
    (hyp_lnanbi12ni_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (synWb (synWa ph (.neg ch)) (synWa ps (.neg th))) :=
  by
  have p0000 := @gNotbii ch th hyp_lnanbi12ni_2
  have p0001 := @gAnbi12i ph ps (.neg ch) (.neg th) hyp_lnanbi12ni_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_lndifopvalg`. -/
@[expose]
noncomputable def gLndifopvalg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (.classEq (synCo A (synClndifop) B) (synCdif A B))) :=
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
  have dv_cache_0006 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0007 : y ∉ ((synCvv)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCdif A (.cv y))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCdif A B)).fv :=
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
  have dv_cache_0010 : y ∉ ((synCdif A B)).fv :=
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
  have p0000 := @gElex A V
  have p0001 := @gElex B W
  have p0002 := @gDifexg A B (synCvv) (synCvv)
  have p0003 := @gDifeq1 (.cv x) A (.cv y)
  have p0004 := @gDifeq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLndifop x y
      dv_cache_0001
  have p0006 :=
    @gOvmpt2g x y A B (synCvv) (synCvv) (synCdif (.cv x) (.cv y)) (synCdif A B)
      (synClndifop) (synCdif A (.cv y)) (synCvv) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @gMpd3an3 (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCdif A B) (synCvv))
      (.classEq (synCo A (synClndifop) B) (synCdif A B)) p0002 p0006
  have p0008 :=
    @gSyl2an (.classMem A V) (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classEq (synCo A (synClndifop) B) (synCdif A B)) (.classMem B W) p0000 p0001
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fnlndifop`. -/
@[expose]
noncomputable def gFnlndifop : Nominal.NPrf (synWfn (synClndifop) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLndifop x y
      dv_cache_0001
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gDifex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @gFnmpt2i x y (synCvv) (synCvv) (synCdif (.cv x) (.cv y)) (synClndifop)
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @gXpvv
  have p0006 := @gFneq2i (synCxp (synCvv) (synCvv)) (synCvv) (synClndifop) p0005
  have p0007 :=
    @gMpbi (synWfn (synClndifop) (synCxp (synCvv) (synCvv)))
      (synWfn (synClndifop) (synCvv)) p0004 p0006
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

/-- Checked nominal proof certificate identified upstream as `g_lndifopex`. -/
@[expose]
noncomputable def gLndifopex : Nominal.NPrf (.classMem (synClndifop) (synCvv)) :=
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
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
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
    x ∉ ((synCdif (synCins3 (synCsset)) (synCins2 (synCsset)))).fv :=
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
    y ∉ ((synCdif (synCins3 (synCsset)) (synCins2 (synCsset)))).fv :=
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
    z ∉ ((synCdif (synCins3 (synCsset)) (synCins2 (synCsset)))).fv :=
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
  have dv_cache_0007 : z ∉ ((synCdif (.cv x) (.cv y))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLndifop x y
      dv_cache_0001
  have p0001 := @gVex y
  have p0002 := @gOtelins3 (synCsn (.cv z)) (.cv x) (.cv y) (synCsset) p0001
  have p0003 := @gVex z
  have p0004 := @gVex x
  have p0005 := @gOpelssetsn (.cv z) (.cv x) p0003 p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x) p0002
      p0006_e01_recanon
  have p0007 := @gOtelins2 (synCsn (.cv z)) (.cv x) (.cv y) (synCsset) p0004
  have p0008 := @gOpelssetsn (.cv z) (.cv y) p0003 p0001
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)) (.objMem z y) p0007
      p0009_e01_recanon
  have p0010 :=
    @gLnanbi12ni
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset)))
      (.objMem z x)
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.objMem z y) p0006 p0009
  have p0011 :=
    @gEldif (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset))
      (synCins2 (synCsset))
  have p0012 := @gEldif (.cv z) (.cv x) (.cv y)
  have p0013_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCdif (.cv x) (.cv y)))
        (synWa (.objMem z x) (.neg (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCdif synCin synCcompl synCnin synWnan synWa
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
    @gN3bitr4i
      (synWa (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
          (synCins3 (synCsset))) (.neg
          (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
            (synCins2 (synCsset)))))
      (synWa (.objMem z x) (.neg (.objMem z y)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
        (synCdif (synCins3 (synCsset)) (synCins2 (synCsset))))
      (.classMem (.cv z) (synCdif (.cv x) (.cv y))) p0010 p0011 p0013_e02_recanon
  have p0014 :=
    @gReleqmpt2 x y z (synCvv) (synCvv)
      (synCdif (synCins3 (synCsset)) (synCins2 (synCsset)))
      (synCdif (.cv x) (.cv y)) dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008
      dv_cache_0009 p0013
  have p0015 :=
    @gEqtr4i (synClndifop)
      (synCmpt2 x (synCvv) y (synCvv) (synCdif (.cv x) (.cv y)))
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCdif (synCins3 (synCsset)) (synCins2 (synCsset))))) (synC1c)))
      p0000 p0014
  have p0016 := @gVvex
  have p0018 := @gSsetex
  have p0019 := @gIns3ex (synCsset) p0018
  have p0021 := @gIns2ex (synCsset) p0018
  have p0022 := @gDifex (synCins3 (synCsset)) (synCins2 (synCsset)) p0019 p0021
  have p0023 :=
    @gMpt2exlem (synCvv) (synCvv)
      (synCdif (synCins3 (synCsset)) (synCins2 (synCsset))) p0016 p0016 p0022
  have p0024 :=
    @gEqeltri (synClndifop)
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCdif (synCins3 (synCsset)) (synCins2 (synCsset))))) (synC1c)))
      (synCvv) p0015 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_ln1stfn`. -/
@[expose]
noncomputable def gLn1stfn : Nominal.NPrf (synWfn (synC1st) (synCvv)) :=
  by
  have p0000 := @gN1stfo
  have p0001 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ln2ndfn`. -/
@[expose]
noncomputable def gLn2ndfn : Nominal.NPrf (synWfn (synC2nd) (synCvv)) :=
  by
  have p0000 := @gN2ndfo
  have p0001 := @gFofn (synCvv) (synCvv) (synC2nd)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_lnpwasymfnfn`. -/
@[expose]
noncomputable def gLnpwasymfnfn : Nominal.NPrf (synWfn (synClnpwasymfn) (synCvv)) :=
  by
  have p0000 := @gFnlndifop
  have p0001 := @gN1stfo
  have p0002 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gImageswapfn
  have p0008 := @gFncovv (synCimage (synCswap)) (synC1st) p0004 p0003
  have p0009 :=
    @gPm32i (synWfn (synC1st) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synC1st)) (synCvv)) p0003 p0008
  have p0010 :=
    @gFntxp (synCvv) (synCvv) (synC1st) (synCcom (synCimage (synCswap)) (synC1st))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @gInidm (synCvv)
  have p0013 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) p0012
  have p0014 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      p0011 p0013
  have p0015 :=
    @gFncovv (synClndifop)
      (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) p0000 p0014
  have p0016 := (Nominal.classEqRefl (synClnpwasymfn))
  have p0017 :=
    @gFneq1i (synCvv) (synClnpwasymfn)
      (synCcom (synClndifop)
        (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))))
      p0016
  have p0018 :=
    @gMpbir (synWfn (synClnpwasymfn) (synCvv))
      (synWfn (synCcom (synClndifop)
          (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))) (synCvv))
      p0015 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_lnpwasymfnex`. -/
@[expose]
noncomputable def gLnpwasymfnex : Nominal.NPrf (.classMem (synClnpwasymfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwasymfn))
  have p0001 := @gLndifopex
  have p0002 := @gN1stex
  have p0003 := @gSwapex
  have p0004 := @gImageex (synCswap) p0003
  have p0006 := @gCoex (synCimage (synCswap)) (synC1st) p0004 p0002
  have p0007 :=
    @gTxpex (synC1st) (synCcom (synCimage (synCswap)) (synC1st)) p0002 p0006
  have p0008 :=
    @gCoex (synClndifop)
      (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) p0001 p0007
  have p0009 :=
    @gEqeltri (synClnpwasymfn)
      (synCcom (synClndifop)
        (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))))
      (synCvv) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_lnpwasymfnval`. -/
@[expose]
noncomputable def gLnpwasymfnval (D : Class) (R : Class)
    (hyp_lnpwasymfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwasymfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwasymfn) (synCop R D)) (synCdif R (synCcnv R))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwasymfn))
  have p0001 :=
    @gFveq1i (synCop R D) (synClnpwasymfn)
      (synCcom (synClndifop)
        (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))))
      p0000
  have p0002 := @gN1stfo
  have p0003 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gImageswapfn
  have p0009 := @gFncovv (synCimage (synCswap)) (synC1st) p0005 p0004
  have p0010 :=
    @gPm32i (synWfn (synC1st) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synC1st)) (synCvv)) p0004 p0009
  have p0011 :=
    @gFntxp (synCvv) (synCvv) (synC1st) (synCcom (synCimage (synCswap)) (synC1st))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gInidm (synCvv)
  have p0014 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) p0013
  have p0015 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      p0012 p0014
  have p0016 := @gOpex R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0017 :=
    @gPm32i
      (synWfn (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st))) (synCvv))
      (.classMem (synCop R D) (synCvv)) p0015 p0016
  have p0018 :=
    @gFvco2 (synCvv) (synCop R D) (synClndifop)
      (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))
  have p0019 := Nominal.mp p0017 p0018
  have p0029 :=
    @gFvtxpvv (synCop R D) (synC1st) (synCcom (synCimage (synCswap)) (synC1st))
      p0004 p0009 p0016
  have p0030 := @gOpfv1st R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0035 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (.classMem (synCop R D) (synCvv)) p0004
      p0016
  have p0036 := @gFvco2 (synCvv) (synCop R D) (synCimage (synCswap)) (synC1st)
  have p0037 := Nominal.mp p0035 p0036
  have p0039 :=
    @gFveq2i (synCfv (synC1st) (synCop R D)) R (synCimage (synCswap)) p0030
  have p0040 :=
    @gEqtri (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop R D))
      (synCfv (synCimage (synCswap)) (synCfv (synC1st) (synCop R D)))
      (synCfv (synCimage (synCswap)) R) p0037 p0039
  have p0041 := @gEqid (synCima (synCswap) R)
  have p0042 := @gSwapex
  have p0043 := @gImaex (synCswap) R p0042 hyp_lnpwasymfnval_1
  have p0044 :=
    @gBrimage R (synCima (synCswap) R) (synCswap) hyp_lnpwasymfnval_1 p0043
  have p0045 :=
    @gMpbir (synWbr R (synCimage (synCswap)) (synCima (synCswap) R))
      (.classEq (synCima (synCswap) R) (synCima (synCswap) R)) p0041 p0044
  have p0047 :=
    @gPm32i (synWfn (synCimage (synCswap)) (synCvv)) (.classMem R (synCvv)) p0005
      hyp_lnpwasymfnval_1
  have p0048 := @gFnbrfvb (synCvv) R (synCima (synCswap) R) (synCimage (synCswap))
  have p0049 := Nominal.mp p0047 p0048
  have p0050 :=
    @gMpbir (.classEq (synCfv (synCimage (synCswap)) R) (synCima (synCswap) R))
      (synWbr R (synCimage (synCswap)) (synCima (synCswap) R)) p0045 p0049
  have p0051 := @gDfcnv2 R
  have p0052 :=
    @gEqtr4i (synCfv (synCimage (synCswap)) R) (synCima (synCswap) R) (synCcnv R)
      p0050 p0051
  have p0053 :=
    @gEqtri (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop R D))
      (synCfv (synCimage (synCswap)) R) (synCcnv R) p0040 p0052
  have p0054 :=
    @gOpeq12i (synCfv (synC1st) (synCop R D)) R
      (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop R D)) (synCcnv R)
      p0030 p0053
  have p0055 :=
    @gEqtri
      (synCfv (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))
        (synCop R D))
      (synCop (synCfv (synC1st) (synCop R D))
        (synCfv (synCcom (synCimage (synCswap)) (synC1st)) (synCop R D)))
      (synCop R (synCcnv R)) p0029 p0054
  have p0056 :=
    @gFveq2i
      (synCfv (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))
        (synCop R D))
      (synCop R (synCcnv R)) (synClndifop) p0055
  have p0057 :=
    @gEqtri
      (synCfv (synCcom (synClndifop)
          (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))) (synCop R D))
      (synCfv (synClndifop)
        (synCfv (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))
          (synCop R D)))
      (synCfv (synClndifop) (synCop R (synCcnv R))) p0019 p0056
  have p0058 := (Nominal.classEqRefl (synCo R (synClndifop) (synCcnv R)))
  have p0059 :=
    @gEqcomi (synCo R (synClndifop) (synCcnv R))
      (synCfv (synClndifop) (synCop R (synCcnv R))) p0058
  have p0060 :=
    @gEqtri
      (synCfv (synCcom (synClndifop)
          (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))) (synCop R D))
      (synCfv (synClndifop) (synCop R (synCcnv R)))
      (synCo R (synClndifop) (synCcnv R)) p0057 p0059
  have p0061 := @gCnvex R hyp_lnpwasymfnval_1
  have p0062 :=
    @gPm32i (.classMem R (synCvv)) (.classMem (synCcnv R) (synCvv))
      hyp_lnpwasymfnval_1 p0061
  have p0063 := @gLndifopvalg R (synCcnv R) (synCvv) (synCvv)
  have p0064 := Nominal.mp p0062 p0063
  have p0065 :=
    @gEqtri
      (synCfv (synCcom (synClndifop)
          (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))) (synCop R D))
      (synCo R (synClndifop) (synCcnv R)) (synCdif R (synCcnv R)) p0060 p0064
  have p0066 :=
    @gEqtri (synCfv (synClnpwasymfn) (synCop R D))
      (synCfv (synCcom (synClndifop)
          (synCtxp (synC1st) (synCcom (synCimage (synCswap)) (synC1st)))) (synCop R D))
      (synCdif R (synCcnv R)) p0001 p0065
  exact p0066

/-- Checked nominal proof certificate identified upstream as `g_tc3lecan`. -/
@[expose]
noncomputable def gTc3lecan (M : Class) (N : Class)
    (hyp_tc3lecb_1 : Nominal.NPrf (.classMem M (synCncs)))
    (hyp_tc3lecb_2 : Nominal.NPrf (.classMem N (synCncs))) :
    Nominal.NPrf
      (.imp (synWbr (synCtc (synCtc (synCtc M))) (synClec) (synCtc (synCtc (synCtc N))))
        (synWbr M (synClec) N)) :=
  by
  have p0000 :=
    @gPm32i (.classMem M (synCncs)) (.classMem N (synCncs)) hyp_tc3lecb_1
      hyp_tc3lecb_2
  have p0001 := @gTlecg M N
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gTccl M
  have p0004 := Nominal.mp hyp_tc3lecb_1 p0003
  have p0005 := @gTccl N
  have p0006 := Nominal.mp hyp_tc3lecb_2 p0005
  have p0007 :=
    @gPm32i (.classMem (synCtc M) (synCncs)) (.classMem (synCtc N) (synCncs)) p0004
      p0006
  have p0008 := @gTlecg (synCtc M) (synCtc N)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gBitri (synWbr M (synClec) N) (synWbr (synCtc M) (synClec) (synCtc N))
      (synWbr (synCtc (synCtc M)) (synClec) (synCtc (synCtc N))) p0002 p0009
  have p0013 := @gTccl (synCtc M)
  have p0014 := Nominal.mp p0004 p0013
  have p0017 := @gTccl (synCtc N)
  have p0018 := Nominal.mp p0006 p0017
  have p0019 :=
    @gPm32i (.classMem (synCtc (synCtc M)) (synCncs))
      (.classMem (synCtc (synCtc N)) (synCncs)) p0014 p0018
  have p0020 := @gTlecg (synCtc (synCtc M)) (synCtc (synCtc N))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @gBitri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc M)) (synClec) (synCtc (synCtc N)))
      (synWbr (synCtc (synCtc (synCtc M))) (synClec) (synCtc (synCtc (synCtc N))))
      p0010 p0021
  have p0023 :=
    @gBiimpri (synWbr M (synClec) N)
      (synWbr (synCtc (synCtc (synCtc M))) (synClec) (synCtc (synCtc (synCtc N))))
      p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_fdifssa`. -/
@[expose]
noncomputable def gFdifssa (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv) : Nominal.NPrf (synWss (synCfdif R A B) A) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdif x y A B R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @gSsrab2
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))) d
      A dv_cache_0003
  have p0002 :=
    @gEqsstri (synCfdif R A B)
      (synCrab d A
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fdordwe2`. -/
@[expose]
noncomputable def gFdordwe2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv) (hyp_fdordwe2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdordwe2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdordwe2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (synWbr (synCfdord R A B) (synCwe) (synCfdif R A B))) :=
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
  have p0000 := @gId (synWbr R (synCwe) A)
  have p0001 := @gFdifssa A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 := @gA1i (synWss (synCfdif R A B) A) (synWbr R (synCwe) A) p0001
  have p0003 :=
    @gFdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdordwe2_1
      hyp_fdordwe2_2 hyp_fdordwe2_3
  have p0004 :=
    @gWerestrndv (synWbr R (synCwe) A) (synCfdif R A B) A R p0000 p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCfdord R A B))
  have p0006 :=
    @gBreq1i (synCfdord R A B) (synCin R (synCxp (synCfdif R A B) (synCfdif R A B)))
      (synCfdif R A B) (synCwe) p0005
  have p0007 :=
    @gSylibr (synWbr R (synCwe) A)
      (synWbr (synCin R (synCxp (synCfdif R A B) (synCfdif R A B))) (synCwe)
        (synCfdif R A B))
      (synWbr (synCfdord R A B) (synCwe) (synCfdif R A B)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ncpw1pw2`. -/
@[expose]
noncomputable def gNcpw1pw2 (A : Class)
    (hyp_ncpw1pw2_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCnc (synCpw1 (synCpw (synCpw A))))
        (synCnc (synCpw (synCpw (synCpw1 A))))) :=
  by
  have p0000 := @gPwex A hyp_ncpw1pw2_1
  have p0001 := @gEnpw1pw (synCpw A) p0000
  have p0002 := @gEnpw1pw A hyp_ncpw1pw2_1
  have p0003 := @gEnpw (synCpw1 (synCpw A)) (synCpw (synCpw1 A))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gPm32i
      (synWbr (synCpw1 (synCpw (synCpw A))) (synCen) (synCpw (synCpw1 (synCpw A))))
      (synWbr (synCpw (synCpw1 (synCpw A))) (synCen) (synCpw (synCpw (synCpw1 A))))
      p0001 p0004
  have p0006 :=
    @gEntr (synCpw1 (synCpw (synCpw A))) (synCpw (synCpw1 (synCpw A)))
      (synCpw (synCpw (synCpw1 A)))
  have p0007 := Nominal.mp p0005 p0006
  have p0009 := @gPwex (synCpw A) p0000
  have p0010 := @gPw1ex (synCpw (synCpw A)) p0009
  have p0011 :=
    @gEqnc (synCpw1 (synCpw (synCpw A))) (synCpw (synCpw (synCpw1 A))) p0010
  have p0012 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCpw (synCpw A))))
        (synCnc (synCpw (synCpw (synCpw1 A)))))
      (synWbr (synCpw1 (synCpw (synCpw A))) (synCen) (synCpw (synCpw (synCpw1 A))))
      p0007 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_tc3nc`. -/
@[expose]
noncomputable def gTc3nc (A : Class)
    (hyp_tc3nc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synCtc (synCnc A))))
        (synCnc (synCpw1 (synCpw1 (synCpw1 A))))) :=
  by
  have p0000 := @gTc2nc A hyp_tc3nc_1
  have p0001 := @gTceq (synCtc (synCtc (synCnc A))) (synCnc (synCpw1 (synCpw1 A)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gPw1ex A hyp_tc3nc_1
  have p0004 := @gPw1ex (synCpw1 A) p0003
  have p0005 := @gTcnc (synCpw1 (synCpw1 A)) p0004
  have p0006 :=
    @gEqtri (synCtc (synCtc (synCtc (synCnc A))))
      (synCtc (synCnc (synCpw1 (synCpw1 A))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 A)))) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_kqlefintcb`. -/
@[expose]
noncomputable def gKqlefintcb (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWb (synWbr M (synCkqrel (synClefin)) N)
          (synWbr (synCtc M) (synCkqrel (synClefin)) (synCtc N)))) :=
  by
  have p0000 := @gKqlefinbr M N (synCnnc) (synCnnc)
  have p0001 := @gTfinlefin M N
  have p0002 :=
    @gBitrd (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWbr M (synCkqrel (synClefin)) N) (.classMem (synCopk M N) (synClefin))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synClefin)) p0000 p0001
  have p0003 := @gSimpl (.classMem M (synCnnc)) (.classMem N (synCnnc))
  have p0004 := @gNntctfin M
  have p0005 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem M (synCnnc)) (.classEq (synCtc M) (synCtfin M)) p0003 p0004
  have p0006 := @gSimpr (.classMem M (synCnnc)) (.classMem N (synCnnc))
  have p0007 := @gNntctfin N
  have p0008 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem N (synCnnc)) (.classEq (synCtc N) (synCtfin N)) p0006 p0007
  have p0009 :=
    @gOpkeq12d (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) (synCtc M)
      (synCtfin M) (synCtc N) (synCtfin N) p0005 p0008
  have p0010 :=
    @gEleq1d (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synCopk (synCtc M) (synCtc N)) (synCopk (synCtfin M) (synCtfin N))
      (synClefin) p0009
  have p0011 :=
    @gBicomd (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCopk (synCtc M) (synCtc N)) (synClefin))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synClefin)) p0010
  have p0012 :=
    @gBitrd (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWbr M (synCkqrel (synClefin)) N)
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synClefin))
      (.classMem (synCopk (synCtc M) (synCtc N)) (synClefin)) p0002 p0011
  have p0014 := @gNntccl M
  have p0015 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem M (synCnnc)) (.classMem (synCtc M) (synCnnc)) p0003 p0014
  have p0017 := @gNntccl N
  have p0018 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem N (synCnnc)) (.classMem (synCtc N) (synCnnc)) p0006 p0017
  have p0019 :=
    @gJca (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCtc M) (synCnnc)) (.classMem (synCtc N) (synCnnc)) p0015 p0018
  have p0020 := @gKqlefinbr (synCtc M) (synCtc N) (synCnnc) (synCnnc)
  have p0021 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (.classMem (synCtc M) (synCnnc)) (.classMem (synCtc N) (synCnnc)))
      (synWb (synWbr (synCtc M) (synCkqrel (synClefin)) (synCtc N))
        (.classMem (synCopk (synCtc M) (synCtc N)) (synClefin)))
      p0019 p0020
  have p0022 :=
    @gBicomd (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWbr (synCtc M) (synCkqrel (synClefin)) (synCtc N))
      (.classMem (synCopk (synCtc M) (synCtc N)) (synClefin)) p0021
  have p0023 :=
    @gBitrd (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWbr M (synCkqrel (synClefin)) N)
      (.classMem (synCopk (synCtc M) (synCtc N)) (synClefin))
      (synWbr (synCtc M) (synCkqrel (synClefin)) (synCtc N)) p0012 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_tcnnresfn`. -/
@[expose]
noncomputable def gTcnnresfn :
    Nominal.NPrf
      (synWfn (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc))) :=
  by
  have p0000 := @gFntcfn
  have p0001 := @gPw1ss1c (synCnnc)
  have p0002 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (synWss (synCpw1 (synCnnc)) (synC1c))
      p0000 p0001
  have p0003 := @gFnssres (synC1c) (synCpw1 (synCnnc)) (synCtcfn)
  have p0004 := Nominal.mp p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_tcnnex`. -/
@[expose]
noncomputable def gTcnnex : Nominal.NPrf (.classMem (synCtcnn) (synCvv)) :=
  by
  have p0000 := @gTcfnex
  have p0001 := @gNncex
  have p0002 := @gPw1ex (synCnnc) p0001
  have p0003 := @gResex (synCtcfn) (synCpw1 (synCnnc)) p0000 p0002
  have p0004 := @gRnex (synCres (synCtcfn) (synCpw1 (synCnnc))) p0003
  have p0005 := (Nominal.classEqRefl (synCtcnn))
  have p0006 :=
    @gEleq1i (synCtcnn) (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) (synCvv)
      p0005
  have p0007 :=
    @gMpbir (.classMem (synCtcnn) (synCvv))
      (.classMem (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) (synCvv)) p0004
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_eltcnn`. -/
@[expose]
noncomputable def gEltcnn (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCtcnn)) (synWrex q (synCpw1 (synCnnc))
          (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))) :=
  by
  have dv_cache_0001 : q ∉ ((synCpw1 (synCnnc))).fv := by
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
  have dv_cache_0003 : q ∉ ((synCres (synCtcfn) (synCpw1 (synCnnc)))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCtcnn))
  have p0001 :=
    @gEleq2i (synCtcnn) (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) A p0000
  have p0002 := @gFntcfn
  have p0003 := @gPw1ss1c (synCnnc)
  have p0004 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (synWss (synCpw1 (synCnnc)) (synC1c))
      p0002 p0003
  have p0005 := @gFnssres (synC1c) (synCpw1 (synCnnc)) (synCtcfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gFvelrnb q (synCpw1 (synCnnc)) A (synCres (synCtcfn) (synCpw1 (synCnnc)))
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gBitri (.classMem A (synCtcnn))
      (.classMem A (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      p0001 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_tcfnfvcl`. -/
@[expose]
noncomputable def gTcfnfvcl (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCvv)) (.classEq (synCfv (synCtcfn) (synCsn B)) (synCtc B))) :=
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
    x ∉ ((Wff.classEq (synCfv (synCtcfn) (synCsn B)) (synCtc B))).fv :=
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
  have p0000 := @gSneq (.cv x) B
  have p0001 :=
    @gFveq2d (.classEq (.cv x) B) (synCsn (.cv x)) (synCsn B) (synCtcfn) p0000
  have p0002 := @gTceq (.cv x) B
  have p0003 :=
    @gEqeq12d (.classEq (.cv x) B) (synCfv (synCtcfn) (synCsn (.cv x)))
      (synCfv (synCtcfn) (synCsn B)) (synCtc (.cv x)) (synCtc B) p0001 p0002
  have p0004 := @gVex x
  have p0005 := @gTcfnfv (.cv x) p0004
  have p0006 :=
    @gVtoclg (.classEq (synCfv (synCtcfn) (synCsn (.cv x))) (synCtc (.cv x)))
      (.classEq (synCfv (synCtcfn) (synCsn B)) (synCtc B)) x B (synCvv) dv_cache_0001
      dv_cache_0002 p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_tcnnssnn`. -/
@[expose]
noncomputable def gTcnnssnn : Nominal.NPrf (synWss (synCtcnn) (synCnnc)) :=
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
  have dv_cache_0002 : p ∉ ((Wff.classMem (.cv q) (synCnnc))).fv :=
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
  have dv_cache_0003 : q ∉ ((synCtcnn)).fv :=
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
  have dv_cache_0004 : q ∉ ((synCnnc)).fv :=
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
  have p0000 := @gEltcnn (.cv q) p dv_cache_0001
  have p0001 :=
    @gBiimpi (.classMem (.cv q) (synCtcnn))
      (synWrex p (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      p0000
  have p0002 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q))
  have p0003 := @gHnwpw1argcl (synCnnc) p
  have p0004 :=
    @gSimpl (.classMem (synCuni (.cv p)) (synCnnc))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0005 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv p)) (synCnnc))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classMem (synCuni (.cv p)) (synCnnc)) p0003 p0004
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (.classMem (.cv p) (synCpw1 (synCnnc))) (.classMem (synCuni (.cv p)) (synCnnc))
      p0002 p0005
  have p0007 := @gNntccl (synCuni (.cv p))
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (.classMem (synCuni (.cv p)) (synCnnc))
      (.classMem (synCtc (synCuni (.cv p))) (synCnnc)) p0006 p0007
  have p0010 := @gFvres (.cv p) (synCpw1 (synCnnc)) (synCtcfn)
  have p0012 :=
    @gSimpr (.classMem (synCuni (.cv p)) (synCnnc))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0013 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv p)) (synCnnc))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0003 p0012
  have p0014 :=
    @gFveq2d (.classMem (.cv p) (synCpw1 (synCnnc))) (.cv p)
      (synCsn (synCuni (.cv p))) (synCtcfn) p0013
  have p0015 :=
    @gEqtrd (.classMem (.cv p) (synCpw1 (synCnnc)))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCfv (synCtcfn) (.cv p)) (synCfv (synCtcfn) (synCsn (synCuni (.cv p))))
      p0010 p0014
  have p0019 := @gElex (synCuni (.cv p)) (synCnnc)
  have p0020 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classMem (synCuni (.cv p)) (synCnnc)) (.classMem (synCuni (.cv p)) (synCvv))
      p0005 p0019
  have p0021 := @gTcfnfvcl (synCuni (.cv p))
  have p0022 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classMem (synCuni (.cv p)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv p)))) (synCtc (synCuni (.cv p))))
      p0020 p0021
  have p0023 :=
    @gEqtrd (.classMem (.cv p) (synCpw1 (synCnnc)))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv p)))) (synCtc (synCuni (.cv p)))
      p0015 p0022
  have p0024 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
        (synCtc (synCuni (.cv p))))
      p0002 p0023
  have p0025 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q))
  have p0026 :=
    @gEqtr3d
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCtc (synCuni (.cv p))) (.cv q) p0024 p0025
  have p0027 :=
    @gEleq1d
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (synCtc (synCuni (.cv p))) (.cv q) (synCnnc) p0026
  have p0028 :=
    @gMpbid
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (.classMem (synCtc (synCuni (.cv p))) (synCnnc)) (.classMem (.cv q) (synCnnc))
      p0008 p0027
  have p0029 :=
    @gRexlimiva
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q))
      (.classMem (.cv q) (synCnnc)) p (synCpw1 (synCnnc)) dv_cache_0002 p0028
  have p0030 :=
    @gSyl (.classMem (.cv q) (synCtcnn))
      (synWrex p (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p)) (.cv q)))
      (.classMem (.cv q) (synCnnc)) p0001 p0029
  have p0031 := @gSsriv q (synCtcnn) (synCnnc) dv_cache_0003 dv_cache_0004 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_nntcsuc`. -/
@[expose]
noncomputable def gNntcsuc (N : Class) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc))
        (.classEq (synCtc (synCplc N (synC1c))) (synCplc (synCtc N) (synC1c)))) :=
  by
  have p0000 := @gNnnc N
  have p0001 := @gN1cnc
  have p0002 := @gA1i (.classMem (synC1c) (synCncs)) (.classMem N (synCnnc)) p0001
  have p0003 :=
    @gJca (.classMem N (synCnnc)) (.classMem N (synCncs))
      (.classMem (synC1c) (synCncs)) p0000 p0002
  have p0004 := @gTcdi N (synC1c)
  have p0005 :=
    @gSyl (.classMem N (synCnnc))
      (synWa (.classMem N (synCncs)) (.classMem (synC1c) (synCncs)))
      (.classEq (synCtc (synCplc N (synC1c))) (synCplc (synCtc N) (synCtc (synC1c))))
      p0003 p0004
  have p0006 := @gTc1c
  have p0007 :=
    @gA1i (.classEq (synCtc (synC1c)) (synC1c)) (.classMem N (synCnnc)) p0006
  have p0008 :=
    @gAddceq2d (.classMem N (synCnnc)) (synCtc (synC1c)) (synC1c) (synCtc N) p0007
  have p0009 :=
    @gEqtrd (.classMem N (synCnnc)) (synCtc (synCplc N (synC1c)))
      (synCplc (synCtc N) (synCtc (synC1c))) (synCplc (synCtc N) (synC1c)) p0005
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

/-- Checked nominal proof certificate identified upstream as `g_nntctcnn`. -/
@[expose]
noncomputable def gNntctcnn (N : Class) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classMem (synCtc N) (synCtcnn))) :=
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
  have dv_cache_0001 : q ∉ ((synCsn N)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_q_not_N,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCpw1 (synCnnc))).fv :=
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
      ((Wff.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N))
          (synCtc N))).fv :=
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
  have dv_cache_0004 : q ∉ ((synCtc N)).fv :=
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
  have p0000 := @gSnelpw1 N (synCnnc)
  have p0001 :=
    @gBiimpri (.classMem (synCsn N) (synCpw1 (synCnnc))) (.classMem N (synCnnc))
      p0000
  have p0004 := @gFvres (synCsn N) (synCpw1 (synCnnc)) (synCtcfn)
  have p0005 :=
    @gSyl (.classMem N (synCnnc)) (.classMem (synCsn N) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N))
        (synCfv (synCtcfn) (synCsn N)))
      p0001 p0004
  have p0006 := @gId (.classMem N (synCnnc))
  have p0007 := @gElex N (synCnnc)
  have p0008 :=
    @gSyl (.classMem N (synCnnc)) (.classMem N (synCnnc)) (.classMem N (synCvv)) p0006
      p0007
  have p0009 := @gTcfnfvcl N
  have p0010 :=
    @gSyl (.classMem N (synCnnc)) (.classMem N (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn N)) (synCtc N)) p0008 p0009
  have p0011 :=
    @gEqtrd (.classMem N (synCnnc))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N))
      (synCfv (synCtcfn) (synCsn N)) (synCtc N) p0005 p0010
  have p0012 :=
    @gJca (.classMem N (synCnnc)) (.classMem (synCsn N) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N)) (synCtc N))
      p0001 p0011
  have p0013 := @gId (.classEq (.cv q) (synCsn N))
  have p0014 :=
    @gFveq2d (.classEq (.cv q) (synCsn N)) (.cv q) (synCsn N)
      (synCres (synCtcfn) (synCpw1 (synCnnc))) p0013
  have p0015 :=
    @gEqeq1d (.classEq (.cv q) (synCsn N))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N)) (synCtc N) p0014
  have p0016 :=
    @gRspcev
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) (synCtc N))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N)) (synCtc N))
      q (synCsn N) (synCpw1 (synCnnc)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @gSyl (.classMem N (synCnnc))
      (synWa (.classMem (synCsn N) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCsn N))
          (synCtc N)))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) (synCtc N)))
      p0012 p0016
  have p0018 := @gEltcnn (synCtc N) q dv_cache_0004
  have p0019 :=
    @gBiimpri (.classMem (synCtc N) (synCtcnn))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) (synCtc N)))
      p0018
  have p0020 :=
    @gSyl (.classMem N (synCnnc))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) (synCtc N)))
      (.classMem (synCtc N) (synCtcnn)) p0017 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_tcnnsuc`. -/
@[expose]
noncomputable def gTcnnsuc (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCtcnn)) (.classMem (synCplc A (synC1c)) (synCtcnn))) :=
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
  have dv_cache_0002 : q ∉ ((Wff.classMem (synCplc A (synC1c)) (synCtcnn))).fv :=
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
  have p0000 := @gEltcnn A q dv_cache_0001
  have p0001 :=
    @gBiimpi (.classMem A (synCtcnn))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      p0000
  have p0002 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A)
  have p0003 := @gHnwpw1argcl (synCnnc) q
  have p0004 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0005 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synCnnc)) p0003 p0004
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (.cv q) (synCpw1 (synCnnc))) (.classMem (synCuni (.cv q)) (synCnnc))
      p0002 p0005
  have p0007 := @gPeano2 (synCuni (.cv q))
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (synCuni (.cv q)) (synCnnc))
      (.classMem (synCplc (synCuni (.cv q)) (synC1c)) (synCnnc)) p0006 p0007
  have p0009 := @gNntctcnn (synCplc (synCuni (.cv q)) (synC1c))
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (synCplc (synCuni (.cv q)) (synC1c)) (synCnnc))
      (.classMem (synCtc (synCplc (synCuni (.cv q)) (synC1c))) (synCtcnn)) p0008
      p0009
  have p0016 := @gNntcsuc (synCuni (.cv q))
  have p0017 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (synCtc (synCplc (synCuni (.cv q)) (synC1c)))
        (synCplc (synCtc (synCuni (.cv q))) (synC1c)))
      p0006 p0016
  have p0019 := @gFvres (.cv q) (synCpw1 (synCnnc)) (synCtcfn)
  have p0020 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
        (synCfv (synCtcfn) (.cv q)))
      p0002 p0019
  have p0023 :=
    @gSimpr (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0024 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0003 p0023
  have p0025 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCnnc))) (.cv q)
      (synCsn (synCuni (.cv q))) (synCtcfn) p0024
  have p0026 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCtcfn) (.cv q))
        (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))))
      p0002 p0025
  have p0027 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCtcfn) (.cv q)) (synCfv (synCtcfn) (synCsn (synCuni (.cv q))))
      p0020 p0026
  have p0032 := @gElex (synCuni (.cv q)) (synCnnc)
  have p0033 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classMem (synCuni (.cv q)) (synCnnc)) (.classMem (synCuni (.cv q)) (synCvv))
      p0005 p0032
  have p0034 := @gTcfnfvcl (synCuni (.cv q))
  have p0035 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classMem (synCuni (.cv q)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q))))
      p0033 p0034
  have p0036 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q))))
      p0002 p0035
  have p0037 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q)))
      p0027 p0036
  have p0038 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A)
  have p0039 :=
    @gEqtr3d
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCtc (synCuni (.cv q))) A p0037 p0038
  have p0040 :=
    @gAddceq1d
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (synCtc (synCuni (.cv q))) A (synC1c) p0039
  have p0041 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (synCtc (synCplc (synCuni (.cv q)) (synC1c)))
      (synCplc (synCtc (synCuni (.cv q))) (synC1c)) (synCplc A (synC1c)) p0017 p0040
  have p0042 :=
    @gEleq1d
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (synCtc (synCplc (synCuni (.cv q)) (synC1c))) (synCplc A (synC1c)) (synCtcnn)
      p0041
  have p0043 :=
    @gMpbid
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (synCtc (synCplc (synCuni (.cv q)) (synC1c))) (synCtcnn))
      (.classMem (synCplc A (synC1c)) (synCtcnn)) p0010 p0042
  have p0044 :=
    @gRexlimiva
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A)
      (.classMem (synCplc A (synC1c)) (synCtcnn)) q (synCpw1 (synCnnc)) dv_cache_0002
      p0043
  have p0045 :=
    @gSyl (.classMem A (synCtcnn))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) A))
      (.classMem (synCplc A (synC1c)) (synCtcnn)) p0001 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_nntcnn`. -/
@[expose]
noncomputable def gNntcnn (N : Class) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classMem N (synCtcnn))) :=
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
  have dv_cache_0001 : x ∉ ((synCtcnn)).fv := by
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
  have dv_cache_0003 : x ∉ ((Wff.classMem (.cv y) (synCtcnn))).fv :=
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
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) (synCtcnn))).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (synC0c) (synCtcnn))).fv :=
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
  have dv_cache_0006 : x ∉ ((Wff.classMem N (synCtcnn))).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classMem (synCplc (.cv y) (synC1c)) (synCtcnn))).fv :=
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
  have p0000 := @gTcnnex
  have p0001 := @gAbid2 x (synCtcnn) dv_cache_0001
  have p0002 :=
    @gEleq1i (.cab x (.classMem (.cv x) (synCtcnn))) (synCtcnn) (synCvv) p0001
  have p0003 :=
    @gMpbir (.classMem (.cab x (.classMem (.cv x) (synCtcnn))) (synCvv))
      (.classMem (synCtcnn) (synCvv)) p0000 p0002
  have p0004 := @gId (.classEq (.cv x) (synC0c))
  have p0005 := @gEleq1d (.classEq (.cv x) (synC0c)) (.cv x) (synC0c) (synCtcnn) p0004
  have p0006 := @gId (.classEq (.cv x) (.cv y))
  have p0007 := @gEleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) (synCtcnn) p0006
  have p0008 := @gId (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
  have p0009 :=
    @gEleq1d (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.cv x)
      (synCplc (.cv y) (synC1c)) (synCtcnn) p0008
  have p0010 := @gId (.classEq (.cv x) N)
  have p0011 := @gEleq1d (.classEq (.cv x) N) (.cv x) N (synCtcnn) p0010
  have p0012 := @gPeano1
  have p0013 := @gNntctcnn (synC0c)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @gTc0c
  have p0016 := @gEleq1i (synCtc (synC0c)) (synC0c) (synCtcnn) p0015
  have p0017 :=
    @gMpbi (.classMem (synCtc (synC0c)) (synCtcnn)) (.classMem (synC0c) (synCtcnn))
      p0014 p0016
  have p0018 := @gTcnnsuc (.cv y)
  have p0019 :=
    @gA1i
      (.imp (.classMem (.cv y) (synCtcnn))
        (.classMem (synCplc (.cv y) (synC1c)) (synCtcnn)))
      (.classMem (.cv y) (synCnnc)) p0018
  have p0020_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y)
        (synWb (.classMem (.cv x) (synCtcnn)) (.classMem (.cv y) (synCtcnn)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCtcnn synCrn synCima synWrex synWex synWa synWbr synCop
          synCun synCnin synWnan synCcompl synCvv synCres synCin synCxp synCopab
          synCtcfn synCmpt synC1c synCtc synCio synCuni synCsn synCpw1 synCnnc
          synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0020 :=
    @gFinds (.classMem (.cv x) (synCtcnn)) (.classMem (synC0c) (synCtcnn))
      (.classMem (.cv y) (synCtcnn)) (.classMem (synCplc (.cv y) (synC1c)) (synCtcnn))
      (.classMem N (synCtcnn)) x y N dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0003 p0005
      p0020_e02_recanon p0009 p0011 p0017 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_tcnnfo`. -/
@[expose]
noncomputable def gTcnnfo :
    Nominal.NPrf
      (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  have dv_cache_0001 : q ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCtcnn)).fv :=
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
  have p0000 := @gTcnnresfn
  have p0001 := (Nominal.classEqRefl (synCtcnn))
  have p0002 :=
    @gEqcomi (synCtcnn) (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) p0001
  have p0003 := @gTcnnssnn
  have p0004 := @gNntcnn (.cv q)
  have p0005 := @gSsriv q (synCnnc) (synCtcnn) dv_cache_0001 dv_cache_0002 p0004
  have p0006 := @gEqssi (synCtcnn) (synCnnc) p0003 p0005
  have p0007 :=
    @gEqtri (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) (synCtcnn) (synCnnc)
      p0002 p0006
  have p0008 :=
    @gPm32i (synWfn (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)))
      (.classEq (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) (synCnnc)) p0000
      p0007
  have p0009 :=
    (Nominal.biimpRefl
      (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc)))
  have p0010 :=
    @gMpbir
      (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (synWa (synWfn (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)))
        (.classEq (synCrn (synCres (synCtcfn) (synCpw1 (synCnnc)))) (synCnnc)))
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

/-- Checked nominal proof certificate identified upstream as `g_tcnnf1`. -/
@[expose]
noncomputable def gTcnnf1 :
    Nominal.NPrf
      (synWf1 (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : q ∉ ((Wff.classMem (.cv p) (synCpw1 (synCnnc)))).fv := by
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
  have dv_cache_0002 : p ∉ ((synCpw1 (synCnnc))).fv :=
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
  have dv_cache_0003 : q ∉ ((synCpw1 (synCnnc))).fv :=
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
  have dv_cache_0004 : p ∉ ((synCres (synCtcfn) (synCpw1 (synCnnc)))).fv :=
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
  have dv_cache_0005 : q ∉ ((synCres (synCtcfn) (synCpw1 (synCnnc)))).fv :=
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
  have p0000 := @gTcnnfo
  have p0001 :=
    @gFof (synCpw1 (synCnnc)) (synCnnc) (synCres (synCtcfn) (synCpw1 (synCnnc)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gSimpl
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classMem (.cv q) (synCpw1 (synCnnc))))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
        (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
  have p0004 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classMem (.cv q) (synCpw1 (synCnnc))))
      (.classMem (.cv p) (synCpw1 (synCnnc))) p0003 p0004
  have p0006 := @gHnwpw1argcl (synCnnc) p
  have p0007 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv p) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv p)) (synCnnc))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      p0005 p0006
  have p0008 :=
    @gSimpr (.classMem (synCuni (.cv p)) (synCnnc))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synCnnc))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0007 p0008
  have p0013 := @gFvres (.cv p) (synCpw1 (synCnnc)) (synCtcfn)
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
        (synCfv (synCtcfn) (.cv p)))
      p0005 p0013
  have p0022 :=
    @gFveq2d
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.cv p) (synCsn (synCuni (.cv p))) (synCtcfn) p0009
  have p0023 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCfv (synCtcfn) (.cv p)) (synCfv (synCtcfn) (synCsn (synCuni (.cv p))))
      p0014 p0022
  have p0029 :=
    @gSimpl (.classMem (synCuni (.cv p)) (synCnnc))
      (.classEq (.cv p) (synCsn (synCuni (.cv p))))
  have p0030 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synCnnc))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      (.classMem (synCuni (.cv p)) (synCnnc)) p0007 p0029
  have p0031 := @gElex (synCuni (.cv p)) (synCnnc)
  have p0032 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCnnc)) (.classMem (synCuni (.cv p)) (synCvv))
      p0030 p0031
  have p0033 := @gTcfnfvcl (synCuni (.cv p))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv p)))) (synCtc (synCuni (.cv p))))
      p0032 p0033
  have p0035 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv p)))) (synCtc (synCuni (.cv p)))
      p0023 p0034
  have p0036 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCtc (synCuni (.cv p))) p0035
  have p0037 :=
    @gSimpr
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classMem (.cv q) (synCpw1 (synCnnc))))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
        (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
  have p0038 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCtc (synCuni (.cv p)))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)) p0036 p0037
  have p0040 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
  have p0041 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classMem (.cv q) (synCpw1 (synCnnc))))
      (.classMem (.cv q) (synCpw1 (synCnnc))) p0003 p0040
  have p0042 := @gFvres (.cv q) (synCpw1 (synCnnc)) (synCtcfn)
  have p0043 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
        (synCfv (synCtcfn) (.cv q)))
      p0041 p0042
  have p0047 := @gHnwpw1argcl (synCnnc) q
  have p0048 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0041 p0047
  have p0049 :=
    @gSimpr (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0050 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0048 p0049
  have p0051 :=
    @gFveq2d
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.cv q) (synCsn (synCuni (.cv q))) (synCtcfn) p0050
  have p0052 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCtcfn) (.cv q)) (synCfv (synCtcfn) (synCsn (synCuni (.cv q))))
      p0043 p0051
  have p0058 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0059 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synCnnc)) p0048 p0058
  have p0060 := @gElex (synCuni (.cv q)) (synCnnc)
  have p0061 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCnnc)) (.classMem (synCuni (.cv q)) (synCvv))
      p0059 p0060
  have p0062 := @gTcfnfvcl (synCuni (.cv q))
  have p0063 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q))))
      p0061 p0062
  have p0064 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q)))
      p0052 p0063
  have p0065 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCtc (synCuni (.cv p)))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCtc (synCuni (.cv q))) p0038 p0064
  have p0073 := @gNnnc (synCuni (.cv p))
  have p0074 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCnnc)) (.classMem (synCuni (.cv p)) (synCncs))
      p0030 p0073
  have p0082 := @gNnnc (synCuni (.cv q))
  have p0083 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCnnc)) (.classMem (synCuni (.cv q)) (synCncs))
      p0059 p0082
  have p0084 :=
    @gJca
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCncs)) (.classMem (synCuni (.cv q)) (synCncs))
      p0074 p0083
  have p0085 := @gTc11 (synCuni (.cv p)) (synCuni (.cv q))
  have p0086 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synCncs))
        (.classMem (synCuni (.cv q)) (synCncs)))
      (synWb (.classEq (synCtc (synCuni (.cv p))) (synCtc (synCuni (.cv q))))
        (.classEq (synCuni (.cv p)) (synCuni (.cv q))))
      p0084 p0085
  have p0087 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classEq (synCtc (synCuni (.cv p))) (synCtc (synCuni (.cv q))))
      (.classEq (synCuni (.cv p)) (synCuni (.cv q))) p0065 p0086
  have p0088 :=
    @gSneqd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCuni (.cv p)) (synCuni (.cv q)) p0087
  have p0089 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.cv p) (synCsn (synCuni (.cv p))) (synCsn (synCuni (.cv q))) p0009 p0088
  have p0097 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.cv q) (synCsn (synCuni (.cv q))) p0050
  have p0098 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
          (.classMem (.cv q) (synCpw1 (synCnnc))))
        (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.cv p) (synCsn (synCuni (.cv q))) (.cv q) p0089 p0097
  have p0099 :=
    @gEx
      (synWa (.classMem (.cv p) (synCpw1 (synCnnc)))
        (.classMem (.cv q) (synCpw1 (synCnnc))))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
        (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
      (.classEq (.cv p) (.cv q)) p0098
  have p0100 :=
    @gEx (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.imp (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
        (.classEq (.cv p) (.cv q)))
      p0099
  have p0101 :=
    @gRalrimiv (.classMem (.cv p) (synCpw1 (synCnnc)))
      (.imp (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
          (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
        (.classEq (.cv p) (.cv q)))
      q (synCpw1 (synCnnc)) dv_cache_0001 p0100
  have p0102 :=
    @gRgen
      (synWral q (synCpw1 (synCnnc)) (.imp
          (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
            (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
          (.classEq (.cv p) (.cv q))))
      p (synCpw1 (synCnnc)) p0101
  have p0103 :=
    @gPm32i
      (synWf (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (synWral p (synCpw1 (synCnnc)) (synWral q (synCpw1 (synCnnc)) (.imp
            (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
              (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
            (.classEq (.cv p) (.cv q)))))
      p0002 p0102
  have p0104 :=
    @gDff13 p q (synCpw1 (synCnnc)) (synCnnc)
      (synCres (synCtcfn) (synCpw1 (synCnnc))) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0105_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc))
          (synCnnc)) (synWa
          (synWf (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
          (synWral p (synCpw1 (synCnnc)) (synWral q (synCpw1 (synCnnc)) (.imp
                (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
                  (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
                (.classEq (.cv p) (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synCres synCtcfn synCmpt
          synC1c synCtc synCio synCuni synCsn synCpw1 synCnnc synCint
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
    @gMpbir
      (synWf1 (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (synWa (synWf (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc))
          (synCnnc)) (synWral p (synCpw1 (synCnnc)) (synWral q (synCpw1 (synCnnc)) (.imp
              (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv p))
                (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
              (.classEq (.cv p) (.cv q))))))
      p0103 p0105_e01_recanon
  exact p0105

/-- Checked nominal proof certificate identified upstream as `g_tcnnf1o`. -/
@[expose]
noncomputable def gTcnnf1o :
    Nominal.NPrf
      (synWf1o (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc))
        (synCnnc)) :=
  by
  have p0000 := @gTcnnf1
  have p0001 := @gTcnnfo
  have p0002 :=
    @gPm32i
      (synWf1 (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      p0000 p0001
  have p0003 :=
    (Nominal.biimpRefl
      (synWf1o (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc)))
  have p0004 :=
    @gMpbir
      (synWf1o (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (synWa (synWf1 (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc))
          (synCnnc))
        (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc)))
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nntcpreim`. -/
@[expose]
noncomputable def gNntcpreim (x : Var) (P : Class) (dv_P_x : x ∉ P.fv) :
    Nominal.NPrf
      (.imp (.classMem P (synCnnc)) (synWrex x (synCnnc) (.classEq (synCtc (.cv x)) P))) :=
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
  have dv_cache_0001 : q ∉ ((synCpw1 (synCnnc))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCnnc)).fv :=
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
  have dv_cache_0004 : q ∉ ((synCres (synCtcfn) (synCpw1 (synCnnc)))).fv :=
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
  have dv_cache_0005 : x ∉ ((synCuni (.cv q))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCnnc)).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classEq (synCtc (synCuni (.cv q))) P)).fv :=
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
  have dv_cache_0008 : q ∉ ((synWrex x (synCnnc) (.classEq (synCtc (.cv x)) P))).fv :=
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
  have p0000 := @gTcnnfo
  have p0001 :=
    @gA1i
      (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (.classMem P (synCnnc)) p0000
  have p0002 := @gId (.classMem P (synCnnc))
  have p0003 :=
    @gJca (.classMem P (synCnnc))
      (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc))
      (.classMem P (synCnnc)) p0001 p0002
  have p0004 :=
    @gFoelrn q (synCpw1 (synCnnc)) (synCnnc) P
      (synCres (synCtcfn) (synCpw1 (synCnnc))) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004
  have p0005 :=
    @gSyl (.classMem P (synCnnc))
      (synWa (synWfo (synCres (synCtcfn) (synCpw1 (synCnnc))) (synCpw1 (synCnnc))
          (synCnnc)) (.classMem P (synCnnc)))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      p0003 p0004
  have p0006 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
  have p0007 := @gHnwpw1argcl (synCnnc) q
  have p0008 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0009 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synCnnc)) p0007 p0008
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCnnc))) (.classMem (synCuni (.cv q)) (synCnnc))
      p0006 p0009
  have p0011 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
  have p0013 := @gFvres (.cv q) (synCpw1 (synCnnc)) (synCtcfn)
  have p0014 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
        (synCfv (synCtcfn) (.cv q)))
      p0006 p0013
  have p0017 :=
    @gSimpr (.classMem (synCuni (.cv q)) (synCnnc))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0018 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCnnc)))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0007 p0017
  have p0019 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCnnc)))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0006 p0018
  have p0020 :=
    @gFveq2d
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.cv q) (synCsn (synCuni (.cv q))) (synCtcfn) p0019
  have p0021 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCtcfn) (.cv q)) (synCfv (synCtcfn) (synCsn (synCuni (.cv q))))
      p0014 p0020
  have p0027 := @gElex (synCuni (.cv q)) (synCnnc)
  have p0028 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCnnc)) (.classMem (synCuni (.cv q)) (synCvv))
      p0010 p0027
  have p0029 := @gTcfnfvcl (synCuni (.cv q))
  have p0030 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q))))
      p0028 p0029
  have p0031 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q)))
      p0021 p0030
  have p0032 :=
    @gEqtrd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))
      (synCtc (synCuni (.cv q))) p0011 p0031
  have p0033 :=
    @gEqcomd
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      P (synCtc (synCuni (.cv q))) p0032
  have p0034 :=
    @gJca
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCnnc)) (.classEq (synCtc (synCuni (.cv q))) P)
      p0010 p0033
  have p0035 := @gTceq (.cv x) (synCuni (.cv q))
  have p0036 :=
    @gEqeq1d (.classEq (.cv x) (synCuni (.cv q))) (synCtc (.cv x))
      (synCtc (synCuni (.cv q))) P p0035
  have p0037 :=
    @gRspcev (.classEq (synCtc (.cv x)) P) (.classEq (synCtc (synCuni (.cv q))) P) x
      (synCuni (.cv q)) (synCnnc) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0036
  have p0038 :=
    @gSyl
      (synWa (.classMem (.cv q) (synCpw1 (synCnnc)))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWa (.classMem (synCuni (.cv q)) (synCnnc))
        (.classEq (synCtc (synCuni (.cv q))) P))
      (synWrex x (synCnnc) (.classEq (synCtc (.cv x)) P)) p0034 p0037
  have p0039 :=
    @gRexlimiva
      (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q)))
      (synWrex x (synCnnc) (.classEq (synCtc (.cv x)) P)) q (synCpw1 (synCnnc))
      dv_cache_0008 p0038
  have p0040 :=
    @gSyl (.classMem P (synCnnc))
      (synWrex q (synCpw1 (synCnnc))
        (.classEq P (synCfv (synCres (synCtcfn) (synCpw1 (synCnnc))) (.cv q))))
      (synWrex x (synCnnc) (.classEq (synCtc (.cv x)) P)) p0005 p0039
  exact p0040

/-- Checked nominal proof certificate identified upstream as `g_pwpullex`. -/
@[expose]
noncomputable def gPwpullex (R : Class) (F : Class)
    (hyp_pwpullex_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_pwpullex_2 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classMem (synCpwpull F R) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpwpull F R))
  have p0001 := @gCnvex F hyp_pwpullex_1
  have p0002 := @gCoex (synCcnv F) R p0001 hyp_pwpullex_2
  have p0003 := @gCoex (synCcom (synCcnv F) R) F p0002 hyp_pwpullex_1
  have p0004 :=
    @gEqeltri (synCpwpull F R) (synCcom (synCcom (synCcnv F) R) F) (synCvv) p0000
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

/-- Checked nominal proof certificate identified upstream as `g_ellntpcndv`. -/
@[expose]
noncomputable def gEllntpcndv (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv)
    (hyp_ellntpcndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ellntpcndv_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_ellntpcndv_3 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop R D) (synClntpc A)) (synWa (synWa
            (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
              (synWbr R (synCconnex) D)) (synWss R (synCxp D D))) (.classEq D A))) :=
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
  have dv_cache_0001 : u ∉ ((synCop R D)).fv := by
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
      ((synWb (.classMem (synCop R D) (synChwrels))
          (synWss (synCfv (synC1st) (synCop R D))
            (synCxp (synCfv (synC2nd) (synCop R D))
              (synCfv (synC2nd) (synCop R D)))))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synClntpc A))
  have p0001 :=
    @gEleq2i (synClntpc A)
      (synCin (synCin (synClntp) (synChwrels)) (synCxp (synCvv) (synCsn A)))
      (synCop R D) p0000
  have p0002 :=
    @gElin (synCop R D) (synCin (synClntp) (synChwrels))
      (synCxp (synCvv) (synCsn A))
  have p0003 := @gElin (synCop R D) (synClntp) (synChwrels)
  have p0004 := (Nominal.classEqRefl (synClntp))
  have p0005 :=
    @gEleq2i (synClntp) (synCin (synCin (synCref) (synCtrans)) (synCconnex))
      (synCop R D) p0004
  have p0006 := @gElin (synCop R D) (synCin (synCref) (synCtrans)) (synCconnex)
  have p0007 := @gElin (synCop R D) (synCref) (synCtrans)
  have p0008 := (Nominal.biimpRefl (synWbr R (synCref) D))
  have p0009 :=
    @gBicomi (synWbr R (synCref) D) (.classMem (synCop R D) (synCref)) p0008
  have p0010 := (Nominal.biimpRefl (synWbr R (synCtrans) D))
  have p0011 :=
    @gBicomi (synWbr R (synCtrans) D) (.classMem (synCop R D) (synCtrans)) p0010
  have p0012 :=
    @gAnbi12i (.classMem (synCop R D) (synCref)) (synWbr R (synCref) D)
      (.classMem (synCop R D) (synCtrans)) (synWbr R (synCtrans) D) p0009 p0011
  have p0013 :=
    @gBitri (.classMem (synCop R D) (synCin (synCref) (synCtrans)))
      (synWa (.classMem (synCop R D) (synCref)) (.classMem (synCop R D) (synCtrans)))
      (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D)) p0007 p0012
  have p0014 := (Nominal.biimpRefl (synWbr R (synCconnex) D))
  have p0015 :=
    @gBicomi (synWbr R (synCconnex) D) (.classMem (synCop R D) (synCconnex)) p0014
  have p0016 :=
    @gAnbi12i (.classMem (synCop R D) (synCin (synCref) (synCtrans)))
      (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
      (.classMem (synCop R D) (synCconnex)) (synWbr R (synCconnex) D) p0013 p0015
  have p0017 :=
    @gBitri
      (.classMem (synCop R D) (synCin (synCin (synCref) (synCtrans)) (synCconnex)))
      (synWa (.classMem (synCop R D) (synCin (synCref) (synCtrans)))
        (.classMem (synCop R D) (synCconnex)))
      (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
        (synWbr R (synCconnex) D))
      p0006 p0016
  have p0018 :=
    @gBitri (.classMem (synCop R D) (synClntp))
      (.classMem (synCop R D) (synCin (synCin (synCref) (synCtrans)) (synCconnex)))
      (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
        (synWbr R (synCconnex) D))
      p0005 p0017
  have p0019 := @gOpex R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0020 := @gEleq1 (.cv u) (synCop R D) (synChwrels)
  have p0021 := @gFveq2 (.cv u) (synCop R D) (synC1st)
  have p0022 := @gFveq2 (.cv u) (synCop R D) (synC2nd)
  have p0024 :=
    @gXpeq12d (.classEq (.cv u) (synCop R D)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (synCop R D)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (synCop R D)) p0022 p0022
  have p0025 :=
    @gSseq12d (.classEq (.cv u) (synCop R D)) (synCfv (synC1st) (.cv u))
      (synCfv (synC1st) (synCop R D))
      (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCxp (synCfv (synC2nd) (synCop R D)) (synCfv (synC2nd) (synCop R D)))
      p0021 p0024
  have p0026 :=
    @gBibi12d (.classEq (.cv u) (synCop R D)) (.classMem (.cv u) (synChwrels))
      (.classMem (synCop R D) (synChwrels))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (synCop R D))
        (synCxp (synCfv (synC2nd) (synCop R D)) (synCfv (synC2nd) (synCop R D))))
      p0020 p0025
  have p0027 := @gElhwrrels u
  have p0028 :=
    @gVtoclg
      (synWb (.classMem (.cv u) (synChwrels)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (synWb (.classMem (synCop R D) (synChwrels))
        (synWss (synCfv (synC1st) (synCop R D)) (synCxp (synCfv (synC2nd) (synCop R D))
            (synCfv (synC2nd) (synCop R D)))))
      u (synCop R D) (synCvv) dv_cache_0001 dv_cache_0002 p0026 p0027
  have p0029 := Nominal.mp p0019 p0028
  have p0030 := @gOpfv1st R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0031 := @gOpfv2nd R D hyp_ellntpcndv_2 hyp_ellntpcndv_3
  have p0033 :=
    @gXpeq12i (synCfv (synC2nd) (synCop R D)) D (synCfv (synC2nd) (synCop R D)) D
      p0031 p0031
  have p0034 :=
    @gSseq12i (synCfv (synC1st) (synCop R D)) R
      (synCxp (synCfv (synC2nd) (synCop R D)) (synCfv (synC2nd) (synCop R D)))
      (synCxp D D) p0030 p0033
  have p0035 :=
    @gBitri (.classMem (synCop R D) (synChwrels))
      (synWss (synCfv (synC1st) (synCop R D))
        (synCxp (synCfv (synC2nd) (synCop R D)) (synCfv (synC2nd) (synCop R D))))
      (synWss R (synCxp D D)) p0029 p0034
  have p0036 :=
    @gAnbi12i (.classMem (synCop R D) (synClntp))
      (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
        (synWbr R (synCconnex) D))
      (.classMem (synCop R D) (synChwrels)) (synWss R (synCxp D D)) p0018 p0035
  have p0037 :=
    @gBitri (.classMem (synCop R D) (synCin (synClntp) (synChwrels)))
      (synWa (.classMem (synCop R D) (synClntp)) (.classMem (synCop R D) (synChwrels)))
      (synWa (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
          (synWbr R (synCconnex) D)) (synWss R (synCxp D D)))
      p0003 p0036
  have p0038 := @gOpelxp R D (synCvv) (synCsn A)
  have p0039 :=
    @gBiantrur (.classMem R (synCvv)) (.classMem D (synCsn A)) hyp_ellntpcndv_2
  have p0040 :=
    @gBicomi (.classMem D (synCsn A))
      (synWa (.classMem R (synCvv)) (.classMem D (synCsn A))) p0039
  have p0041 := @gElsnc2 D A hyp_ellntpcndv_1
  have p0042 :=
    @gBitri (synWa (.classMem R (synCvv)) (.classMem D (synCsn A)))
      (.classMem D (synCsn A)) (.classEq D A) p0040 p0041
  have p0043 :=
    @gBitri (.classMem (synCop R D) (synCxp (synCvv) (synCsn A)))
      (synWa (.classMem R (synCvv)) (.classMem D (synCsn A))) (.classEq D A) p0038
      p0042
  have p0044 :=
    @gAnbi12i (.classMem (synCop R D) (synCin (synClntp) (synChwrels)))
      (synWa (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
          (synWbr R (synCconnex) D)) (synWss R (synCxp D D)))
      (.classMem (synCop R D) (synCxp (synCvv) (synCsn A))) (.classEq D A) p0037 p0043
  have p0045 :=
    @gBitri
      (.classMem (synCop R D)
        (synCin (synCin (synClntp) (synChwrels)) (synCxp (synCvv) (synCsn A))))
      (synWa (.classMem (synCop R D) (synCin (synClntp) (synChwrels)))
        (.classMem (synCop R D) (synCxp (synCvv) (synCsn A))))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
            (synWbr R (synCconnex) D)) (synWss R (synCxp D D))) (.classEq D A))
      p0002 p0044
  have p0046 :=
    @gBitri (.classMem (synCop R D) (synClntpc A))
      (.classMem (synCop R D)
        (synCin (synCin (synClntp) (synChwrels)) (synCxp (synCvv) (synCsn A))))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) D) (synWbr R (synCtrans) D))
            (synWbr R (synCconnex) D)) (synWss R (synCxp D D))) (.classEq D A))
      p0001 p0045
  exact p0046

/-- Checked nominal proof certificate identified upstream as `g_ellnpwcndv`. -/
@[expose]
noncomputable def gEllnpwcndv (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv)
    (hyp_ellnpwcndv_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_ellnpwcndv_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop R D) (synClnpwc A))
        (synWa (.classMem (synCop R D) (synClntpc A))
          (synWbr (synCdif R (synCcnv R)) (synCfound) D))) :=
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
  have dv_cache_0008 : r ∉ ((synWbr (synCdif R (synCcnv R)) (synCfound) D)).fv :=
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
  have dv_cache_0009 : d ∉ ((synWbr (synCdif R (synCcnv R)) (synCfound) D)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLnpwc A r d
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEleq2i (synClnpwc A)
      (synCin (synClntpc A) (synCopab r d
          (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
      (synCop R D) p0000
  have p0002 :=
    @gElin (synCop R D) (synClntpc A)
      (synCopab r d (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))
  have p0003 := @gId (.classEq (.cv r) R)
  have p0005 := @gCnveqd (.classEq (.cv r) R) (.cv r) R p0003
  have p0006 :=
    @gDifeq12d (.classEq (.cv r) R) (.cv r) R (synCcnv (.cv r)) (synCcnv R) p0003 p0005
  have p0007 :=
    @gBreq1d (.classEq (.cv r) R) (synCdif (.cv r) (synCcnv (.cv r)))
      (synCdif R (synCcnv R)) (.cv d) (synCfound) p0006
  have p0008 := @gBreq2 (.cv d) D (synCdif R (synCcnv R)) (synCfound)
  have p0009 :=
    @gOpelopabg (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))
      (synWbr (synCdif R (synCcnv R)) (synCfound) (.cv d))
      (synWbr (synCdif R (synCcnv R)) (synCfound) D) r d R D (synCvv) (synCvv)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0007 p0008
  have p0010 :=
    @gMp2an (.classMem R (synCvv)) (.classMem D (synCvv))
      (synWb (.classMem (synCop R D) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
        (synWbr (synCdif R (synCcnv R)) (synCfound) D))
      hyp_ellnpwcndv_1 hyp_ellnpwcndv_2 p0009
  have p0011 :=
    @gAnbi2i
      (.classMem (synCop R D) (synCopab r d
          (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d))))
      (synWbr (synCdif R (synCcnv R)) (synCfound) D)
      (.classMem (synCop R D) (synClntpc A)) p0010
  have p0012 :=
    @gN3bitri (.classMem (synCop R D) (synClnpwc A))
      (.classMem (synCop R D) (synCin (synClntpc A) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))))
      (synWa (.classMem (synCop R D) (synClntpc A)) (.classMem (synCop R D) (synCopab r d
            (synWbr (synCdif (.cv r) (synCcnv (.cv r))) (synCfound) (.cv d)))))
      (synWa (.classMem (synCop R D) (synClntpc A))
        (synWbr (synCdif R (synCcnv R)) (synCfound) D))
      p0001 p0002 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lnpwkerfnfn`. -/
@[expose]
noncomputable def gLnpwkerfnfn : Nominal.NPrf (synWfn (synClnpwkerfn) (synCvv)) :=
  by
  have p0000 := @gFnlndifop
  have p0001 := @gLn1stfn
  have p0002 := @gLnpwasymfnfn
  have p0003 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClnpwasymfn) (synCvv)) p0001
      p0002
  have p0004 := @gFntxp (synCvv) (synCvv) (synC1st) (synClnpwasymfn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gInidm (synCvv)
  have p0007 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synClnpwasymfn)) p0006
  have p0008 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synClnpwasymfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClnpwasymfn)) (synCvv)) p0005 p0007
  have p0009 :=
    @gFncovv (synClndifop) (synCtxp (synC1st) (synClnpwasymfn)) p0000 p0008
  have p0010 := (Nominal.classEqRefl (synClnpwkerfn))
  have p0011 :=
    @gFneq1i (synCvv) (synClnpwkerfn)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClnpwasymfn))) p0010
  have p0012 :=
    @gMpbir (synWfn (synClnpwkerfn) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synC1st) (synClnpwasymfn))) (synCvv))
      p0009 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lnpwkerfnex`. -/
@[expose]
noncomputable def gLnpwkerfnex : Nominal.NPrf (.classMem (synClnpwkerfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwkerfn))
  have p0001 := @gLndifopex
  have p0002 := @gN1stex
  have p0003 := @gLnpwasymfnex
  have p0004 := @gTxpex (synC1st) (synClnpwasymfn) p0002 p0003
  have p0005 := @gCoex (synClndifop) (synCtxp (synC1st) (synClnpwasymfn)) p0001 p0004
  have p0006 :=
    @gEqeltri (synClnpwkerfn)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClnpwasymfn))) (synCvv) p0000
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lnpwkerfnval`. -/
@[expose]
noncomputable def gLnpwkerfnval (D : Class) (R : Class)
    (hyp_lnpwkerfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwkerfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synClnpwkerfn) (synCop R D)) (synClnker R)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwkerfn))
  have p0001 :=
    @gFveq1i (synCop R D) (synClnpwkerfn)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClnpwasymfn))) p0000
  have p0002 := @gLn1stfn
  have p0003 := @gLnpwasymfnfn
  have p0004 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClnpwasymfn) (synCvv)) p0002
      p0003
  have p0005 := @gFntxp (synCvv) (synCvv) (synC1st) (synClnpwasymfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gInidm (synCvv)
  have p0008 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synClnpwasymfn)) p0007
  have p0009 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synClnpwasymfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClnpwasymfn)) (synCvv)) p0006 p0008
  have p0010 := @gOpex R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0011 :=
    @gPm32i (synWfn (synCtxp (synC1st) (synClnpwasymfn)) (synCvv))
      (.classMem (synCop R D) (synCvv)) p0009 p0010
  have p0012 :=
    @gFvco2 (synCvv) (synCop R D) (synClndifop)
      (synCtxp (synC1st) (synClnpwasymfn))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gEqtri (synCfv (synClnpwkerfn) (synCop R D))
      (synCfv (synCcom (synClndifop) (synCtxp (synC1st) (synClnpwasymfn))) (synCop R D))
      (synCfv (synClndifop) (synCfv (synCtxp (synC1st) (synClnpwasymfn)) (synCop R D)))
      p0001 p0013
  have p0018 := @gFvtxpvv (synCop R D) (synC1st) (synClnpwasymfn) p0002 p0003 p0010
  have p0019 := @gOpfv1st R D hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0020 := @gLnpwasymfnval D R hyp_lnpwkerfnval_1 hyp_lnpwkerfnval_2
  have p0021 :=
    @gOpeq12i (synCfv (synC1st) (synCop R D)) R
      (synCfv (synClnpwasymfn) (synCop R D)) (synCdif R (synCcnv R)) p0019 p0020
  have p0022 :=
    @gEqtri (synCfv (synCtxp (synC1st) (synClnpwasymfn)) (synCop R D))
      (synCop (synCfv (synC1st) (synCop R D)) (synCfv (synClnpwasymfn) (synCop R D)))
      (synCop R (synCdif R (synCcnv R))) p0018 p0021
  have p0023 :=
    @gFveq2i (synCfv (synCtxp (synC1st) (synClnpwasymfn)) (synCop R D))
      (synCop R (synCdif R (synCcnv R))) (synClndifop) p0022
  have p0024 :=
    @gEqtri (synCfv (synClnpwkerfn) (synCop R D))
      (synCfv (synClndifop) (synCfv (synCtxp (synC1st) (synClnpwasymfn)) (synCop R D)))
      (synCfv (synClndifop) (synCop R (synCdif R (synCcnv R)))) p0014 p0023
  have p0025 := (Nominal.classEqRefl (synCo R (synClndifop) (synCdif R (synCcnv R))))
  have p0026 :=
    @gEqcomi (synCo R (synClndifop) (synCdif R (synCcnv R)))
      (synCfv (synClndifop) (synCop R (synCdif R (synCcnv R)))) p0025
  have p0027 := @gCnvex R hyp_lnpwkerfnval_1
  have p0028 := @gDifex R (synCcnv R) hyp_lnpwkerfnval_1 p0027
  have p0029 :=
    @gPm32i (.classMem R (synCvv)) (.classMem (synCdif R (synCcnv R)) (synCvv))
      hyp_lnpwkerfnval_1 p0028
  have p0030 := @gLndifopvalg R (synCdif R (synCcnv R)) (synCvv) (synCvv)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @gEqtri (synCfv (synClndifop) (synCop R (synCdif R (synCcnv R))))
      (synCo R (synClndifop) (synCdif R (synCcnv R)))
      (synCdif R (synCdif R (synCcnv R))) p0026 p0031
  have p0033 :=
    @gEqtri (synCfv (synClnpwkerfn) (synCop R D))
      (synCfv (synClndifop) (synCop R (synCdif R (synCcnv R))))
      (synCdif R (synCdif R (synCcnv R))) p0024 p0032
  have p0034 := (Nominal.classEqRefl (synClnker R))
  have p0035 := @gDfin4 R (synCcnv R)
  have p0036 :=
    @gEqtri (synClnker R) (synCin R (synCcnv R))
      (synCdif R (synCdif R (synCcnv R))) p0034 p0035
  have p0037 := @gEqcomi (synClnker R) (synCdif R (synCdif R (synCcnv R))) p0036
  have p0038 :=
    @gEqtri (synCfv (synClnpwkerfn) (synCop R D))
      (synCdif R (synCdif R (synCcnv R))) (synClnker R) p0033 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_lninteropfn`. -/
@[expose]
noncomputable def gLninteropfn : Nominal.NPrf (synWfn (synClninterop) (synCvv)) :=
  by
  have p0000 := @gFnlndifop
  have p0001 := @gLn1stfn
  have p0003 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClndifop) (synCvv)) p0001
      p0000
  have p0004 := @gFntxp (synCvv) (synCvv) (synC1st) (synClndifop)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gInidm (synCvv)
  have p0007 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synClndifop))
      p0006
  have p0008 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synClndifop)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClndifop)) (synCvv)) p0005 p0007
  have p0009 := @gFncovv (synClndifop) (synCtxp (synC1st) (synClndifop)) p0000 p0008
  have p0010 := (Nominal.classEqRefl (synClninterop))
  have p0011 :=
    @gFneq1i (synCvv) (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) p0010
  have p0012 :=
    @gMpbir (synWfn (synClninterop) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv))
      p0009 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lninteropex`. -/
@[expose]
noncomputable def gLninteropex : Nominal.NPrf (.classMem (synClninterop) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClninterop))
  have p0001 := @gLndifopex
  have p0002 := @gN1stex
  have p0004 := @gTxpex (synC1st) (synClndifop) p0002 p0001
  have p0005 := @gCoex (synClndifop) (synCtxp (synC1st) (synClndifop)) p0001 p0004
  have p0006 :=
    @gEqeltri (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lninteropval`. -/
@[expose]
noncomputable def gLninteropval (A : Class) (B : Class)
    (hyp_lninteropval_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_lninteropval_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synClninterop) (synCop A B)) (synCin A B)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClninterop))
  have p0001 :=
    @gFveq1i (synCop A B) (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) p0000
  have p0002 := @gLn1stfn
  have p0003 := @gFnlndifop
  have p0004 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClndifop) (synCvv)) p0002
      p0003
  have p0005 := @gFntxp (synCvv) (synCvv) (synC1st) (synClndifop)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gInidm (synCvv)
  have p0008 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synClndifop))
      p0007
  have p0009 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synClndifop)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClndifop)) (synCvv)) p0006 p0008
  have p0010 := @gOpex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0011 :=
    @gPm32i (synWfn (synCtxp (synC1st) (synClndifop)) (synCvv))
      (.classMem (synCop A B) (synCvv)) p0009 p0010
  have p0012 :=
    @gFvco2 (synCvv) (synCop A B) (synClndifop) (synCtxp (synC1st) (synClndifop))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gEqtri (synCfv (synClninterop) (synCop A B))
      (synCfv (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCop A B))
      (synCfv (synClndifop) (synCfv (synCtxp (synC1st) (synClndifop)) (synCop A B)))
      p0001 p0013
  have p0018 := @gFvtxpvv (synCop A B) (synC1st) (synClndifop) p0002 p0003 p0010
  have p0019 := @gOpfv1st A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0020 := (Nominal.classEqRefl (synCo A (synClndifop) B))
  have p0021 :=
    @gEqcomi (synCo A (synClndifop) B) (synCfv (synClndifop) (synCop A B)) p0020
  have p0022 :=
    @gPm32i (.classMem A (synCvv)) (.classMem B (synCvv)) hyp_lninteropval_1
      hyp_lninteropval_2
  have p0023 := @gLndifopvalg A B (synCvv) (synCvv)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gEqtri (synCfv (synClndifop) (synCop A B)) (synCo A (synClndifop) B)
      (synCdif A B) p0021 p0024
  have p0026 :=
    @gOpeq12i (synCfv (synC1st) (synCop A B)) A (synCfv (synClndifop) (synCop A B))
      (synCdif A B) p0019 p0025
  have p0027 :=
    @gEqtri (synCfv (synCtxp (synC1st) (synClndifop)) (synCop A B))
      (synCop (synCfv (synC1st) (synCop A B)) (synCfv (synClndifop) (synCop A B)))
      (synCop A (synCdif A B)) p0018 p0026
  have p0028 :=
    @gFveq2i (synCfv (synCtxp (synC1st) (synClndifop)) (synCop A B))
      (synCop A (synCdif A B)) (synClndifop) p0027
  have p0029 :=
    @gEqtri (synCfv (synClninterop) (synCop A B))
      (synCfv (synClndifop) (synCfv (synCtxp (synC1st) (synClndifop)) (synCop A B)))
      (synCfv (synClndifop) (synCop A (synCdif A B))) p0014 p0028
  have p0030 := (Nominal.classEqRefl (synCo A (synClndifop) (synCdif A B)))
  have p0031 :=
    @gEqcomi (synCo A (synClndifop) (synCdif A B))
      (synCfv (synClndifop) (synCop A (synCdif A B))) p0030
  have p0032 := @gDifex A B hyp_lninteropval_1 hyp_lninteropval_2
  have p0033 :=
    @gPm32i (.classMem A (synCvv)) (.classMem (synCdif A B) (synCvv))
      hyp_lninteropval_1 p0032
  have p0034 := @gLndifopvalg A (synCdif A B) (synCvv) (synCvv)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @gEqtri (synCfv (synClndifop) (synCop A (synCdif A B)))
      (synCo A (synClndifop) (synCdif A B)) (synCdif A (synCdif A B)) p0031 p0035
  have p0037 :=
    @gEqtri (synCfv (synClninterop) (synCop A B))
      (synCfv (synClndifop) (synCop A (synCdif A B))) (synCdif A (synCdif A B))
      p0029 p0036
  have p0038 := @gDfin4 A B
  have p0039 := @gEqcomi (synCin A B) (synCdif A (synCdif A B)) p0038
  have p0040 :=
    @gEqtri (synCfv (synClninterop) (synCop A B)) (synCdif A (synCdif A B))
      (synCin A B) p0037 p0039
  exact p0040

/-- Checked nominal proof certificate identified upstream as `g_lnimagecrossfnval`. -/
@[expose]
noncomputable def gLnimagecrossfnval (B : Class) (R : Class)
    (hyp_lnimagecrossfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnimagecrossfnval_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnimagecrossfn) (synCop R B)) (synCxp B (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0001 :=
    @gFveq1i (synCop R B) (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      p0000
  have p0002 := @gLn2ndfn
  have p0003 := @gVvex
  have p0004 := @gFnconstg (synCvv) (synCvv) (synCvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCvv))) (synCvv)) p0002 p0005
  have p0007 :=
    @gFntxp (synCvv) (synCvv) (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gInidm (synCvv)
  have p0010 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) p0009
  have p0011 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCvv))
      p0008 p0010
  have p0012 := @gOpex R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0013 :=
    @gPm32i
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCvv))
      (.classMem (synCop R B) (synCvv)) p0011 p0012
  have p0014 :=
    @gFvco2 (synCvv) (synCop R B) (synCcross)
      (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gEqtri (synCfv (synClnimagecrossfn) (synCop R B))
      (synCfv (synCcom (synCcross)
          (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))) (synCop R B))
      (synCfv (synCcross)
        (synCfv (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCop R B)))
      p0001 p0015
  have p0022 :=
    @gFvtxpvv (synCop R B) (synC2nd) (synCxp (synCvv) (synCsn (synCvv))) p0002
      p0005 p0012
  have p0023 := @gOpfv2nd R B hyp_lnimagecrossfnval_1 hyp_lnimagecrossfnval_2
  have p0026 := @gFvconst2 (synCvv) (synCvv) (synCop R B) p0003
  have p0027 := Nominal.mp p0012 p0026
  have p0028 :=
    @gOpeq12i (synCfv (synC2nd) (synCop R B)) B
      (synCfv (synCxp (synCvv) (synCsn (synCvv))) (synCop R B)) (synCvv) p0023
      p0027
  have p0029 :=
    @gEqtri
      (synCfv (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCop R B))
      (synCop (synCfv (synC2nd) (synCop R B))
        (synCfv (synCxp (synCvv) (synCsn (synCvv))) (synCop R B)))
      (synCop B (synCvv)) p0022 p0028
  have p0030 :=
    @gFveq2i
      (synCfv (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCop R B))
      (synCop B (synCvv)) (synCcross) p0029
  have p0031 :=
    @gEqtri (synCfv (synClnimagecrossfn) (synCop R B))
      (synCfv (synCcross)
        (synCfv (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCop R B)))
      (synCfv (synCcross) (synCop B (synCvv))) p0016 p0030
  have p0032 := (Nominal.classEqRefl (synCo B (synCcross) (synCvv)))
  have p0033 :=
    @gEqcomi (synCo B (synCcross) (synCvv))
      (synCfv (synCcross) (synCop B (synCvv))) p0032
  have p0035 :=
    @gPm32i (.classMem B (synCvv)) (.classMem (synCvv) (synCvv))
      hyp_lnimagecrossfnval_2 p0003
  have p0036 := @gOvcross B (synCvv) (synCvv) (synCvv)
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @gEqtri (synCfv (synCcross) (synCop B (synCvv)))
      (synCo B (synCcross) (synCvv)) (synCxp B (synCvv)) p0033 p0037
  have p0039 :=
    @gEqtri (synCfv (synClnimagecrossfn) (synCop R B))
      (synCfv (synCcross) (synCop B (synCvv))) (synCxp B (synCvv)) p0031 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_lnimageresfnfn`. -/
@[expose]
noncomputable def gLnimageresfnfn :
    Nominal.NPrf (synWfn (synClnimageresfn) (synCvv)) :=
  by
  have p0000 := @gFnlndifop
  have p0001 := @gLn1stfn
  have p0003 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClndifop) (synCvv)) p0001
      p0000
  have p0004 := @gFntxp (synCvv) (synCvv) (synC1st) (synClndifop)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gInidm (synCvv)
  have p0007 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synClndifop))
      p0006
  have p0008 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synClndifop)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClndifop)) (synCvv)) p0005 p0007
  have p0009 := @gFncovv (synClndifop) (synCtxp (synC1st) (synClndifop)) p0000 p0008
  have p0010 := (Nominal.classEqRefl (synClninterop))
  have p0011 :=
    @gFneq1i (synCvv) (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) p0010
  have p0012 :=
    @gMpbir (synWfn (synClninterop) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv))
      p0009 p0011
  have p0014 := @gFncross
  have p0015 := @gLn2ndfn
  have p0016 := @gVvex
  have p0017 := @gFnconstg (synCvv) (synCvv) (synCvv)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCvv))) (synCvv)) p0015 p0018
  have p0020 :=
    @gFntxp (synCvv) (synCvv) (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))
  have p0021 := Nominal.mp p0019 p0020
  have p0023 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) p0006
  have p0024 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCvv))
      p0021 p0023
  have p0025 :=
    @gFncovv (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
      p0014 p0024
  have p0026 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0027 :=
    @gFneq1i (synCvv) (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      p0026
  have p0028 :=
    @gMpbir (synWfn (synClnimagecrossfn) (synCvv))
      (synWfn (synCcom (synCcross)
          (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))) (synCvv))
      p0025 p0027
  have p0029 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClnimagecrossfn) (synCvv))
      p0001 p0028
  have p0030 := @gFntxp (synCvv) (synCvv) (synC1st) (synClnimagecrossfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0033 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synClnimagecrossfn)) p0006
  have p0034 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCvv)) p0031 p0033
  have p0035 :=
    @gFncovv (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)) p0012 p0034
  have p0036 := (Nominal.classEqRefl (synClnimageresfn))
  have p0037 :=
    @gFneq1i (synCvv) (synClnimageresfn)
      (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn))) p0036
  have p0038 :=
    @gMpbir (synWfn (synClnimageresfn) (synCvv))
      (synWfn (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)))
        (synCvv))
      p0035 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_lnimageresfnex`. -/
@[expose]
noncomputable def gLnimageresfnex :
    Nominal.NPrf (.classMem (synClnimageresfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnimageresfn))
  have p0001 := (Nominal.classEqRefl (synClninterop))
  have p0002 := @gLndifopex
  have p0003 := @gN1stex
  have p0005 := @gTxpex (synC1st) (synClndifop) p0003 p0002
  have p0006 := @gCoex (synClndifop) (synCtxp (synC1st) (synClndifop)) p0002 p0005
  have p0007 :=
    @gEqeltri (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv) p0001 p0006
  have p0009 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0010 := @gCrossex
  have p0011 := @gN2ndex
  have p0012 := @gVvex
  have p0013 := @gSnex (synCvv)
  have p0014 := @gXpex (synCvv) (synCsn (synCvv)) p0012 p0013
  have p0015 := @gTxpex (synC2nd) (synCxp (synCvv) (synCsn (synCvv))) p0011 p0014
  have p0016 :=
    @gCoex (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
      p0010 p0015
  have p0017 :=
    @gEqeltri (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      (synCvv) p0009 p0016
  have p0018 := @gTxpex (synC1st) (synClnimagecrossfn) p0003 p0017
  have p0019 :=
    @gCoex (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)) p0007 p0018
  have p0020 :=
    @gEqeltri (synClnimageresfn)
      (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn))) (synCvv)
      p0000 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_lnimageresfnval`. -/
@[expose]
noncomputable def gLnimageresfnval (B : Class) (R : Class)
    (hyp_lnimageresfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnimageresfnval_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synClnimageresfn) (synCop R B)) (synCres R B)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnimageresfn))
  have p0001 :=
    @gFveq1i (synCop R B) (synClnimageresfn)
      (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn))) p0000
  have p0002 := @gLn1stfn
  have p0003 := @gFncross
  have p0004 := @gLn2ndfn
  have p0005 := @gVvex
  have p0006 := @gFnconstg (synCvv) (synCvv) (synCvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCvv))) (synCvv)) p0004 p0007
  have p0009 :=
    @gFntxp (synCvv) (synCvv) (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gInidm (synCvv)
  have p0012 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) p0011
  have p0013 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCvv))
      p0010 p0012
  have p0014 :=
    @gFncovv (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
      p0003 p0013
  have p0015 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0016 :=
    @gFneq1i (synCvv) (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      p0015
  have p0017 :=
    @gMpbir (synWfn (synClnimagecrossfn) (synCvv))
      (synWfn (synCcom (synCcross)
          (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))) (synCvv))
      p0014 p0016
  have p0018 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClnimagecrossfn) (synCvv))
      p0002 p0017
  have p0019 := @gFntxp (synCvv) (synCvv) (synC1st) (synClnimagecrossfn)
  have p0020 := Nominal.mp p0018 p0019
  have p0022 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synClnimagecrossfn)) p0011
  have p0023 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCvv)) p0020 p0022
  have p0024 := @gOpex R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0025 :=
    @gPm32i (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCvv))
      (.classMem (synCop R B) (synCvv)) p0023 p0024
  have p0026 :=
    @gFvco2 (synCvv) (synCop R B) (synClninterop)
      (synCtxp (synC1st) (synClnimagecrossfn))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @gEqtri (synCfv (synClnimageresfn) (synCop R B))
      (synCfv (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)))
        (synCop R B))
      (synCfv (synClninterop)
        (synCfv (synCtxp (synC1st) (synClnimagecrossfn)) (synCop R B)))
      p0001 p0027
  have p0046 :=
    @gFvtxpvv (synCop R B) (synC1st) (synClnimagecrossfn) p0002 p0017 p0024
  have p0047 := @gOpfv1st R B hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0048 := @gLnimagecrossfnval B R hyp_lnimageresfnval_1 hyp_lnimageresfnval_2
  have p0049 :=
    @gOpeq12i (synCfv (synC1st) (synCop R B)) R
      (synCfv (synClnimagecrossfn) (synCop R B)) (synCxp B (synCvv)) p0047 p0048
  have p0050 :=
    @gEqtri (synCfv (synCtxp (synC1st) (synClnimagecrossfn)) (synCop R B))
      (synCop (synCfv (synC1st) (synCop R B)) (synCfv (synClnimagecrossfn) (synCop R B)))
      (synCop R (synCxp B (synCvv))) p0046 p0049
  have p0051 :=
    @gFveq2i (synCfv (synCtxp (synC1st) (synClnimagecrossfn)) (synCop R B))
      (synCop R (synCxp B (synCvv))) (synClninterop) p0050
  have p0052 :=
    @gEqtri (synCfv (synClnimageresfn) (synCop R B))
      (synCfv (synClninterop)
        (synCfv (synCtxp (synC1st) (synClnimagecrossfn)) (synCop R B)))
      (synCfv (synClninterop) (synCop R (synCxp B (synCvv)))) p0028 p0051
  have p0054 := @gXpex B (synCvv) hyp_lnimageresfnval_2 p0005
  have p0055 := @gLninteropval R (synCxp B (synCvv)) hyp_lnimageresfnval_1 p0054
  have p0056 :=
    @gEqtri (synCfv (synClnimageresfn) (synCop R B))
      (synCfv (synClninterop) (synCop R (synCxp B (synCvv))))
      (synCin R (synCxp B (synCvv))) p0052 p0055
  have p0057 := (Nominal.classEqRefl (synCres R B))
  have p0058 := @gEqcomi (synCres R B) (synCin R (synCxp B (synCvv))) p0057
  have p0059 :=
    @gEqtri (synCfv (synClnimageresfn) (synCop R B)) (synCin R (synCxp B (synCvv)))
      (synCres R B) p0056 p0058
  exact p0059

/-- Checked nominal proof certificate identified upstream as `g_lnimageopfn`. -/
@[expose]
noncomputable def gLnimageopfn : Nominal.NPrf (synWfn (synClnimageop) (synCvv)) :=
  by
  have p0000 := @gRanfnfn
  have p0001 := @gFnlndifop
  have p0002 := @gLn1stfn
  have p0004 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClndifop) (synCvv)) p0002
      p0001
  have p0005 := @gFntxp (synCvv) (synCvv) (synC1st) (synClndifop)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gInidm (synCvv)
  have p0008 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synClndifop))
      p0007
  have p0009 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synClndifop)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClndifop)) (synCvv)) p0006 p0008
  have p0010 := @gFncovv (synClndifop) (synCtxp (synC1st) (synClndifop)) p0001 p0009
  have p0011 := (Nominal.classEqRefl (synClninterop))
  have p0012 :=
    @gFneq1i (synCvv) (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) p0011
  have p0013 :=
    @gMpbir (synWfn (synClninterop) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv))
      p0010 p0012
  have p0015 := @gFncross
  have p0016 := @gLn2ndfn
  have p0017 := @gVvex
  have p0018 := @gFnconstg (synCvv) (synCvv) (synCvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCvv))) (synCvv)) p0016 p0019
  have p0021 :=
    @gFntxp (synCvv) (synCvv) (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))
  have p0022 := Nominal.mp p0020 p0021
  have p0024 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) p0007
  have p0025 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCvv))
      p0022 p0024
  have p0026 :=
    @gFncovv (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
      p0015 p0025
  have p0027 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0028 :=
    @gFneq1i (synCvv) (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      p0027
  have p0029 :=
    @gMpbir (synWfn (synClnimagecrossfn) (synCvv))
      (synWfn (synCcom (synCcross)
          (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))) (synCvv))
      p0026 p0028
  have p0030 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClnimagecrossfn) (synCvv))
      p0002 p0029
  have p0031 := @gFntxp (synCvv) (synCvv) (synC1st) (synClnimagecrossfn)
  have p0032 := Nominal.mp p0030 p0031
  have p0034 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synClnimagecrossfn)) p0007
  have p0035 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCvv)) p0032 p0034
  have p0036 :=
    @gFncovv (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)) p0013 p0035
  have p0037 := (Nominal.classEqRefl (synClnimageresfn))
  have p0038 :=
    @gFneq1i (synCvv) (synClnimageresfn)
      (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn))) p0037
  have p0039 :=
    @gMpbir (synWfn (synClnimageresfn) (synCvv))
      (synWfn (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)))
        (synCvv))
      p0036 p0038
  have p0040 := @gFncovv (synCranfn) (synClnimageresfn) p0000 p0039
  have p0041 := (Nominal.classEqRefl (synClnimageop))
  have p0042 :=
    @gFneq1i (synCvv) (synClnimageop) (synCcom (synCranfn) (synClnimageresfn)) p0041
  have p0043 :=
    @gMpbir (synWfn (synClnimageop) (synCvv))
      (synWfn (synCcom (synCranfn) (synClnimageresfn)) (synCvv)) p0040 p0042
  exact p0043

/-- Checked nominal proof certificate identified upstream as `g_lnimageopex`. -/
@[expose]
noncomputable def gLnimageopex : Nominal.NPrf (.classMem (synClnimageop) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnimageop))
  have p0001 := @gRanfnex
  have p0002 := (Nominal.classEqRefl (synClnimageresfn))
  have p0003 := (Nominal.classEqRefl (synClninterop))
  have p0004 := @gLndifopex
  have p0005 := @gN1stex
  have p0007 := @gTxpex (synC1st) (synClndifop) p0005 p0004
  have p0008 := @gCoex (synClndifop) (synCtxp (synC1st) (synClndifop)) p0004 p0007
  have p0009 :=
    @gEqeltri (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv) p0003 p0008
  have p0011 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0012 := @gCrossex
  have p0013 := @gN2ndex
  have p0014 := @gVvex
  have p0015 := @gSnex (synCvv)
  have p0016 := @gXpex (synCvv) (synCsn (synCvv)) p0014 p0015
  have p0017 := @gTxpex (synC2nd) (synCxp (synCvv) (synCsn (synCvv))) p0013 p0016
  have p0018 :=
    @gCoex (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
      p0012 p0017
  have p0019 :=
    @gEqeltri (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      (synCvv) p0011 p0018
  have p0020 := @gTxpex (synC1st) (synClnimagecrossfn) p0005 p0019
  have p0021 :=
    @gCoex (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)) p0009 p0020
  have p0022 :=
    @gEqeltri (synClnimageresfn)
      (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn))) (synCvv)
      p0002 p0021
  have p0023 := @gCoex (synCranfn) (synClnimageresfn) p0001 p0022
  have p0024 :=
    @gEqeltri (synClnimageop) (synCcom (synCranfn) (synClnimageresfn)) (synCvv)
      p0000 p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end
