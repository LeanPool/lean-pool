/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6tchomdmndv (x : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
        (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have dv_cache_0001 : x ≠ z := by exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0002 :
    z ∉
      ((Wff.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_wppconcrete6dmrepdndv x z dv_cache_0001
  have p0001 :=
    @g_id
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0002 :=
    @g_fveq2 (.cv x)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (syn_cwppconcrete6fn)
  have p0003 :=
    @g_syl
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0001 p0002
  have p0004 :=
    @g_tceq (syn_cfv (syn_cwppconcrete6fn) (.cv x))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0005 :=
    @g_syl
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_ctc
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))))
      p0003 p0004
  have p0006 := @g_vex z
  have p0007 := @g_wppconcrete6canonicaltchomndv (.cv z) p0006
  have p0008 :=
    @g_a1i
      (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0007
  have p0010 :=
    @g_tceq (.cv x)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
  have p0011 :=
    @g_syl
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (syn_ctc (.cv x)) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0001 p0010
  have p0012 :=
    @g_fveq2 (syn_ctc (.cv x))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_cwppconcrete6fn)
  have p0013 :=
    @g_syl
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (syn_ctc (.cv x)) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))) (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))))
      p0011 p0012
  have p0014 :=
    @g_eqcomd
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x)))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0013
  have p0015 :=
    @g_n_3eqtrd
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
      (syn_ctc (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))) p0005 p0008 p0014
  have p0016 :=
    @g_exlimiv
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))
      z dv_cache_0002 p0015
  have p0017 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (syn_wex z (.classEq (.cv x)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))
      p0000 p0016
  exact p0017

@[expose]
noncomputable def g_wppstopstepexndv (C : Class) (F : Class)
    (hyp_wppstopstepexndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) :
    Nominal.NPrf (.classMem (syn_cwppstopstep F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0001 := @g_elex F (syn_cfuns)
  have p0002 := Nominal.mp hyp_wppstopstepexndv_1 p0001
  have p0003 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0006 := @g_dmex F p0002
  have p0007 := @g_vvex
  have p0008 := @g_hwcardsexg (syn_cvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_lecex
  have p0011 := @g_cnvex (syn_clec) p0010
  have p0012 := @g_snex C
  have p0013 := @g_imaex (syn_ccnv (syn_clec)) (syn_csn C) p0011 p0012
  have p0014 :=
    @g_inex (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) p0009
      p0013
  have p0015 :=
    @g_inex (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      p0006 p0014
  have p0016 :=
    @g_eqeltri (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cvv) p0003 p0015
  have p0017 := @g_resex F (syn_cwppstopact F C) p0002 p0016
  have p0018 := @g_idex
  have p0036 := @g_difex (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) p0009 p0016
  have p0037 :=
    @g_resex (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) p0018
      p0036
  have p0038 :=
    @g_unex (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) p0017
      p0037
  have p0039 :=
    @g_eqeltri (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      (syn_cvv) p0000 p0038
  exact p0039

@[expose]
noncomputable def g_wppstopstepmapndv (C : Class) (F : Class)
    (hyp_wppstopstepmapndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepmapndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) :=
  by
  have p0000 := @g_elfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepmapndv_1 p0000
  have p0002 := @g_funfn F
  have p0003 := @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 := @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F))
      (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepmapndv_2
  have p0007 := @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_cdm F))
      p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 := @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_chwcards (syn_cvv)))
      p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i
      (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))
      p0015 p0022
  have p0024 := @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i
      (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C)
          (syn_chwcards (syn_cvv))) (syn_wf
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))))
      (.classEq (syn_cin (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0))
      p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0029 :=
    @g_feq1i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0028
  have p0030 :=
    @g_mpbir
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_chwcards (syn_cvv)) p0031 p0032
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_chwcards (syn_cvv)) p0010
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_chwcards (syn_cvv)))
      p0033 p0035
  have p0037 := @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (.classEq (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)))
      p0036 p0037
  have p0039 :=
    @g_feq2i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0030 p0039
  have p0041 := @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      p0040 p0043
  exact p0044

@[expose]
noncomputable def g_wppstopstepfunsndv (C : Class) (F : Class)
    (hyp_wppstopstepfunsndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepfunsndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppstopstep F C) (syn_cfuns)) :=
  by
  have p0000 := @g_elfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepfunsndv_1 p0000
  have p0002 := @g_funfn F
  have p0003 := @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 := @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F))
      (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepfunsndv_2
  have p0007 := @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_cdm F))
      p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 := @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_chwcards (syn_cvv)))
      p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i
      (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))
      p0015 p0022
  have p0024 := @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i
      (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C)
          (syn_chwcards (syn_cvv))) (syn_wf
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))))
      (.classEq (syn_cin (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0))
      p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0029 :=
    @g_feq1i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0028
  have p0030 :=
    @g_mpbir
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_chwcards (syn_cvv)) p0031 p0032
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_chwcards (syn_cvv)) p0010
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_chwcards (syn_cvv)))
      p0033 p0035
  have p0037 := @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (.classEq (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)))
      p0036 p0037
  have p0039 :=
    @g_feq2i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0030 p0039
  have p0041 := @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      p0040 p0043
  have p0045 :=
    @g_ffun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0046 := Nominal.mp p0044 p0045
  have p0047 := @g_wppstopstepexndv C F hyp_wppstopstepfunsndv_1
  have p0048 := @g_elfuns (syn_cwppstopstep F C) p0047
  have p0049 :=
    @g_mpbir (.classMem (syn_cwppstopstep F C) (syn_cfuns))
      (syn_wfun (syn_cwppstopstep F C)) p0046 p0048
  exact p0049

@[expose]
noncomputable def g_wppstopstepdmndv (C : Class) (F : Class)
    (hyp_wppstopstepdmndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepdmndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv))) :=
  by
  have p0000 := @g_elfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepdmndv_1 p0000
  have p0002 := @g_funfn F
  have p0003 := @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 := @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F))
      (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepdmndv_2
  have p0007 := @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_cdm F))
      p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 := @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_chwcards (syn_cvv)))
      p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i
      (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))
      p0015 p0022
  have p0024 := @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i
      (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C)
          (syn_chwcards (syn_cvv))) (syn_wf
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))))
      (.classEq (syn_cin (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0))
      p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0029 :=
    @g_feq1i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0028
  have p0030 :=
    @g_mpbir
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_chwcards (syn_cvv)) p0031 p0032
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_chwcards (syn_cvv)) p0010
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_chwcards (syn_cvv)))
      p0033 p0035
  have p0037 := @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (.classEq (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)))
      p0036 p0037
  have p0039 :=
    @g_feq2i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0030 p0039
  have p0041 := @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      p0040 p0043
  have p0045 :=
    @g_fdm (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0046 := Nominal.mp p0044 p0045
  exact p0046

@[expose]
noncomputable def g_wppstopsteprndmndv (C : Class) (F : Class)
    (hyp_wppstopstepdmndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepdmndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) :=
  by
  have p0000 := @g_elfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepdmndv_1 p0000
  have p0002 := @g_funfn F
  have p0003 := @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 := @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F))
      (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepdmndv_2
  have p0007 := @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_cdm F))
      p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 := @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
        (syn_chwcards (syn_cvv)))
      p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i
      (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))
      p0015 p0022
  have p0024 := @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i
      (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C)
          (syn_chwcards (syn_cvv))) (syn_wf
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))))
      (.classEq (syn_cin (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0))
      p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0029 :=
    @g_feq1i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0028
  have p0030 :=
    @g_mpbir
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_chwcards (syn_cvv)) p0031 p0032
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_chwcards (syn_cvv)) p0010
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_chwcards (syn_cvv)))
      p0033 p0035
  have p0037 := @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv)))
      (.classEq (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)))
      p0036 p0037
  have p0039 :=
    @g_feq2i
      (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C)
          (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      p0030 p0039
  have p0041 := @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv))
        (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))))
      (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))
      p0040 p0043
  have p0045 :=
    @g_frn (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0046 := Nominal.mp p0044 p0045
  have p0047 := @g_wppstopstepdmndv C F hyp_wppstopstepdmndv_1 hyp_wppstopstepdmndv_2
  have p0048 := @g_eqcomi (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) p0047
  have p0049 :=
    @g_sseq2i (syn_chwcards (syn_cvv)) (syn_cdm (syn_cwppstopstep F C))
      (syn_crn (syn_cwppstopstep F C)) p0048
  have p0050 :=
    @g_mpbi (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)))
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0046
      p0049
  exact p0050

@[expose]
noncomputable def g_wppstopstepfvactclndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvactclndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepfvactclndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cwppstopact F C))
        (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A))) :=
  by
  have p0000 :=
    @g_inss1 (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0001 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0002 :=
    @g_sseq1i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_cdm F) p0001
  have p0003 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F))
      (syn_wss (syn_cin (syn_cdm F)
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (syn_cdm F))
      p0000 p0002
  have p0004 := @g_sseli (syn_cwppstopact F C) (syn_cdm F) A p0003
  have p0005 := @g_elfunsi F
  have p0006 := Nominal.mp hyp_wppstopstepfvactclndv_1 p0005
  have p0007 := @g_funfvbrb A F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_biimpi (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)) p0008
  have p0010 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (.classMem A (syn_cdm F))
      (syn_wbr A F (syn_cfv F A)) p0004 p0009
  have p0011 := @g_id (.classMem A (syn_cwppstopact F C))
  have p0012 :=
    @g_jca (.classMem A (syn_cwppstopact F C)) (syn_wbr A F (syn_cfv F A))
      (.classMem A (syn_cwppstopact F C)) p0010 p0011
  have p0013 := @g_brres A (syn_cfv F A) F (syn_cwppstopact F C)
  have p0014 :=
    @g_biimpri (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A))
      (syn_wa (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cwppstopact F C))) p0013
  have p0015 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wa (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cwppstopact F C)))
      (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) p0012 p0014
  have p0016 :=
    @g_orc (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A))
      (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
        (syn_cfv F A))
  have p0017 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A))
      (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cfv F A)))
      p0015 p0016
  have p0018 :=
    @g_brun A (syn_cfv F A) (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0019 :=
    @g_biimpri
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cfv F A))
      (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cfv F A)))
      p0018
  have p0020 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
          (syn_cfv F A)))
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cfv F A))
      p0017 p0019
  have p0021 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0022 :=
    @g_breqi A (syn_cfv F A) (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0021
  have p0023 :=
    @g_biimpri (syn_wbr A (syn_cwppstopstep F C) (syn_cfv F A))
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cfv F A))
      p0022
  have p0024 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
        (syn_cfv F A))
      (syn_wbr A (syn_cwppstopstep F C) (syn_cfv F A)) p0020 p0023
  have p0025 :=
    @g_wppstopstepmapndv C F hyp_wppstopstepfvactclndv_1 hyp_wppstopstepfvactclndv_2
  have p0026 :=
    @g_ffun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @g_funbrfv A (syn_cfv F A) (syn_cwppstopstep F C)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wbr A (syn_cwppstopstep F C) (syn_cfv F A))
      (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A)) p0024 p0029
  exact p0030

@[expose]
noncomputable def g_wppstopstepfvidleclndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvidleclndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepfvidleclndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
          (.neg (.classMem A (syn_cwppstopact F C))))
        (.classEq (syn_cfv (syn_cwppstopstep F C) A) A)) :=
  by
  have p0000 := @g_eldif A (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0001 :=
    @g_biimpri (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      p0000
  have p0002 := @g_ididg A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0003 :=
    @g_syl
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
      (syn_wbr A (syn_cid) A) p0001 p0002
  have p0006 :=
    @g_jca
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (syn_wbr A (syn_cid) A)
      (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) p0003 p0001
  have p0007 :=
    @g_brres A A (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0008 :=
    @g_biimpri
      (syn_wbr A
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)
      (syn_wa (syn_wbr A (syn_cid) A)
        (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0007
  have p0009 :=
    @g_syl
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (syn_wa (syn_wbr A (syn_cid) A)
        (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      (syn_wbr A
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)
      p0006 p0008
  have p0010 :=
    @g_olc
      (syn_wbr A
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)
      (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A)
  have p0011 :=
    @g_syl
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (syn_wbr A
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)
      (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A) (syn_wbr A
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A))
      p0009 p0010
  have p0012 :=
    @g_brun A A (syn_cres F (syn_cwppstopact F C))
      (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0013 :=
    @g_biimpri
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A)
      (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A) (syn_wbr A
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A))
      p0012
  have p0014 :=
    @g_syl
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A) (syn_wbr A
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A))
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A)
      p0011 p0013
  have p0015 := (Nominal.classEqRefl (syn_cwppstopstep F C))
  have p0016 :=
    @g_breqi A A (syn_cwppstopstep F C)
      (syn_cun (syn_cres F (syn_cwppstopact F C))
        (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))))
      p0015
  have p0017 :=
    @g_biimpri (syn_wbr A (syn_cwppstopstep F C) A)
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A)
      p0016
  have p0018 :=
    @g_syl
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C))
          (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A)
      (syn_wbr A (syn_cwppstopstep F C) A) p0014 p0017
  have p0019 :=
    @g_wppstopstepmapndv C F hyp_wppstopstepfvidleclndv_1 hyp_wppstopstepfvidleclndv_2
  have p0020 :=
    @g_ffun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_funbrfv A A (syn_cwppstopstep F C)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 :=
    @g_syl
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (syn_wbr A (syn_cwppstopstep F C) A) (.classEq (syn_cfv (syn_cwppstopstep F C) A) A)
      p0018 p0023
  exact p0024

@[expose]
noncomputable def g_wppstopactlecbindv (A : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
        (syn_wb (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppstopact F C))
  have p0001 :=
    @g_eleq2i (syn_cwppstopact F C)
      (syn_cin (syn_cdm F)
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      A p0000
  have p0002 :=
    @g_elin A (syn_cdm F)
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0003 :=
    @g_elin A (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0004 := @g_elimasn (syn_ccnv (syn_clec)) C A
  have p0005 := (Nominal.biimpRefl (syn_wbr C (syn_ccnv (syn_clec)) A))
  have p0006 :=
    @g_bicomi (syn_wbr C (syn_ccnv (syn_clec)) A)
      (.classMem (syn_cop C A) (syn_ccnv (syn_clec))) p0005
  have p0007 :=
    @g_bitri (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (.classMem (syn_cop C A) (syn_ccnv (syn_clec))) (syn_wbr C (syn_ccnv (syn_clec)) A)
      p0004 p0006
  have p0008 := @g_brcnv C A (syn_clec)
  have p0009 :=
    @g_bitri (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_wbr C (syn_ccnv (syn_clec)) A) (syn_wbr A (syn_clec) C) p0007 p0008
  have p0010 :=
    @g_anbi2i (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_wbr A (syn_clec) C) (.classMem A (syn_chwcards (syn_cvv))) p0009
  have p0011 :=
    @g_bitri
      (.classMem A
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0003 p0010
  have p0012 :=
    @g_anbi2i
      (.classMem A
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))
      (.classMem A (syn_cdm F)) p0011
  have p0013 :=
    @g_bitri
      (.classMem A (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv))
            (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))))
      (syn_wa (.classMem A (syn_cdm F)) (.classMem A (syn_cin (syn_chwcards (syn_cvv))
            (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))))
      (syn_wa (.classMem A (syn_cdm F))
        (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)))
      p0002 p0012
  have p0014 :=
    @g_bitri (.classMem A (syn_cwppstopact F C))
      (.classMem A (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv))
            (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))))
      (syn_wa (.classMem A (syn_cdm F))
        (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)))
      p0001 p0013
  have p0015 :=
    @g_biimpi (.classMem A (syn_cwppstopact F C))
      (syn_wa (.classMem A (syn_cdm F))
        (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)))
      p0014
  have p0016 :=
    @g_simpr (.classMem A (syn_cdm F))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))
  have p0017 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wa (.classMem A (syn_cdm F))
        (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0015 p0016
  have p0018 := @g_simpr (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)
  have p0019 :=
    @g_syl (.classMem A (syn_cwppstopact F C))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))
      (syn_wbr A (syn_clec) C) p0017 p0018
  have p0020 :=
    @g_a1i (.imp (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      p0019
  have p0021 :=
    @g_simpr (.classMem A (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))
  have p0022 :=
    @g_simpl (.classMem A (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))
  have p0023 :=
    @g_a1d
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C) p0022
  have p0024 := @g_id (syn_wbr A (syn_clec) C)
  have p0025 :=
    @g_a1i (.imp (syn_wbr A (syn_clec) C) (syn_wbr A (syn_clec) C))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      p0024
  have p0026 :=
    @g_jcad
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (syn_wbr A (syn_clec) C) (.classMem A (syn_chwcards (syn_cvv)))
      (syn_wbr A (syn_clec) C) p0023 p0025
  have p0027 :=
    @g_jcad
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0021 p0026
  have p0043 :=
    @g_biimpri (.classMem A (syn_cwppstopact F C))
      (syn_wa (.classMem A (syn_cdm F))
        (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)))
      p0014
  have p0044 :=
    @g_syl6
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (syn_wbr A (syn_clec) C)
      (syn_wa (.classMem A (syn_cdm F))
        (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)))
      (.classMem A (syn_cwppstopact F C)) p0027 p0043
  have p0045 :=
    @g_impbid
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0020 p0044
  exact p0045

@[expose]
noncomputable def g_wppstopstepfvlecdndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvlecdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepfvlecdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
        (.imp (syn_wbr A (syn_clec) C)
          (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A)))) :=
  by
  have p0000 := @g_wppstopactlecbindv A C F
  have p0001 :=
    @g_biimprd
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0000
  have p0002 :=
    @g_wppstopstepfvactclndv A C F hyp_wppstopstepfvlecdndv_1 hyp_wppstopstepfvlecdndv_2
  have p0003 :=
    @g_syl6
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (syn_wbr A (syn_clec) C) (.classMem A (syn_cwppstopact F C))
      (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A)) p0001 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part054`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppstopstepfvnlecdndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvnlecdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepfvnlecdndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
        (.imp (.neg (syn_wbr A (syn_clec) C))
          (.classEq (syn_cfv (syn_cwppstopstep F C) A) A))) :=
  by
  have p0000 :=
    @g_simpl (.classMem A (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))
  have p0001 :=
    @g_a1d
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.classMem A (syn_chwcards (syn_cvv))) (.neg (syn_wbr A (syn_clec) C)) p0000
  have p0002 := @g_wppstopactlecbindv A C F
  have p0003 :=
    @g_biimpd
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0002
  have p0004 :=
    @g_con3d
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0003
  have p0005 :=
    @g_jcad
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.neg (syn_wbr A (syn_clec) C)) (.classMem A (syn_chwcards (syn_cvv)))
      (.neg (.classMem A (syn_cwppstopact F C))) p0001 p0004
  have p0006 :=
    @g_wppstopstepfvidleclndv A C F hyp_wppstopstepfvnlecdndv_1
      hyp_wppstopstepfvnlecdndv_2
  have p0007 :=
    @g_syl6
      (syn_wa (.classMem A (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F))))
      (.neg (syn_wbr A (syn_clec) C))
      (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))))
      (.classEq (syn_cfv (syn_cwppstopstep F C) A) A) p0005 p0006
  exact p0007

@[expose]
noncomputable def g_wppstopsteptchomdndv (x : Var) (C : Class) (F : Class)
    (hyp_wppstopsteptchomdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopsteptchomdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopsteptchomdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
          (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))) :=
  by
  have p0000 :=
    @g_simpr
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C)
  have p0001 :=
    @g_simpl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C)
  have p0002 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0003 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0004 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0002 p0003
  have p0006 :=
    @g_simpr (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0007 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
      p0002 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))
  have p0009 :=
    @g_syl6
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C)
      (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))
      (.classMem (.cv x) (syn_cdm F)) p0007 p0008
  have p0010 :=
    @g_jca
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F))) p0004 p0009
  have p0011 :=
    @g_wppstopstepfvlecdndv (.cv x) C F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0012 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))))
      p0010 p0011
  have p0013 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))))
      p0001 p0012
  have p0014 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_wbr (.cv x) (syn_clec) C)
      (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))) p0000 p0013
  have p0015 := @g_tceq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))
  have p0016 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x)))
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
        (syn_ctc (syn_cfv F (.cv x))))
      p0014 p0015
  have p0019 :=
    @g_n_3simpc (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0020 :=
    @g_simpr
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0021 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
            (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
      p0019 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (syn_wbr (.cv x) (syn_clec) C)
        (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
      p0001 p0021
  have p0023 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_wbr (.cv x) (syn_clec) C)
      (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))) p0000 p0022
  have p0029 := @g_hwcardssnc (syn_cvv)
  have p0030 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv x) p0029
  have p0031 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (.cv x) (syn_cncs)) p0004
      p0030
  have p0033 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0029
  have p0034 := Nominal.mp hyp_wppstopsteptchomdndv_3 p0033
  have p0035 :=
    @g_a1i (.classMem C (syn_cncs))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      p0034
  have p0036 :=
    @g_jca
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs)) p0031 p0035
  have p0037 := @g_tlecg (.cv x) C
  have p0038 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wb (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)))
      p0036 p0037
  have p0039 :=
    @g_biimpd
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
      p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)))
      p0001 p0039
  have p0041 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
      p0000 p0040
  have p0046 := @g_hwcardstcclndv (.cv x)
  have p0047 := @g_id (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
  have p0048 :=
    @g_n_3syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) p0004 p0046 p0047
  have p0062 :=
    @g_biimprd
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
      p0038
  have p0066 :=
    @g_syld
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (syn_wbr (.cv x) (syn_clec) C)
      (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))
      p0062 p0007
  have p0067 :=
    @g_simpr (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))
  have p0068 :=
    @g_syl6
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
      (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))
      (.classMem (syn_ctc (.cv x)) (syn_cdm F)) p0066 p0067
  have p0069 :=
    @g_jca
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
        (.classMem (syn_ctc (.cv x)) (syn_cdm F)))
      p0048 p0068
  have p0070 :=
    @g_wppstopstepfvlecdndv (syn_ctc (.cv x)) (syn_ctc C) F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0071 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
      (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
        (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))
          (syn_cfv F (syn_ctc (.cv x)))))
      p0069 p0070
  have p0072 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
        (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))
          (syn_cfv F (syn_ctc (.cv x)))))
      p0001 p0071
  have p0073 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
      (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))
        (syn_cfv F (syn_ctc (.cv x))))
      p0041 p0072
  have p0074 :=
    @g_eqcomd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))
      (syn_cfv F (syn_ctc (.cv x))) p0073
  have p0075 :=
    @g_n_3eqtrd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (syn_wbr (.cv x) (syn_clec) C))
      (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (syn_cfv F (.cv x)))
      (syn_cfv F (syn_ctc (.cv x)))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) p0016 p0023 p0074
  have p0076 :=
    @g_ex
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C)
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
        (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))
      p0075
  have p0077 :=
    @g_simpr
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0078 :=
    @g_simpl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0088 :=
    @g_wppstopstepfvnlecdndv (.cv x) C F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0089 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F))))
      (.imp (.neg (syn_wbr (.cv x) (syn_clec) C))
        (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)))
      p0010 p0088
  have p0090 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (.neg (syn_wbr (.cv x) (syn_clec) C))
        (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)))
      p0078 p0089
  have p0091 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (.neg (syn_wbr (.cv x) (syn_clec) C))
      (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)) p0077 p0090
  have p0092 := @g_tceq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)
  have p0093 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x))
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (.cv x)))
      p0091 p0092
  have p0109 :=
    @g_notbid
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
      p0038
  have p0110 :=
    @g_biimpd
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.neg (syn_wbr (.cv x) (syn_clec) C))
      (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0109
  have p0111 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (.neg (syn_wbr (.cv x) (syn_clec) C))
        (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))))
      p0078 p0110
  have p0112 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (.neg (syn_wbr (.cv x) (syn_clec) C))
      (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0077 p0111
  have p0141 :=
    @g_wppstopstepfvnlecdndv (syn_ctc (.cv x)) (syn_ctc C) F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0142 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wa (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))
          (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
      (.imp (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)))
        (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))
          (syn_ctc (.cv x))))
      p0069 p0141
  have p0143 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.imp (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)))
        (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))
          (syn_ctc (.cv x))))
      p0078 p0142
  have p0144 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)))
      (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_ctc (.cv x)))
      p0112 p0143
  have p0145 :=
    @g_eqcomd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_ctc (.cv x)) p0144
  have p0146 :=
    @g_eqtrd
      (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F))
              (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C)
            (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
        (.neg (syn_wbr (.cv x) (syn_clec) C)))
      (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (.cv x))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) p0093 p0145
  have p0147 :=
    @g_ex
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (.neg (syn_wbr (.cv x) (syn_clec) C))
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
        (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))
      p0146
  have p0148 :=
    @g_pm2_61d
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C)
          (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
        (.imp (syn_wbr (.cv x) (syn_clec) C)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))))
      (syn_wbr (.cv x) (syn_clec) C)
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
        (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))
      p0076 p0147
  exact p0148


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part055`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6stoppedtchomndv (x : Var)
    (hyp_wppconcrete6stoppedtchomndv_1 :
      Nominal.NPrf (syn_wss (syn_crn (syn_cwppconcrete6fn)) (syn_chwcards (syn_cvv))))
    (hyp_wppconcrete6stoppedtchomndv_2 : Nominal.NPrf (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wral x (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x)))
          (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_ctc (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_singleton.mpr h)
  have dv_cache_0001 : p ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    p ∉
      ((Wff.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
            (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          Finset.mem_union, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @g_wppconcrete6fnfunsndv
  have p0001 :=
    @g_wppstopstepdmndv
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cwppconcrete6fn) p0000 hyp_wppconcrete6stoppedtchomndv_1
  have p0002 :=
    @g_eleq2i
      (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_chwcards (syn_cvv)) (.cv x) p0001
  have p0003 :=
    @g_biimpi
      (.classMem (.cv x) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0002
  have p0004 := @g_id (.classMem (.cv x) (syn_chwcards (syn_cvv)))
  have p0005 := @g_wppconcrete6thresholdtclecndv
  have p0006 := @g_wppconcrete6hncard1dmpaircovndv p p0005
  have p0007 :=
    @g_a1i
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
            (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0006
  have p0008 := @g_id (.classEq (.cv p) (.cv x))
  have p0009 :=
    @g_breq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_clec) p0008
  have p0011 :=
    @g_eleq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x) (syn_cdm (syn_cwppconcrete6fn))
      p0008
  have p0013 := @g_tceq (.cv p) (.cv x)
  have p0014 :=
    @g_syl (.classEq (.cv p) (.cv x)) (.classEq (.cv p) (.cv x))
      (.classEq (syn_ctc (.cv p)) (syn_ctc (.cv x))) p0008 p0013
  have p0015 :=
    @g_eleq1d (.classEq (.cv p) (.cv x)) (syn_ctc (.cv p)) (syn_ctc (.cv x))
      (syn_cdm (syn_cwppconcrete6fn)) p0014
  have p0016 :=
    @g_anbi12d (.classEq (.cv p) (.cv x))
      (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))) p0011 p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv p) (.cv x))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (.cv x) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
        (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))
      p0009 p0016
  have p0018 :=
    @g_rspcv
      (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
          (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))))
      p (.cv x) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0017
  have p0019 :=
    @g_mpd (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
            (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))))
      (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
          (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))))
      p0007 p0018
  have p0035 :=
    @g_simpl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))
  have p0036 :=
    @g_syl6 (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv x) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
        (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))
      (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) p0019 p0035
  have p0037 := @g_wppconcrete6tchomdmndv x
  have p0038 :=
    @g_syl6 (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv x) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))
      p0036 p0037
  have p0039 :=
    @g_n_3jca (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
          (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x)))))
      p0004 p0019 p0038
  have p0041 :=
    @g_wppstopsteptchomdndv x
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cwppconcrete6fn) p0000 hyp_wppconcrete6stoppedtchomndv_1
      hyp_wppconcrete6stoppedtchomndv_2
  have p0042 :=
    @g_syl (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
            (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) (.imp
          (syn_wbr (.cv x) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x)))
            (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))))
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x)))
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_ctc (.cv x))))
      p0039 p0041
  have p0043 :=
    @g_syl
      (.classMem (.cv x) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.classMem (.cv x) (syn_chwcards (syn_cvv)))
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x)))
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_ctc (.cv x))))
      p0003 p0042
  have p0044 :=
    @g_rgen
      (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x)))
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_ctc (.cv x))))
      x
      (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      p0043
  exact p0044

@[expose]
noncomputable def g_wppconcrete6rnhwcardsredndv (u : Var)
    (hyp_wppconcrete6rnhwcardsredndv_1 : Nominal.NPrf (syn_wral u (syn_cvv)
          (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
            (syn_chwcards (syn_cvv))))) :
    Nominal.NPrf (syn_wss (syn_crn (syn_cwppconcrete6fn)) (syn_chwcards (syn_cvv))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ≠ z := by exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0002 : u ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_z, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 :
    u ∉
      ((Wff.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z)))))
          (syn_chwcards (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((Wff.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_crn (syn_cwppcardt6fn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cwppconcrete6fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_wppconcrete6fnfnndv
  have p0001 := @g_wppconcrete6fndmndv
  have p0002 :=
    @g_eleq2i (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn)) (.cv x) p0001
  have p0003 :=
    @g_biimpri (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) p0002
  have p0004 := @g_wppconcrete6dmrepdndv x z dv_cache_0001
  have p0005 :=
    @g_id
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0006 :=
    @g_fveq2d
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.cv x)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (syn_cwppconcrete6fn) p0005
  have p0007 := @g_vex z
  have p0008 := @g_wppconcrete6fnvalndv (.cv z) p0007
  have p0009 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0008
  have p0010 :=
    @g_eqtrd
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_cfv (syn_cwppconcrete6fn) (.cv x))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) p0006 p0009
  have p0012 := @g_id (.classEq (.cv u) (.cv z))
  have p0013 := @g_pweqd (.classEq (.cv u) (.cv z)) (.cv u) (.cv z) p0012
  have p0014 :=
    @g_pweqd (.classEq (.cv u) (.cv z)) (syn_cpw (.cv u)) (syn_cpw (.cv z)) p0013
  have p0015 := @g_hnordeqdndv (syn_cpw (syn_cpw (.cv u))) (syn_cpw (syn_cpw (.cv z)))
  have p0016 :=
    @g_syl (.classEq (.cv u) (.cv z))
      (.classEq (syn_cpw (syn_cpw (.cv u))) (syn_cpw (syn_cpw (.cv z))))
      (.classEq (syn_chnord (syn_cpw (syn_cpw (.cv u))))
        (syn_chnord (syn_cpw (syn_cpw (.cv z)))))
      p0014 p0015
  have p0017 :=
    @g_hncardeqdndv (syn_chnord (syn_cpw (syn_cpw (.cv u))))
      (syn_chnord (syn_cpw (syn_cpw (.cv z))))
  have p0018 :=
    @g_syl (.classEq (.cv u) (.cv z))
      (.classEq (syn_chnord (syn_cpw (syn_cpw (.cv u))))
        (syn_chnord (syn_cpw (syn_cpw (.cv z)))))
      (.classEq (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))))
      p0016 p0017
  have p0019 :=
    @g_eleq1d (.classEq (.cv u) (.cv z))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv))
      p0018
  have p0020 :=
    @g_rspcv
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
        (syn_chwcards (syn_cvv)))
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z)))))
        (syn_chwcards (syn_cvv)))
      u (.cv z) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0019
  have p0021 :=
    @g_mpi (.classMem (.cv z) (syn_cvv))
      (syn_wral u (syn_cvv) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u)))))
          (syn_chwcards (syn_cvv))))
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z)))))
        (syn_chwcards (syn_cvv)))
      hyp_wppconcrete6rnhwcardsredndv_1 p0020
  have p0022 := Nominal.mp p0007 p0021
  have p0023 :=
    @g_a1i
      (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z)))))
        (syn_chwcards (syn_cvv)))
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0022
  have p0024 :=
    @g_eqeltrd
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_cfv (syn_cwppconcrete6fn) (.cv x))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv))
      p0010 p0023
  have p0025 :=
    @g_exlimiv
      (.classEq (.cv x)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) z
      dv_cache_0005 p0024
  have p0026 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (syn_wex z (.classEq (.cv x)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) p0004
      p0025
  have p0027 :=
    @g_syl (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn)))
      (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) p0003
      p0026
  have p0028 :=
    @g_rgen (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) x
      (syn_crn (syn_cwppcardt6fn)) p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn)))
      (syn_wral x (syn_crn (syn_cwppcardt6fn))
        (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))))
      p0000 p0028
  have p0030 :=
    @g_fnfvrnss x (syn_crn (syn_cwppcardt6fn)) (syn_chwcards (syn_cvv))
      (syn_cwppconcrete6fn) dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0031 := Nominal.mp p0029 p0030
  exact p0031

@[expose]
noncomputable def g_wppfreceqexndv (F : Class) (G : Class) (I : Class)
    (hyp_wppfreceqexndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppfreceqexndv_2 : Nominal.NPrf (.classMem G (syn_cfuns))) :
    Nominal.NPrf (.classMem (syn_cwppfreceq F G I) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppfreceq F G I))
  have p0001 := @g_eqid (syn_cfrec F I)
  have p0002 := @g_elex F (syn_cfuns)
  have p0003 := Nominal.mp hyp_wppfreceqexndv_1 p0002
  have p0004 := @g_frecex (syn_cfrec F I) F I p0001 p0003
  have p0005 := @g_cnvexg (syn_cfrec F I) (syn_cvv)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_eqid (syn_cfrec G I)
  have p0008 := @g_elex G (syn_cfuns)
  have p0009 := Nominal.mp hyp_wppfreceqexndv_2 p0008
  have p0010 := @g_frecex (syn_cfrec G I) G I p0007 p0009
  have p0011 :=
    @g_pm3_2i (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv))
      (.classMem (syn_cfrec G I) (syn_cvv)) p0006 p0010
  have p0012 := @g_coexg (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I) (syn_cvv) (syn_cvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @g_fixexg (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I)) (syn_cvv)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_eqeltri (syn_cwppfreceq F G I)
      (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))) (syn_cvv) p0000
      p0015
  exact p0016

@[expose]
noncomputable def g_wppfreceqvalndv (n : Var) (F : Class) (G : Class) (I : Class)
    (hyp_wppfreceqvalndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppfreceqvalndv_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_wppfreceqvalndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppfreceqvalndv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppfreceqvalndv_5 : Nominal.NPrf (.classMem I (syn_cdm G)))
    (hyp_wppfreceqvalndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I))
          (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppfreceq F G I))
  have p0001 :=
    @g_eleq2i (syn_cwppfreceq F G I)
      (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))) (.cv n) p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classMem (.cv n)
          (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I)))))
      (.classMem (.cv n) (syn_cnnc)) p0001
  have p0003 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppfreceqvalndv_1 hyp_wppfreceqvalndv_2
      hyp_wppfreceqvalndv_3
  have p0004 := @g_wpporbitfnndv F I
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_fnfun (syn_cnnc) (syn_cfrec F I)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_a1i (syn_wfun (syn_cfrec F I)) (.classMem (.cv n) (syn_cnnc)) p0007
  have p0009 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G))
      (syn_wss (syn_crn G) (syn_cdm G)) hyp_wppfreceqvalndv_4 hyp_wppfreceqvalndv_5
      hyp_wppfreceqvalndv_6
  have p0010 := @g_wpporbitfnndv G I
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @g_fnfun (syn_cnnc) (syn_cfrec G I)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @g_a1i (syn_wfun (syn_cfrec G I)) (.classMem (.cv n) (syn_cnnc)) p0013
  have p0018 := @g_fndm (syn_cnnc) (syn_cfrec F I)
  have p0019 := Nominal.mp p0005 p0018
  have p0020 := @g_eleq2i (syn_cdm (syn_cfrec F I)) (syn_cnnc) (.cv n) p0019
  have p0021 :=
    @g_biimpri (.classMem (.cv n) (syn_cdm (syn_cfrec F I)))
      (.classMem (.cv n) (syn_cnnc)) p0020
  have p0025 := @g_fndm (syn_cnnc) (syn_cfrec G I)
  have p0026 := Nominal.mp p0011 p0025
  have p0027 := @g_eleq2i (syn_cdm (syn_cfrec G I)) (syn_cnnc) (.cv n) p0026
  have p0028 :=
    @g_biimpri (.classMem (.cv n) (syn_cdm (syn_cfrec G I)))
      (.classMem (.cv n) (syn_cnnc)) p0027
  have p0029 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cdm (syn_cfrec F I)))
      (.classMem (.cv n) (syn_cdm (syn_cfrec G I))) p0021 p0028
  have p0030 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_cfrec F I))
      (syn_wfun (syn_cfrec G I))
      (syn_wa (.classMem (.cv n) (syn_cdm (syn_cfrec F I)))
        (.classMem (.cv n) (syn_cdm (syn_cfrec G I))))
      p0008 p0014 p0029
  have p0031 := @g_funeqfix (.cv n) (syn_cfrec F I) (syn_cfrec G I)
  have p0032 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_w3a (syn_wfun (syn_cfrec F I)) (syn_wfun (syn_cfrec G I))
        (syn_wa (.classMem (.cv n) (syn_cdm (syn_cfrec F I)))
          (.classMem (.cv n) (syn_cdm (syn_cfrec G I)))))
      (syn_wb (.classMem (.cv n)
          (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))))
        (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))
      p0030 p0031
  have p0033 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwppfreceq F G I))
      (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))))
      (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))) p0002
      p0032
  exact p0033

@[expose]
noncomputable def g_wppfreceqvalclndv (B : Class) (F : Class) (G : Class) (I : Class)
    (hyp_wppfreceqvalclndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppfreceqvalclndv_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_wppfreceqvalclndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppfreceqvalclndv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppfreceqvalclndv_5 : Nominal.NPrf (.classMem I (syn_cdm G)))
    (hyp_wppfreceqvalclndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppfreceq F G I))
          (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 :
    n ∉
      ((syn_wb (.classMem B (syn_cwppfreceq F G I))
          (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfreceq,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_wppfreceqvalndv n F G I hyp_wppfreceqvalclndv_1 hyp_wppfreceqvalclndv_2
      hyp_wppfreceqvalclndv_3 hyp_wppfreceqvalclndv_4 hyp_wppfreceqvalclndv_5
      hyp_wppfreceqvalclndv_6
  have p0001 :=
    @g_rgen
      (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I))
        (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))
      n (syn_cnnc) p0000
  have p0002 := @g_id (.classEq (.cv n) B)
  have p0003 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwppfreceq F G I) p0002
  have p0005 := @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F I) p0002
  have p0007 := @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec G I) p0002
  have p0008 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_cfv (syn_cfrec F I) (.cv n))
      (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) (.cv n))
      (syn_cfv (syn_cfrec G I) B) p0005 p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwppfreceq F G I))
      (.classMem B (syn_cwppfreceq F G I))
      (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))
      (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)) p0003 p0008
  have p0010 :=
    @g_rspcv
      (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I))
        (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))
      (syn_wb (.classMem B (syn_cwppfreceq F G I))
        (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
      n B (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009
  have p0011 :=
    @g_mpi (.classMem B (syn_cnnc))
      (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I))
          (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))))
      (syn_wb (.classMem B (syn_cwppfreceq F G I))
        (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
      p0001 p0010
  exact p0011

@[expose]
noncomputable def g_wppfrecprefixeqexndv (k : Var) (F : Class) (G : Class) (I : Class)
    (hyp_wppfrecprefixeqexndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppfrecprefixeqexndv_2 : Nominal.NPrf (.classMem G (syn_cfuns))) :
    Nominal.NPrf (.classMem (syn_cwppfrecprefixeq F G I k) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppfrecprefixeq F G I k))
  have p0001 := @g_nncex
  have p0002 := @g_lefinex
  have p0003 := @g_kqrelex (syn_clefin) p0002
  have p0004 := @g_cnvexg (syn_ckqrel (syn_clefin)) (syn_cvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_snex (.cv k)
  have p0007 :=
    @g_imaex (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)) p0005 p0006
  have p0008 :=
    @g_difex (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))
      p0001 p0007
  have p0009 :=
    @g_wppfreceqexndv F G I hyp_wppfrecprefixeqexndv_1 hyp_wppfrecprefixeqexndv_2
  have p0010 :=
    @g_unex
      (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
      (syn_cwppfreceq F G I) p0008 p0009
  have p0011 :=
    @g_eqeltri (syn_cwppfrecprefixeq F G I k)
      (syn_cun (syn_cdif (syn_cnnc)
          (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
        (syn_cwppfreceq F G I))
      (syn_cvv) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_wppfrecprefixeqvalndv (B : Class) (k : Var) (F : Class) (G : Class)
    (I : Class) (hyp_wppfrecprefixeqvalndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppfrecprefixeqvalndv_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_wppfrecprefixeqvalndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppfrecprefixeqvalndv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppfrecprefixeqvalndv_5 : Nominal.NPrf (.classMem I (syn_cdm G)))
    (hyp_wppfrecprefixeqvalndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppfrecprefixeq F G I k))
          (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
            (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppfrecprefixeq F G I k))
  have p0001 :=
    @g_eleq2i (syn_cwppfrecprefixeq F G I k)
      (syn_cun (syn_cdif (syn_cnnc)
          (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
        (syn_cwppfreceq F G I))
      B p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem B (syn_cwppfrecprefixeq F G I k)) (.classMem B (syn_cun
            (syn_cdif (syn_cnnc)
              (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
            (syn_cwppfreceq F G I))))
      (.classMem B (syn_cnnc)) p0001
  have p0003 :=
    @g_elun B
      (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
      (syn_cwppfreceq F G I)
  have p0004 :=
    @g_a1i
      (syn_wb (.classMem B (syn_cun (syn_cdif (syn_cnnc)
              (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
            (syn_cwppfreceq F G I))) (syn_wo (.classMem B (syn_cdif (syn_cnnc)
              (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
          (.classMem B (syn_cwppfreceq F G I))))
      (.classMem B (syn_cnnc)) p0003
  have p0005 :=
    @g_eldif B (syn_cnnc)
      (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))
  have p0006 :=
    @g_a1i
      (syn_wb (.classMem B (syn_cdif (syn_cnnc)
            (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
        (syn_wa (.classMem B (syn_cnnc)) (.neg (.classMem B
              (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))))
      (.classMem B (syn_cnnc)) p0005
  have p0007 := @g_id (.classMem B (syn_cnnc))
  have p0008 :=
    @g_biantrurd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
      p0007
  have p0009 :=
    @g_bitr4d (.classMem B (syn_cnnc))
      (.classMem B (syn_cdif (syn_cnnc)
          (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
      (syn_wa (.classMem B (syn_cnnc)) (.neg (.classMem B
            (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))))
      (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
      p0006 p0008
  have p0010 := @g_elimasn (syn_ccnv (syn_ckqrel (syn_clefin))) (.cv k) B
  have p0011 :=
    (Nominal.biimpRefl (syn_wbr (.cv k) (syn_ccnv (syn_ckqrel (syn_clefin))) B))
  have p0012 :=
    @g_bitr4i
      (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
      (.classMem (syn_cop (.cv k) B) (syn_ccnv (syn_ckqrel (syn_clefin))))
      (syn_wbr (.cv k) (syn_ccnv (syn_ckqrel (syn_clefin))) B) p0010 p0011
  have p0013 := @g_brcnv (.cv k) B (syn_ckqrel (syn_clefin))
  have p0014 :=
    @g_bitri
      (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
      (syn_wbr (.cv k) (syn_ccnv (syn_ckqrel (syn_clefin))) B)
      (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) p0012 p0013
  have p0015 :=
    @g_notbi
      (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
      (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
  have p0016 :=
    @g_mpbi
      (syn_wb (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
        (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))
      (syn_wb (.neg
          (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
        (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))))
      p0014 p0015
  have p0017 :=
    @g_a1i
      (syn_wb (.neg
          (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
        (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))))
      (.classMem B (syn_cnnc)) p0016
  have p0018 :=
    @g_bitrd (.classMem B (syn_cnnc))
      (.classMem B (syn_cdif (syn_cnnc)
          (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
      (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
      (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) p0009 p0017
  have p0019 :=
    @g_wppfreceqvalclndv B F G I hyp_wppfrecprefixeqvalndv_1 hyp_wppfrecprefixeqvalndv_2
      hyp_wppfrecprefixeqvalndv_3 hyp_wppfrecprefixeqvalndv_4 hyp_wppfrecprefixeqvalndv_5
      hyp_wppfrecprefixeqvalndv_6
  have p0020 :=
    @g_orbi12d (.classMem B (syn_cnnc))
      (.classMem B (syn_cdif (syn_cnnc)
          (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
      (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))
      (.classMem B (syn_cwppfreceq F G I))
      (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)) p0018 p0019
  have p0021 :=
    @g_bitrd (.classMem B (syn_cnnc))
      (.classMem B (syn_cun (syn_cdif (syn_cnnc)
            (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
          (syn_cwppfreceq F G I)))
      (syn_wo (.classMem B (syn_cdif (syn_cnnc)
            (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))
        (.classMem B (syn_cwppfreceq F G I)))
      (syn_wo (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))
        (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
      p0004 p0020
  have p0022 :=
    @g_imor (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
      (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))
  have p0023 :=
    @g_a1i
      (syn_wb (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
          (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
        (syn_wo (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))
          (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))))
      (.classMem B (syn_cnnc)) p0022
  have p0024 :=
    @g_bitr4d (.classMem B (syn_cnnc))
      (.classMem B (syn_cun (syn_cdif (syn_cnnc)
            (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
          (syn_cwppfreceq F G I)))
      (syn_wo (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))
        (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
      (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
        (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
      p0021 p0023
  have p0025 :=
    @g_bitrd (.classMem B (syn_cnnc)) (.classMem B (syn_cwppfrecprefixeq F G I k))
      (.classMem B (syn_cun (syn_cdif (syn_cnnc)
            (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))
          (syn_cwppfreceq F G I)))
      (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
        (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))
      p0002 p0024
  exact p0025

@[expose]
noncomputable def g_wppstopstepsamebelowdndv (y : Var) (C : Class) (F : Class) (p : Var)
    (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_p_y : p ≠ y)
    (hyp_wppstopstepsamebelowdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopstepsamebelowdndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopstepsamebelowdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppstopstepsamebelowdndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C))
    (hyp_wppstopstepsamebelowdndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
          (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))))) :=
  by
  have dv_cache_0001 : p ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_p_y,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    p ∉ ((Wff.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          Finset.mem_singleton, dv_p_y, dv_C_p, dv_F_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0001 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C)
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      hyp_wppstopstepsamebelowdndv_4
  have p0002 :=
    @g_jca
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C) p0000
      p0001
  have p0003 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0004 := @g_hwcardssnc (syn_cvv)
  have p0005 := @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0003
      p0006
  have p0009 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0004 hyp_wppstopstepsamebelowdndv_3
  have p0010 := @g_tccl C
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i (.classMem (syn_ctc C) (syn_cncs))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      p0011
  have p0015 :=
    @g_a1i (.classMem C (syn_cncs))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      p0009
  have p0016 :=
    @g_n_3jca
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs))
      (.classMem C (syn_cncs)) p0007 p0012 p0015
  have p0017 := @g_lectr (.cv y) (syn_ctc C) C
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs))
        (.classMem C (syn_cncs)))
      (.imp (syn_wa (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C))
        (syn_wbr (.cv y) (syn_clec) C))
      p0016 p0017
  have p0019 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wa (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C))
      (syn_wbr (.cv y) (syn_clec) C) p0002 p0018
  have p0022 := @g_id (.classEq (.cv p) (.cv y))
  have p0023 := @g_breq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) C (syn_clec) p0022
  have p0025 := @g_eleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_cdm F) p0022
  have p0026 :=
    @g_imbi12d (.classEq (.cv p) (.cv y)) (syn_wbr (.cv p) (syn_clec) C)
      (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))
      (.classMem (.cv y) (syn_cdm F)) p0023 p0025
  have p0027 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))
      (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p (.cv y)
      (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0026
  have p0028 :=
    @g_mpi (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wral p (syn_chwcards (syn_cvv))
        (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))
      (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F)))
      hyp_wppstopstepsamebelowdndv_5 p0027
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p0003 p0028
  have p0030 :=
    @g_jca
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p0003 p0029
  have p0031 :=
    @g_wppstopstepfvlecdndv (.cv y) C F hyp_wppstopstepsamebelowdndv_1
      hyp_wppstopstepsamebelowdndv_2
  have p0032 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))))
      (.imp (syn_wbr (.cv y) (syn_clec) C)
        (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv F (.cv y))))
      p0030 p0031
  have p0033 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wbr (.cv y) (syn_clec) C)
      (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv F (.cv y))) p0019 p0032
  have p0066 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F)) p0019 p0029
  have p0067 :=
    @g_ex (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F)) p0066
  have p0068 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F)))
      p0003 p0067
  have p0069 :=
    @g_jca
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F)))
      p0003 p0068
  have p0070 :=
    @g_wppstopstepfvlecdndv (.cv y) (syn_ctc C) F hyp_wppstopstepsamebelowdndv_1
      hyp_wppstopstepsamebelowdndv_2
  have p0071 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F))))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
        (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv F (.cv y))))
      p0069 p0070
  have p0072 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
      (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv F (.cv y)))
      p0000 p0071
  have p0073 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv F (.cv y)) p0072
  have p0074 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc C)))
      (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv F (.cv y))
      (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) p0033 p0073
  have p0075 :=
    @g_ex (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
      (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y))
        (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))
      p0074
  exact p0075


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part056`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppreachtchwboundedndv (x : Var) (C : Class) (F : Class) (G : Class)
    (r : Var) (p : Var) (d : Var) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv)
    (dv_C_x : x ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_G_p : p ∉ G.fv) (_dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_d_p : d ≠ p)
    (dv_d_r : d ≠ r) (dv_d_x : d ≠ x) (dv_p_r : p ≠ r) (_dv_p_x : p ≠ x) (_dv_r_x : r ≠ x)
    (hyp_wppreachtchwboundedndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachtchwboundedndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppreachtchwboundedndv_3 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppreachtchwboundedndv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppreachtchwboundedndv_5 : Nominal.NPrf (syn_wral x (syn_cdm F)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))))
    (hyp_wppreachtchwboundedndv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F))
              (.classMem (syn_ctc (.cv p)) (syn_cdm G))))))
    (hyp_wppreachtchwboundedndv_7 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc)
              (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))))))
    (hyp_wppreachtchwboundedndv_8 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
        (syn_wb (.classMem (.cv d) (syn_cwppreach F C))
          (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))))) :=
  by
  have dv_cache_0001 :
    p ∉
      ((syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_d_p), dv_C_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem
              (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                  (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc
                (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                    (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_d_p), dv_C_p, dv_F_p, dv_G_p,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    r ∉
      ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_p_r), (Ne.symm dv_d_r), dv_C_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wral r (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F (syn_cif
                    (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                      (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_d_p), dv_C_p, dv_p_r,
          dv_F_p, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    r ∉
      ((syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_d_r), dv_C_r, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    x ∉
      ((syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_d_x), dv_C_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_r, not_false_eq_true])
  have dv_cache_0009 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0010 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have p0000 :=
    @g_id
      (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0001 :=
    @g_eleq1d
      (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.cv d)
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      (syn_cwppreach F C) p0000
  have p0002 :=
    @g_tceq (.cv d)
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0003 :=
    @g_eleq1d
      (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_ctc (.cv d))
      (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_cwppreach G (syn_ctc C)) p0002
  have p0004 :=
    @g_bibi12d
      (.classEq (.cv d) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.classMem (.cv d) (syn_cwppreach F C))
      (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cwppreach F C))
      (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C)))
      (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cwppreach G (syn_ctc C)))
      p0001 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0006 :=
    @g_iftrue
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.cv d) C
  have p0007 :=
    @g_breq1d
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      (.cv d) C (syn_clec) p0006
  have p0008 :=
    @g_mpbird
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C)
      (syn_wbr (.cv d) (syn_clec) C) p0005 p0007
  have p0009 := @g_hwcardssnc (syn_cvv)
  have p0010 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0009
  have p0011 := Nominal.mp hyp_wppreachtchwboundedndv_8 p0010
  have p0012 := @g_nclecid C
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_a1i (syn_wbr C (syn_clec) C)
      (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)))
      p0013
  have p0015 :=
    @g_iffalse
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.cv d) C
  have p0016 :=
    @g_breq1d
      (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)))
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      C C (syn_clec) p0015
  have p0017 :=
    @g_mpbird
      (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)))
      (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C)
      (syn_wbr C (syn_clec) C) p0014 p0016
  have p0018 :=
    @g_pm2_61i
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C)
      p0008 p0017
  have p0019 := @g_tru
  have p0020 :=
    @g_simpr syn_wtru
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
  have p0021 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0022 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0020 p0021
  have p0023 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wa syn_wtru (.neg (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C))))
      hyp_wppreachtchwboundedndv_8
  have p0024 :=
    @g_ifclda syn_wtru
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.cv d) C (syn_chwcards (syn_cvv)) p0022 p0023
  have p0025 := Nominal.mp p0019 p0024
  have p0026 :=
    @g_pm3_2i
      (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv)))
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C)
          (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))))
      p0025 hyp_wppreachtchwboundedndv_6
  have p0027 :=
    @g_id
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
  have p0028 :=
    @g_breq1d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.cv p)
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      C (syn_clec) p0027
  have p0030 :=
    @g_eleq1d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.cv p)
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      (syn_cdm F) p0027
  have p0031 :=
    @g_tceq (.cv p)
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0032 :=
    @g_eleq1d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_ctc (.cv p))
      (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_cdm G) p0031
  have p0033 :=
    @g_anbi12d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.classMem (.cv p) (syn_cdm F))
      (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F))
      (.classMem (syn_ctc (.cv p)) (syn_cdm G))
      (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))
      p0030 p0032
  have p0034 :=
    @g_imbi12d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_wbr (.cv p) (syn_clec) C)
      (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C)
      (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))
      (syn_wa (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc
            (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G)))
      p0028 p0033
  have p0035 :=
    @g_rspcva
      (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F))
          (.classMem (syn_ctc (.cv p)) (syn_cdm G))))
      (.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wa (.classMem
            (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F)) (.classMem (syn_ctc
              (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                  (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))))
      p
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0034
  have p0036 := Nominal.mp p0026 p0035
  have p0037 := Nominal.mp p0018 p0036
  have p0038 :=
    @g_simpl
      (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F))
      (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))
  have p0039 := Nominal.mp p0037 p0038
  have p0073 :=
    @g_simpr
      (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cdm F))
      (.classMem (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cdm G))
  have p0074 := Nominal.mp p0037 p0073
  have p0099 :=
    @g_pm3_2i
      (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_chwcards (syn_cvv)))
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C)
          (syn_wral r (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)))))
      p0025 hyp_wppreachtchwboundedndv_7
  have p0102 :=
    @g_eqidd
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      F
  have p0104 :=
    @g_jca
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.classEq F F)
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      p0102 p0027
  have p0105 :=
    @g_freceq12 F F (.cv p)
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
  have p0106 :=
    @g_syl
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_wa (.classEq F F) (.classEq (.cv p) (syn_cif
            (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
            (.cv d) C)))
      (.classEq (syn_cfrec F (.cv p)) (syn_cfrec F (syn_cif
            (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
            (.cv d) C)))
      p0104 p0105
  have p0107 :=
    @g_fveq1d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.cv r) (syn_cfrec F (.cv p))
      (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      p0106
  have p0108 :=
    @g_eleq1d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_cfv (syn_cfrec F (.cv p)) (.cv r))
      (syn_cfv (syn_cfrec F (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r))
      (syn_cncs) p0107
  have p0109 :=
    @g_ralbidv
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F (syn_cif
              (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs))
      r (syn_cnnc) dv_cache_0004 p0108
  have p0110 :=
    @g_imbi12d
      (.classEq (.cv p) (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C))
      (syn_wbr (.cv p) (syn_clec) C)
      (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
            (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C)
      (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)))
      (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (syn_cif
                (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                  (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs)))
      p0028 p0109
  have p0111 :=
    @g_rspcva
      (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc)
          (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))))
      (.imp (syn_wbr (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_clec) C) (syn_wral r (syn_cnnc)
          (.classMem (syn_cfv (syn_cfrec F (syn_cif
                  (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                    (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (.cv r)) (syn_cncs))))
      p
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0005 p0110
  have p0112 := Nominal.mp p0099 p0111
  have p0113 := Nominal.mp p0018 p0112
  have p0114 :=
    @g_wppreachtcbidv x C
      (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)
      F G r dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      hyp_wppreachtchwboundedndv_1 p0039 hyp_wppreachtchwboundedndv_2
      hyp_wppreachtchwboundedndv_3 p0074 hyp_wppreachtchwboundedndv_4
      hyp_wppreachtchwboundedndv_5 p0011 p0113
  have p0115 :=
    @g_dedth
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (syn_wb (.classMem (.cv d) (syn_cwppreach F C))
        (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))))
      (syn_wb (.classMem (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
              (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C) (syn_cwppreach F C)) (.classMem
          (syn_ctc (syn_cif (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
                (syn_wbr (.cv d) (syn_clec) C)) (.cv d) C)) (syn_cwppreach G (syn_ctc C))))
      (.cv d) C p0004 p0114
  exact p0115


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part057`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppcandtchwboundedimagebindv (x : Var) (C : Class) (k : Var)
    (F : Class) (G : Class) (r : Var) (p : Var) (d : Var) (dv_C_d : d ∉ C.fv)
    (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_d : d ∉ F.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_d : d ∉ G.fv)
    (dv_G_p : p ∉ G.fv) (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_d_k : d ≠ k)
    (dv_d_p : d ≠ p) (dv_d_r : d ≠ r) (dv_d_x : d ≠ x) (_dv_k_p : k ≠ p) (_dv_k_r : k ≠ r)
    (_dv_k_x : k ≠ x) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x) (dv_r_x : r ≠ x)
    (hyp_wppcandtchwboundedimagebindv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppcandtchwboundedimagebindv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppcandtchwboundedimagebindv_3 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppcandtchwboundedimagebindv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppcandtchwboundedimagebindv_5 : Nominal.NPrf (syn_wral x (syn_cdm F)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))))
    (hyp_wppcandtchwboundedimagebindv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F))
              (.classMem (syn_ctc (.cv p)) (syn_cdm G))))))
    (hyp_wppcandtchwboundedimagebindv_7 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc)
              (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))))))
    (hyp_wppcandtchwboundedimagebindv_8 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wex d
          (syn_wa (.classMem (.cv d) (syn_cwppcand F C))
            (.classEq (.cv k) (syn_ctc (.cv d)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ C.fv ∪ ({ k } : Finset Var) ∪ F.fv ∪ G.fv ∪
          ({ r } : Finset Var) ∪
        ({ p } : Finset Var) ∪
      ({ d } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_q_ne_k : q ≠ k := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_q_not_G : q ∉ G.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_q_ne_d : q ≠ d := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_q : d ≠ q := Ne.symm fresh_q_ne_d
  have dv_cache_0001 : q ∉ ((Class.cv k)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_k, not_false_eq_true])
  have dv_cache_0002 : p ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0003 : r ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_r, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0005 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0006 : r ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_r, not_false_eq_true])
  have dv_cache_0007 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0008 : p ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_p, not_false_eq_true])
  have dv_cache_0009 : r ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_r, not_false_eq_true])
  have dv_cache_0010 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have dv_cache_0011 : q ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show q ≠ p from (by exact fresh_q_ne_p))
  have dv_cache_0012 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0013 : q ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0014 : p ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show p ≠ r from (by exact dv_p_r))
  have dv_cache_0015 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0016 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show r ≠ x from (by exact dv_r_x))
  have dv_cache_0017 : d ∉ ((Class.cv q)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_q, not_false_eq_true])
  have dv_cache_0018 :
    d ∉
      ((syn_wa (.classMem (.cv q) (syn_cwppcand F C))
          (.classEq (.cv k) (syn_ctc (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_q, dv_C_d, dv_F_d, dv_d_k, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    q ∉
      ((syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C))
            (.classEq (.cv k) (syn_ctc (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_d, fresh_q_not_C,
          fresh_q_not_F, fresh_q_ne_k, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((Wff.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_k, fresh_q_not_C, fresh_q_not_G, or_false,
          not_false_eq_true])
  have dv_cache_0021 : d ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show d ≠ p from (by exact dv_d_p))
  have dv_cache_0022 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show d ≠ r from (by exact dv_d_r))
  have dv_cache_0023 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ x from (by exact dv_d_x))
  have dv_cache_0024 : d ∉ ((Wff.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          Finset.mem_singleton, dv_d_k, dv_C_d, dv_G_d, or_false, not_false_eq_true])
  have p0000 := @g_elwppcand (syn_ctc C) (.cv k) G
  have p0001 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
        (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
      (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0003 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
        (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))))
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
      p0001 p0002
  have p0004 :=
    @g_simpl (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0005 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) p0003 p0004
  have p0006 := @g_hwcardssnc (syn_cvv)
  have p0007 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv k) p0006
  have p0008 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv k) (syn_cncs)) p0005
      p0007
  have p0010 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0006
  have p0011 := Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0010
  have p0012 :=
    @g_a1i (.classMem C (syn_cncs)) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) p0011
  have p0017 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0018 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
      (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0003 p0017
  have p0019 :=
    @g_n_3jca (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (.classMem (.cv k) (syn_cncs)) (.classMem C (syn_cncs))
      (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0008 p0012 p0018
  have p0020 := @g_letc (.cv k) C q dv_cache_0001
  have p0021 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_w3a (.classMem (.cv k) (syn_cncs)) (.classMem C (syn_cncs))
        (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
      (syn_wrex q (syn_cncs) (.classEq (.cv k) (syn_ctc (.cv q)))) p0019 p0020
  have p0022 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0023 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0024 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
      (.classMem (.cv q) (syn_cncs)) p0022 p0023
  have p0025 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      hyp_wppcandtchwboundedimagebindv_8
  have p0026 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))) p0024 p0025
  have p0027 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0034 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0027 p0018
  have p0036 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0037 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
      (.classEq (.cv k) (syn_ctc (.cv q))) p0022 p0036
  have p0038 := @g_id (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0039 :=
    @g_breq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q)) (syn_ctc C)
      (syn_clec) p0038
  have p0040 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classEq (.cv k) (syn_ctc (.cv q)))
      (syn_wb (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
        (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)))
      p0037 p0039
  have p0041 :=
    @g_mpbid
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
      (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0034 p0040
  have p0048 :=
    @g_a1i (.classMem C (syn_cncs))
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      p0011
  have p0049 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) p0024 p0048
  have p0050 := @g_tlecg (.cv q) C
  have p0051 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wb (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)))
      p0049 p0050
  have p0052 :=
    @g_mpbird
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))
      p0041 p0051
  have p0053 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
      (syn_wbr (.cv q) (syn_clec) C) p0026 p0052
  have p0054 := @g_hwcardsdownltcndv C q
  have p0055 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv q) (syn_clec) C))
      (.classMem (.cv q) (syn_chwcards (syn_cvv))) p0053 p0054
  have p0082 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C) p0055
      p0052
  have p0086 :=
    @g_simpr
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
      (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0087 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) (syn_ctc C)))
        (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))))
      (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))) p0001 p0086
  have p0088 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))) p0027 p0087
  have p0093 :=
    @g_eleq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q))
      (syn_cwppreach G (syn_ctc C)) p0038
  have p0094 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classEq (.cv k) (syn_ctc (.cv q)))
      (syn_wb (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
        (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C))))
      p0037 p0093
  have p0095 :=
    @g_mpbid
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
      (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C))) p0088 p0094
  have p0157 :=
    @g_wppreachtchwboundedndv x C F G r p q dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      hyp_wppcandtchwboundedimagebindv_1 hyp_wppcandtchwboundedimagebindv_2
      hyp_wppcandtchwboundedimagebindv_3 hyp_wppcandtchwboundedimagebindv_4
      hyp_wppcandtchwboundedimagebindv_5 hyp_wppcandtchwboundedimagebindv_6
      hyp_wppcandtchwboundedimagebindv_7 hyp_wppcandtchwboundedimagebindv_8
  have p0158 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C))
      (syn_wb (.classMem (.cv q) (syn_cwppreach F C))
        (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C))))
      p0082 p0157
  have p0159 :=
    @g_mpbird
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv q) (syn_cwppreach F C))
      (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C))) p0095 p0158
  have p0160 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C))
      (.classMem (.cv q) (syn_cwppreach F C)) p0082 p0159
  have p0161 := @g_elwppcand C (.cv q) F
  have p0162 :=
    @g_biimpri (.classMem (.cv q) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_cwppreach F C)))
      p0161
  have p0163 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_cwppreach F C)))
      (.classMem (.cv q) (syn_cwppcand F C)) p0160 p0162
  have p0167 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q))) p0163
      p0037
  have p0168 := @g_vex q
  have p0169 := @g_id (.classEq (.cv d) (.cv q))
  have p0170 :=
    @g_eleq1d (.classEq (.cv d) (.cv q)) (.cv d) (.cv q) (syn_cwppcand F C) p0169
  have p0171 := @g_tceq (.cv d) (.cv q)
  have p0172 :=
    @g_eqeq2d (.classEq (.cv d) (.cv q)) (syn_ctc (.cv d)) (syn_ctc (.cv q)) (.cv k) p0171
  have p0173 :=
    @g_anbi12d (.classEq (.cv d) (.cv q)) (.classMem (.cv d) (syn_cwppcand F C))
      (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
      (.classEq (.cv k) (syn_ctc (.cv q))) p0170 p0172
  have p0174 :=
    @g_spcev
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q))))
      d (.cv q) dv_cache_0017 dv_cache_0018 p0168 p0173
  have p0175 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q))))
      (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C))
          (.classEq (.cv k) (syn_ctc (.cv d)))))
      p0167 p0174
  have p0176 :=
    @g_rexlimddv (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (.classEq (.cv k) (syn_ctc (.cv q)))
      (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C))
          (.classEq (.cv k) (syn_ctc (.cv d)))))
      q (syn_cncs) dv_cache_0019 dv_cache_0020 p0021 p0175
  have p0177 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0178 := @g_elwppcand C (.cv d) F
  have p0179 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      p0178
  have p0180 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      p0177 p0179
  have p0181 :=
    @g_simpl
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_cwppreach F C))
  have p0182 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      p0180 p0181
  have p0183 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0184 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0182 p0183
  have p0185 := @g_hwcardstcclndv (.cv d)
  have p0186 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv))) p0184 p0185
  have p0193 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0194 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (syn_wbr (.cv d) (syn_clec) C) p0182 p0193
  have p0204 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv d) p0006
  have p0205 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) (.classMem (.cv d) (syn_cncs)) p0184
      p0204
  have p0209 :=
    @g_a1i (.classMem C (syn_cncs))
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      p0011
  have p0210 :=
    @g_jca
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_cncs)) p0205 p0209
  have p0211 := @g_tlecg (.cv d) C
  have p0212 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_cncs)))
      (syn_wb (syn_wbr (.cv d) (syn_clec) C) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)))
      p0210 p0211
  have p0213 :=
    @g_mpbid
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wbr (.cv d) (syn_clec) C) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C))
      p0194 p0212
  have p0214 :=
    @g_jca
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)) p0186 p0213
  have p0219 :=
    @g_simpr
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_cwppreach F C))
  have p0220 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      (.classMem (.cv d) (syn_cwppreach F C)) p0180 p0219
  have p0237 :=
    @g_jca
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C) p0184
      p0194
  have p0238 :=
    @g_wppreachtchwboundedndv x C F G r p d dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0014 dv_cache_0015 dv_cache_0016
      hyp_wppcandtchwboundedimagebindv_1 hyp_wppcandtchwboundedimagebindv_2
      hyp_wppcandtchwboundedimagebindv_3 hyp_wppcandtchwboundedimagebindv_4
      hyp_wppcandtchwboundedimagebindv_5 hyp_wppcandtchwboundedimagebindv_6
      hyp_wppcandtchwboundedimagebindv_7 hyp_wppcandtchwboundedimagebindv_8
  have p0239 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (syn_wb (.classMem (.cv d) (syn_cwppreach F C))
        (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))))
      p0237 p0238
  have p0240 :=
    @g_mpbid
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_cwppreach F C))
      (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))) p0220 p0239
  have p0241 :=
    @g_jca
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)))
      (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))) p0214 p0240
  have p0242 := @g_elwppcand (syn_ctc C) (syn_ctc (.cv d)) G
  have p0243 :=
    @g_biimpri (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C)))
      (syn_wa (syn_wa (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)))
        (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))))
      p0242
  have p0244 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (syn_wa (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)))
        (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))))
      (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C))) p0241 p0243
  have p0245 :=
    @g_simpr (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0246 := @g_id (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0247 :=
    @g_eleq1d (.classEq (.cv k) (syn_ctc (.cv d))) (.cv k) (syn_ctc (.cv d))
      (syn_cwppcand G (syn_ctc C)) p0246
  have p0248 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classEq (.cv k) (syn_ctc (.cv d)))
      (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C))))
      p0245 p0247
  have p0249 :=
    @g_mpbird
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C))) p0244 p0248
  have p0250 :=
    @g_exlimiv
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) d dv_cache_0024 p0249
  have p0251 :=
    @g_impbii (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C))
          (.classEq (.cv k) (syn_ctc (.cv d)))))
      p0176 p0250
  exact p0251


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part058`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppgammatchwboundedeqndv (x : Var) (C : Class) (F : Class) (G : Class)
    (r : Var) (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_p : p ∉ G.fv)
    (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x)
    (dv_r_x : r ≠ x)
    (hyp_wppgammatchwboundedeqndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppgammatchwboundedeqndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppgammatchwboundedeqndv_3 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppgammatchwboundedeqndv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppgammatchwboundedeqndv_5 : Nominal.NPrf (syn_wral x (syn_cdm F)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))))
    (hyp_wppgammatchwboundedeqndv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F))
              (.classMem (syn_ctc (.cv p)) (syn_cdm G))))))
    (hyp_wppgammatchwboundedeqndv_7 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc)
              (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs))))))
    (hyp_wppgammatchwboundedeqndv_8 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ C.fv ∪ F.fv ∪ G.fv ∪ ({ r } : Finset Var) ∪
      ({ p } : Finset Var)
  let k : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_ne_x : k ≠ x := by
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
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_ne_r : k ≠ r := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_p : k ≠ p := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_r : d ≠ r := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_d_ne_p : d ≠ p := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_k_ne_d : k ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have dv_cache_0001 : d ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0002 : p ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0003 : r ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_r, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_F, not_false_eq_true])
  have dv_cache_0006 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0007 : r ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_r, not_false_eq_true])
  have dv_cache_0008 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0009 : d ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_G, not_false_eq_true])
  have dv_cache_0010 : p ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_p, not_false_eq_true])
  have dv_cache_0011 : r ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_r, not_false_eq_true])
  have dv_cache_0012 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have dv_cache_0013 : d ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0014 : d ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show d ≠ p from (by exact fresh_d_ne_p))
  have dv_cache_0015 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0016 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0017 : k ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show k ≠ p from (by exact fresh_k_ne_p))
  have dv_cache_0018 : k ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show k ≠ r from (by exact fresh_k_ne_r))
  have dv_cache_0019 : k ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show k ≠ x from (by exact fresh_k_ne_x))
  have dv_cache_0020 : p ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show p ≠ r from (by exact dv_p_r))
  have dv_cache_0021 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0022 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ x from (by exact dv_r_x))
  have dv_cache_0023 : k ∉ (C).fv :=
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
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0024 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0025 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_G, not_false_eq_true])
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wppgammatchwboundedeqndv_1 p0000
  have p0002 := @g_elex G (syn_cfuns)
  have p0003 := Nominal.mp hyp_wppgammatchwboundedeqndv_3 p0002
  have p0004 := @g_hwcardstcclndv C
  have p0005 := Nominal.mp hyp_wppgammatchwboundedeqndv_8 p0004
  have p0006 :=
    @g_wppcandtchwboundedimagebindv x C k F G r p d dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 hyp_wppgammatchwboundedeqndv_1
      hyp_wppgammatchwboundedeqndv_2 hyp_wppgammatchwboundedeqndv_3
      hyp_wppgammatchwboundedeqndv_4 hyp_wppgammatchwboundedeqndv_5
      hyp_wppgammatchwboundedeqndv_6 hyp_wppgammatchwboundedeqndv_7
      hyp_wppgammatchwboundedeqndv_8
  have p0007 :=
    (Nominal.biimpRefl (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))))
  have p0008 :=
    @g_bitr4i (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C))
          (.classEq (.cv k) (syn_ctc (.cv d)))))
      (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))) p0006 p0007
  have p0009 := Nominal.gen p0008 k
  have p0010 :=
    @g_wppgammaimagetceqndv C k F G d dv_cache_0001 dv_cache_0023 dv_cache_0005
      dv_cache_0024 dv_cache_0009 dv_cache_0025 dv_cache_0013 p0001
      hyp_wppgammatchwboundedeqndv_8 p0003 p0005 p0009
  exact p0010

@[expose]
noncomputable def g_wppgammadomhwndv (C : Class) (F : Class) (p : Var) (dv_C_p : p ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (hyp_wppgammadomhwndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppgammadomhwndv_2 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppgammadomhwndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppgamma F C) (syn_cdm F)) :=
  by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ ({ p } : Finset Var)
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0002 : k ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_cwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_C_p, dv_F_p, or_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0005 :
    p ∉
      ((Wff.imp (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
          (.classMem (syn_cwppgamma F C) (syn_cdm F)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, dv_C_p,
          dv_F_p, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))
      hyp_wppgammadomhwndv_1 hyp_wppgammadomhwndv_3
  have p0001 := @g_wppgammaminhwndv C k F dv_cache_0001 dv_cache_0002
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_elwppcand C (syn_cwppgamma F C) F
  have p0006 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma F C) (syn_clec) C))
        (.classMem (syn_cwppgamma F C) (syn_cwppreach F C)))
      p0005
  have p0007 := Nominal.mp p0004 p0006
  have p0008 :=
    @g_simpl
      (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma F C) (syn_clec) C))
      (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_simpr (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0011 := Nominal.mp p0009 p0010
  have p0022 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0023 := Nominal.mp p0009 p0022
  have p0024 :=
    @g_pm3_2i (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
      (syn_wral p (syn_chwcards (syn_cvv))
        (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))
      p0023 hyp_wppgammadomhwndv_2
  have p0025 := @g_id (.classEq (.cv p) (syn_cwppgamma F C))
  have p0026 :=
    @g_breq1d (.classEq (.cv p) (syn_cwppgamma F C)) (.cv p) (syn_cwppgamma F C) C
      (syn_clec) p0025
  have p0028 :=
    @g_eleq1d (.classEq (.cv p) (syn_cwppgamma F C)) (.cv p) (syn_cwppgamma F C)
      (syn_cdm F) p0025
  have p0029 :=
    @g_imbi12d (.classEq (.cv p) (syn_cwppgamma F C)) (syn_wbr (.cv p) (syn_clec) C)
      (syn_wbr (syn_cwppgamma F C) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))
      (.classMem (syn_cwppgamma F C) (syn_cdm F)) p0026 p0028
  have p0030 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))
      (.imp (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
        (.classMem (syn_cwppgamma F C) (syn_cdm F)))
      p (syn_cwppgamma F C) (syn_chwcards (syn_cvv)) dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0029
  have p0031 := Nominal.mp p0024 p0030
  have p0032 := Nominal.mp p0011 p0031
  exact p0032

@[expose]
noncomputable def g_wppgammareachexhwndv (C : Class) (n : Var) (F : Class) (p : Var)
    (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv)
    (_dv_n_p : n ≠ p)
    (hyp_wppgammareachexhwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppgammareachexhwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppgammareachexhwndv_3 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppgammareachexhwndv_4 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wrex n (syn_cnnc)
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv n)))) :=
  by
  have dv_cache_0001 : p ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0002 : p ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0003 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wppgammareachexhwndv_1 p0000
  have p0002 := @g_wppgammareachndv C F p0001 hyp_wppgammareachexhwndv_4
  have p0005 :=
    @g_wppgammadomhwndv C F p dv_cache_0001 dv_cache_0002 p0001 hyp_wppgammareachexhwndv_3
      hyp_wppgammareachexhwndv_4
  have p0006 := @g_elex C (syn_chwcards (syn_cvv))
  have p0007 := Nominal.mp hyp_wppgammareachexhwndv_4 p0006
  have p0008 :=
    @g_wppreachfwdrexvndv C (syn_cwppgamma F C) n F dv_cache_0003 dv_cache_0004
      dv_cache_0005 hyp_wppgammareachexhwndv_1 p0005 hyp_wppgammareachexhwndv_2 p0007
  have p0009 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
      (syn_wrex n (syn_cnnc)
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv n))))
      p0008
  have p0010 := Nominal.mp p0002 p0009
  exact p0010

@[expose]
noncomputable def g_wppgammaleasthithwndv (C : Class) (m : Var) (n : Var) (F : Class)
    (p : Var) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_m_n : m ≠ n)
    (hyp_wppgammaleasthithwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppgammaleasthithwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppgammaleasthithwndv_3 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppgammaleasthithwndv_4 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F (syn_cwppgamma F C) C))
          (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F (syn_cwppgamma F C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) :=
  by
  let proofSupport : Finset Var :=
    C.fv ∪ ({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪ F.fv ∪ ({ p } : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_q_ne_m : q ≠ m := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_m_ne_q : m ≠ q := Ne.symm fresh_q_ne_m
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_q : n ≠ q := Ne.symm fresh_q_ne_n
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : q ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0002 : p ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0003 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_F, not_false_eq_true])
  have dv_cache_0004 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0005 : q ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ p from (by exact fresh_q_ne_p))
  have dv_cache_0006 : m ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0007 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
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
        simp only [dv_F_m, not_false_eq_true])
  have dv_cache_0009 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((syn_cwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((syn_cwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_cwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_q_not_C, fresh_q_not_F, or_false, not_false_eq_true])
  have dv_cache_0013 : m ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((syn_ckqrel (syn_clefin))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 : q ∉ ((syn_ckqrel (syn_clefin))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0017 : m ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show m ≠ q from (by exact fresh_m_ne_q))
  have dv_cache_0018 : n ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have p0000 := @g_finlewe
  have p0001 :=
    @g_wppgammareachexhwndv C q F p dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_wppgammaleasthithwndv_1 hyp_wppgammaleasthithwndv_2
      hyp_wppgammaleasthithwndv_3 hyp_wppgammaleasthithwndv_4
  have p0002 := @g_elex F (syn_cfuns)
  have p0003 := Nominal.mp hyp_wppgammaleasthithwndv_1 p0002
  have p0004 :=
    @g_wppgammadomhwndv C F p dv_cache_0002 dv_cache_0004 p0003
      hyp_wppgammaleasthithwndv_3 hyp_wppgammaleasthithwndv_4
  have p0005 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem (syn_cwppgamma F C) (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppgammaleasthithwndv_1 p0004
      hyp_wppgammaleasthithwndv_2
  have p0006 := @g_elwpphitvndv C F (syn_cwppgamma F C) (.cv q)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_biimpri (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C))
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q))))
      p0007
  have p0009 :=
    @g_expcom (.classMem (.cv q) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q)))
      (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) p0008
  have p0010 :=
    @g_com12 (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q)))
      (.classMem (.cv q) (syn_cnnc))
      (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) p0009
  have p0011 :=
    @g_reximia (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F C)) (.cv q)))
      (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)) q (syn_cnnc) p0010
  have p0012 := Nominal.mp p0001 p0011
  have p0013 :=
    @g_pm3_2i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc))
      (syn_wrex q (syn_cnnc) (.classMem (.cv q) (syn_cwpphit F (syn_cwppgamma F C) C)))
      p0000 p0012
  have p0016 :=
    @g_wpphitminexvndv q C (syn_ckqrel (syn_clefin)) m n F (syn_cwppgamma F C)
      dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0003
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 p0003
  have p0017 := Nominal.mp p0013 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end
