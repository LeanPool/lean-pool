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

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6tchomdmndv`. -/
@[expose]
noncomputable def gWppconcrete6tchomdmndv (x : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
        (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
          (synCfv (synCwppconcrete6fn) (synCtc (.cv x))))) :=
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
      ((Wff.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
          (synCfv (synCwppconcrete6fn) (synCtc (.cv x))))).fv :=
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
  have p0000 := @gWppconcrete6dmrepdndv x z dv_cache_0001
  have p0001 :=
    @gId
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
  have p0002 :=
    @gFveq2 (.cv x)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (synCwppconcrete6fn)
  have p0003 :=
    @gSyl
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (synCfv (synCwppconcrete6fn) (.cv x)) (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0001 p0002
  have p0004 :=
    @gTceq (synCfv (synCwppconcrete6fn) (.cv x))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
  have p0005 :=
    @gSyl
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (synCfv (synCwppconcrete6fn) (.cv x)) (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x))) (synCtc
          (synCfv (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))))
      p0003 p0004
  have p0006 := @gVex z
  have p0007 := @gWppconcrete6canonicaltchomndv (.cv z) p0006
  have p0008 :=
    @gA1i
      (.classEq (synCtc (synCfv (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0007
  have p0010 :=
    @gTceq (.cv x)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
  have p0011 :=
    @gSyl
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (synCtc (.cv x)) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0001 p0010
  have p0012 :=
    @gFveq2 (synCtc (.cv x))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCwppconcrete6fn)
  have p0013 :=
    @gSyl
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (synCtc (.cv x)) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (.classEq (synCfv (synCwppconcrete6fn) (synCtc (.cv x))) (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))))
      p0011 p0012
  have p0014 :=
    @gEqcomd
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (.cv x)))
      (synCfv (synCwppconcrete6fn) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0013
  have p0015 :=
    @gN3eqtrd
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
      (synCtc (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synCfv (synCwppconcrete6fn) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (.cv x))) p0005 p0008 p0014
  have p0016 :=
    @gExlimiv
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
        (synCfv (synCwppconcrete6fn) (synCtc (.cv x))))
      z dv_cache_0002 p0015
  have p0017 :=
    @gSyl (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (synWex z (.classEq (.cv x)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
        (synCfv (synCwppconcrete6fn) (synCtc (.cv x))))
      p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepexndv`. -/
@[expose]
noncomputable def gWppstopstepexndv (C : Class) (F : Class)
    (hyp_wppstopstepexndv_1 : Nominal.NPrf (.classMem F (synCfuns))) :
    Nominal.NPrf (.classMem (synCwppstopstep F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0001 := @gElex F (synCfuns)
  have p0002 := Nominal.mp hyp_wppstopstepexndv_1 p0001
  have p0003 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0006 := @gDmex F p0002
  have p0007 := @gVvex
  have p0008 := @gHwcardsexg (synCvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gLecex
  have p0011 := @gCnvex (synClec) p0010
  have p0012 := @gSnex C
  have p0013 := @gImaex (synCcnv (synClec)) (synCsn C) p0011 p0012
  have p0014 :=
    @gInex (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)) p0009
      p0013
  have p0015 :=
    @gInex (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      p0006 p0014
  have p0016 :=
    @gEqeltri (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCvv) p0003 p0015
  have p0017 := @gResex F (synCwppstopact F C) p0002 p0016
  have p0018 := @gIdex
  have p0036 := @gDifex (synChwcards (synCvv)) (synCwppstopact F C) p0009 p0016
  have p0037 :=
    @gResex (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) p0018
      p0036
  have p0038 :=
    @gUnex (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) p0017
      p0037
  have p0039 :=
    @gEqeltri (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      (synCvv) p0000 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepmapndv`. -/
@[expose]
noncomputable def gWppstopstepmapndv (C : Class) (F : Class)
    (hyp_wppstopstepmapndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepmapndv_2 : Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWf (synCwppstopstep F C) (synChwcards (synCvv)) (synChwcards (synCvv))) :=
  by
  have p0000 := @gElfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepmapndv_1 p0000
  have p0002 := @gFunfn F
  have p0003 := @gMpbi (synWfun F) (synWfn F (synCdm F)) p0001 p0002
  have p0004 := @gDffn3 (synCdm F) F
  have p0005 :=
    @gMpbi (synWfn F (synCdm F)) (synWf F (synCdm F) (synCrn F)) p0003 p0004
  have p0006 :=
    @gPm32i (synWf F (synCdm F) (synCrn F))
      (synWss (synCrn F) (synChwcards (synCvv))) p0005 hyp_wppstopstepmapndv_2
  have p0007 := @gFss (synCdm F) (synCrn F) (synChwcards (synCvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gInss1 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0010 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0011 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCdm F) p0010
  have p0012 :=
    @gMpbir (synWss (synCwppstopact F C) (synCdm F))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synCdm F))
      p0009 p0011
  have p0013 :=
    @gPm32i (synWf F (synCdm F) (synChwcards (synCvv)))
      (synWss (synCwppstopact F C) (synCdm F)) p0008 p0012
  have p0014 := @gFssres (synCdm F) (synChwcards (synCvv)) (synCwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gF1oi (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
  have p0017 :=
    @gF1of (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gDifss (synChwcards (synCvv)) (synCwppstopact F C)
  have p0020 :=
    @gPm32i
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synWss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synChwcards (synCvv)))
      p0018 p0019
  have p0021 :=
    @gFss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gPm32i
      (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C) (synChwcards (synCvv)))
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv)))
      p0015 p0022
  have p0024 := @gDisjdif (synCwppstopact F C) (synChwcards (synCvv))
  have p0025 :=
    @gPm32i
      (synWa (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C)
          (synChwcards (synCvv))) (synWf
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))))
      (.classEq (synCin (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synC0))
      p0023 p0024
  have p0026 :=
    @gFun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0029 :=
    @gFeq1i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synCun (synChwcards (synCvv)) (synChwcards (synCvv))) (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0028
  have p0030 :=
    @gMpbir
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0027 p0029
  have p0031 :=
    @gInss2 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0032 :=
    @gInss1 (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))
  have p0033 :=
    @gSstri
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synChwcards (synCvv)) p0031 p0032
  have p0035 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synChwcards (synCvv)) p0010
  have p0036 :=
    @gMpbir (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synChwcards (synCvv)))
      p0033 p0035
  have p0037 := @gUndif (synCwppstopact F C) (synChwcards (synCvv))
  have p0038 :=
    @gMpbi (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (.classEq (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synChwcards (synCvv)))
      p0036 p0037
  have p0039 :=
    @gFeq2i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synChwcards (synCvv)) (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synCwppstopstep F C) p0038
  have p0040 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0030 p0039
  have p0041 := @gUnidm (synChwcards (synCvv))
  have p0042 :=
    @gFeq3 (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv)) (synChwcards (synCvv)))
      p0040 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepfunsndv`. -/
@[expose]
noncomputable def gWppstopstepfunsndv (C : Class) (F : Class)
    (hyp_wppstopstepfunsndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepfunsndv_2 : Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf (.classMem (synCwppstopstep F C) (synCfuns)) :=
  by
  have p0000 := @gElfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepfunsndv_1 p0000
  have p0002 := @gFunfn F
  have p0003 := @gMpbi (synWfun F) (synWfn F (synCdm F)) p0001 p0002
  have p0004 := @gDffn3 (synCdm F) F
  have p0005 :=
    @gMpbi (synWfn F (synCdm F)) (synWf F (synCdm F) (synCrn F)) p0003 p0004
  have p0006 :=
    @gPm32i (synWf F (synCdm F) (synCrn F))
      (synWss (synCrn F) (synChwcards (synCvv))) p0005 hyp_wppstopstepfunsndv_2
  have p0007 := @gFss (synCdm F) (synCrn F) (synChwcards (synCvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gInss1 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0010 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0011 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCdm F) p0010
  have p0012 :=
    @gMpbir (synWss (synCwppstopact F C) (synCdm F))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synCdm F))
      p0009 p0011
  have p0013 :=
    @gPm32i (synWf F (synCdm F) (synChwcards (synCvv)))
      (synWss (synCwppstopact F C) (synCdm F)) p0008 p0012
  have p0014 := @gFssres (synCdm F) (synChwcards (synCvv)) (synCwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gF1oi (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
  have p0017 :=
    @gF1of (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gDifss (synChwcards (synCvv)) (synCwppstopact F C)
  have p0020 :=
    @gPm32i
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synWss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synChwcards (synCvv)))
      p0018 p0019
  have p0021 :=
    @gFss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gPm32i
      (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C) (synChwcards (synCvv)))
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv)))
      p0015 p0022
  have p0024 := @gDisjdif (synCwppstopact F C) (synChwcards (synCvv))
  have p0025 :=
    @gPm32i
      (synWa (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C)
          (synChwcards (synCvv))) (synWf
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))))
      (.classEq (synCin (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synC0))
      p0023 p0024
  have p0026 :=
    @gFun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0029 :=
    @gFeq1i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synCun (synChwcards (synCvv)) (synChwcards (synCvv))) (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0028
  have p0030 :=
    @gMpbir
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0027 p0029
  have p0031 :=
    @gInss2 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0032 :=
    @gInss1 (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))
  have p0033 :=
    @gSstri
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synChwcards (synCvv)) p0031 p0032
  have p0035 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synChwcards (synCvv)) p0010
  have p0036 :=
    @gMpbir (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synChwcards (synCvv)))
      p0033 p0035
  have p0037 := @gUndif (synCwppstopact F C) (synChwcards (synCvv))
  have p0038 :=
    @gMpbi (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (.classEq (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synChwcards (synCvv)))
      p0036 p0037
  have p0039 :=
    @gFeq2i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synChwcards (synCvv)) (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synCwppstopstep F C) p0038
  have p0040 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0030 p0039
  have p0041 := @gUnidm (synChwcards (synCvv))
  have p0042 :=
    @gFeq3 (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv)) (synChwcards (synCvv)))
      p0040 p0043
  have p0045 :=
    @gFfun (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0046 := Nominal.mp p0044 p0045
  have p0047 := @gWppstopstepexndv C F hyp_wppstopstepfunsndv_1
  have p0048 := @gElfuns (synCwppstopstep F C) p0047
  have p0049 :=
    @gMpbir (.classMem (synCwppstopstep F C) (synCfuns))
      (synWfun (synCwppstopstep F C)) p0046 p0048
  exact p0049

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepdmndv`. -/
@[expose]
noncomputable def gWppstopstepdmndv (C : Class) (F : Class)
    (hyp_wppstopstepdmndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepdmndv_2 : Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf (.classEq (synCdm (synCwppstopstep F C)) (synChwcards (synCvv))) :=
  by
  have p0000 := @gElfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepdmndv_1 p0000
  have p0002 := @gFunfn F
  have p0003 := @gMpbi (synWfun F) (synWfn F (synCdm F)) p0001 p0002
  have p0004 := @gDffn3 (synCdm F) F
  have p0005 :=
    @gMpbi (synWfn F (synCdm F)) (synWf F (synCdm F) (synCrn F)) p0003 p0004
  have p0006 :=
    @gPm32i (synWf F (synCdm F) (synCrn F))
      (synWss (synCrn F) (synChwcards (synCvv))) p0005 hyp_wppstopstepdmndv_2
  have p0007 := @gFss (synCdm F) (synCrn F) (synChwcards (synCvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gInss1 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0010 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0011 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCdm F) p0010
  have p0012 :=
    @gMpbir (synWss (synCwppstopact F C) (synCdm F))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synCdm F))
      p0009 p0011
  have p0013 :=
    @gPm32i (synWf F (synCdm F) (synChwcards (synCvv)))
      (synWss (synCwppstopact F C) (synCdm F)) p0008 p0012
  have p0014 := @gFssres (synCdm F) (synChwcards (synCvv)) (synCwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gF1oi (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
  have p0017 :=
    @gF1of (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gDifss (synChwcards (synCvv)) (synCwppstopact F C)
  have p0020 :=
    @gPm32i
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synWss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synChwcards (synCvv)))
      p0018 p0019
  have p0021 :=
    @gFss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gPm32i
      (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C) (synChwcards (synCvv)))
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv)))
      p0015 p0022
  have p0024 := @gDisjdif (synCwppstopact F C) (synChwcards (synCvv))
  have p0025 :=
    @gPm32i
      (synWa (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C)
          (synChwcards (synCvv))) (synWf
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))))
      (.classEq (synCin (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synC0))
      p0023 p0024
  have p0026 :=
    @gFun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0029 :=
    @gFeq1i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synCun (synChwcards (synCvv)) (synChwcards (synCvv))) (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0028
  have p0030 :=
    @gMpbir
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0027 p0029
  have p0031 :=
    @gInss2 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0032 :=
    @gInss1 (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))
  have p0033 :=
    @gSstri
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synChwcards (synCvv)) p0031 p0032
  have p0035 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synChwcards (synCvv)) p0010
  have p0036 :=
    @gMpbir (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synChwcards (synCvv)))
      p0033 p0035
  have p0037 := @gUndif (synCwppstopact F C) (synChwcards (synCvv))
  have p0038 :=
    @gMpbi (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (.classEq (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synChwcards (synCvv)))
      p0036 p0037
  have p0039 :=
    @gFeq2i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synChwcards (synCvv)) (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synCwppstopstep F C) p0038
  have p0040 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0030 p0039
  have p0041 := @gUnidm (synChwcards (synCvv))
  have p0042 :=
    @gFeq3 (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv)) (synChwcards (synCvv)))
      p0040 p0043
  have p0045 :=
    @gFdm (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0046 := Nominal.mp p0044 p0045
  exact p0046

/-- Checked nominal proof certificate identified upstream as `g_wppstopsteprndmndv`. -/
@[expose]
noncomputable def gWppstopsteprndmndv (C : Class) (F : Class)
    (hyp_wppstopstepdmndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepdmndv_2 : Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))) :=
  by
  have p0000 := @gElfunsi F
  have p0001 := Nominal.mp hyp_wppstopstepdmndv_1 p0000
  have p0002 := @gFunfn F
  have p0003 := @gMpbi (synWfun F) (synWfn F (synCdm F)) p0001 p0002
  have p0004 := @gDffn3 (synCdm F) F
  have p0005 :=
    @gMpbi (synWfn F (synCdm F)) (synWf F (synCdm F) (synCrn F)) p0003 p0004
  have p0006 :=
    @gPm32i (synWf F (synCdm F) (synCrn F))
      (synWss (synCrn F) (synChwcards (synCvv))) p0005 hyp_wppstopstepdmndv_2
  have p0007 := @gFss (synCdm F) (synCrn F) (synChwcards (synCvv)) F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gInss1 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0010 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0011 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCdm F) p0010
  have p0012 :=
    @gMpbir (synWss (synCwppstopact F C) (synCdm F))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synCdm F))
      p0009 p0011
  have p0013 :=
    @gPm32i (synWf F (synCdm F) (synChwcards (synCvv)))
      (synWss (synCwppstopact F C) (synCdm F)) p0008 p0012
  have p0014 := @gFssres (synCdm F) (synChwcards (synCvv)) (synCwppstopact F C) F
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gF1oi (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
  have p0017 :=
    @gF1of (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 := @gDifss (synChwcards (synCvv)) (synCwppstopact F C)
  have p0020 :=
    @gPm32i
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synWss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
        (synChwcards (synCvv)))
      p0018 p0019
  have p0021 :=
    @gFss (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gPm32i
      (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C) (synChwcards (synCvv)))
      (synWf (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv)))
      p0015 p0022
  have p0024 := @gDisjdif (synCwppstopact F C) (synChwcards (synCvv))
  have p0025 :=
    @gPm32i
      (synWa (synWf (synCres F (synCwppstopact F C)) (synCwppstopact F C)
          (synChwcards (synCvv))) (synWf
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)) (synChwcards (synCvv))))
      (.classEq (synCin (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synC0))
      p0023 p0024
  have p0026 :=
    @gFun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0029 :=
    @gFeq1i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synCun (synChwcards (synCvv)) (synChwcards (synCvv))) (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0028
  have p0030 :=
    @gMpbir
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0027 p0029
  have p0031 :=
    @gInss2 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0032 :=
    @gInss1 (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))
  have p0033 :=
    @gSstri
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synChwcards (synCvv)) p0031 p0032
  have p0035 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synChwcards (synCvv)) p0010
  have p0036 :=
    @gMpbir (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synChwcards (synCvv)))
      p0033 p0035
  have p0037 := @gUndif (synCwppstopact F C) (synChwcards (synCvv))
  have p0038 :=
    @gMpbi (synWss (synCwppstopact F C) (synChwcards (synCvv)))
      (.classEq (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) (synChwcards (synCvv)))
      p0036 p0037
  have p0039 :=
    @gFeq2i
      (synCun (synCwppstopact F C) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synChwcards (synCvv)) (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synCwppstopstep F C) p0038
  have p0040 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synCun (synCwppstopact F C)
          (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      p0030 p0039
  have p0041 := @gUnidm (synChwcards (synCvv))
  have p0042 :=
    @gFeq3 (synCun (synChwcards (synCvv)) (synChwcards (synCvv)))
      (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @gMpbi
      (synWf (synCwppstopstep F C) (synChwcards (synCvv))
        (synCun (synChwcards (synCvv)) (synChwcards (synCvv))))
      (synWf (synCwppstopstep F C) (synChwcards (synCvv)) (synChwcards (synCvv)))
      p0040 p0043
  have p0045 :=
    @gFrn (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0046 := Nominal.mp p0044 p0045
  have p0047 := @gWppstopstepdmndv C F hyp_wppstopstepdmndv_1 hyp_wppstopstepdmndv_2
  have p0048 := @gEqcomi (synCdm (synCwppstopstep F C)) (synChwcards (synCvv)) p0047
  have p0049 :=
    @gSseq2i (synChwcards (synCvv)) (synCdm (synCwppstopstep F C))
      (synCrn (synCwppstopstep F C)) p0048
  have p0050 :=
    @gMpbi (synWss (synCrn (synCwppstopstep F C)) (synChwcards (synCvv)))
      (synWss (synCrn (synCwppstopstep F C)) (synCdm (synCwppstopstep F C))) p0046
      p0049
  exact p0050

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepfvactclndv`. -/
@[expose]
noncomputable def gWppstopstepfvactclndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvactclndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepfvactclndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (.classMem A (synCwppstopact F C))
        (.classEq (synCfv (synCwppstopstep F C) A) (synCfv F A))) :=
  by
  have p0000 :=
    @gInss1 (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0001 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0002 :=
    @gSseq1i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synCdm F) p0001
  have p0003 :=
    @gMpbir (synWss (synCwppstopact F C) (synCdm F))
      (synWss (synCin (synCdm F)
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (synCdm F))
      p0000 p0002
  have p0004 := @gSseli (synCwppstopact F C) (synCdm F) A p0003
  have p0005 := @gElfunsi F
  have p0006 := Nominal.mp hyp_wppstopstepfvactclndv_1 p0005
  have p0007 := @gFunfvbrb A F
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gBiimpi (.classMem A (synCdm F)) (synWbr A F (synCfv F A)) p0008
  have p0010 :=
    @gSyl (.classMem A (synCwppstopact F C)) (.classMem A (synCdm F))
      (synWbr A F (synCfv F A)) p0004 p0009
  have p0011 := @gId (.classMem A (synCwppstopact F C))
  have p0012 :=
    @gJca (.classMem A (synCwppstopact F C)) (synWbr A F (synCfv F A))
      (.classMem A (synCwppstopact F C)) p0010 p0011
  have p0013 := @gBrres A (synCfv F A) F (synCwppstopact F C)
  have p0014 :=
    @gBiimpri (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A))
      (synWa (synWbr A F (synCfv F A)) (.classMem A (synCwppstopact F C))) p0013
  have p0015 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWa (synWbr A F (synCfv F A)) (.classMem A (synCwppstopact F C)))
      (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A)) p0012 p0014
  have p0016 :=
    @gOrc (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A))
      (synWbr A (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
        (synCfv F A))
  have p0017 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A))
      (synWo (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A)) (synWbr A
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCfv F A)))
      p0015 p0016
  have p0018 :=
    @gBrun A (synCfv F A) (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0019 :=
    @gBiimpri
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCfv F A))
      (synWo (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A)) (synWbr A
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCfv F A)))
      p0018
  have p0020 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWo (synWbr A (synCres F (synCwppstopact F C)) (synCfv F A)) (synWbr A
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
          (synCfv F A)))
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCfv F A))
      p0017 p0019
  have p0021 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0022 :=
    @gBreqi A (synCfv F A) (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0021
  have p0023 :=
    @gBiimpri (synWbr A (synCwppstopstep F C) (synCfv F A))
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCfv F A))
      p0022
  have p0024 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
        (synCfv F A))
      (synWbr A (synCwppstopstep F C) (synCfv F A)) p0020 p0023
  have p0025 :=
    @gWppstopstepmapndv C F hyp_wppstopstepfvactclndv_1 hyp_wppstopstepfvactclndv_2
  have p0026 :=
    @gFfun (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @gFunbrfv A (synCfv F A) (synCwppstopstep F C)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWbr A (synCwppstopstep F C) (synCfv F A))
      (.classEq (synCfv (synCwppstopstep F C) A) (synCfv F A)) p0024 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepfvidleclndv`. -/
@[expose]
noncomputable def gWppstopstepfvidleclndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvidleclndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepfvidleclndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synChwcards (synCvv)))
          (.neg (.classMem A (synCwppstopact F C))))
        (.classEq (synCfv (synCwppstopstep F C) A) A)) :=
  by
  have p0000 := @gEldif A (synChwcards (synCvv)) (synCwppstopact F C)
  have p0001 :=
    @gBiimpri (.classMem A (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      p0000
  have p0002 := @gIdidg A (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
  have p0003 :=
    @gSyl
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (.classMem A (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
      (synWbr A (synCid) A) p0001 p0002
  have p0006 :=
    @gJca
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (synWbr A (synCid) A)
      (.classMem A (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) p0003 p0001
  have p0007 :=
    @gBrres A A (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))
  have p0008 :=
    @gBiimpri
      (synWbr A
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A)
      (synWa (synWbr A (synCid) A)
        (.classMem A (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0007
  have p0009 :=
    @gSyl
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (synWa (synWbr A (synCid) A)
        (.classMem A (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      (synWbr A
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A)
      p0006 p0008
  have p0010 :=
    @gOlc
      (synWbr A
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A)
      (synWbr A (synCres F (synCwppstopact F C)) A)
  have p0011 :=
    @gSyl
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (synWbr A
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A)
      (synWo (synWbr A (synCres F (synCwppstopact F C)) A) (synWbr A
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A))
      p0009 p0010
  have p0012 :=
    @gBrun A A (synCres F (synCwppstopact F C))
      (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))
  have p0013 :=
    @gBiimpri
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))) A)
      (synWo (synWbr A (synCres F (synCwppstopact F C)) A) (synWbr A
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A))
      p0012
  have p0014 :=
    @gSyl
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (synWo (synWbr A (synCres F (synCwppstopact F C)) A) (synWbr A
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))) A))
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))) A)
      p0011 p0013
  have p0015 := (Nominal.classEqRefl (synCwppstopstep F C))
  have p0016 :=
    @gBreqi A A (synCwppstopstep F C)
      (synCun (synCres F (synCwppstopact F C))
        (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C))))
      p0015
  have p0017 :=
    @gBiimpri (synWbr A (synCwppstopstep F C) A)
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))) A)
      p0016
  have p0018 :=
    @gSyl
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (synWbr A (synCun (synCres F (synCwppstopact F C))
          (synCres (synCid) (synCdif (synChwcards (synCvv)) (synCwppstopact F C)))) A)
      (synWbr A (synCwppstopstep F C) A) p0014 p0017
  have p0019 :=
    @gWppstopstepmapndv C F hyp_wppstopstepfvidleclndv_1 hyp_wppstopstepfvidleclndv_2
  have p0020 :=
    @gFfun (synChwcards (synCvv)) (synChwcards (synCvv)) (synCwppstopstep F C)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gFunbrfv A A (synCwppstopstep F C)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 :=
    @gSyl
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (synWbr A (synCwppstopstep F C) A) (.classEq (synCfv (synCwppstopstep F C) A) A)
      p0018 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_wppstopactlecbindv`. -/
@[expose]
noncomputable def gWppstopactlecbindv (A : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synChwcards (synCvv)))
          (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
        (synWb (.classMem A (synCwppstopact F C)) (synWbr A (synClec) C))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppstopact F C))
  have p0001 :=
    @gEleq2i (synCwppstopact F C)
      (synCin (synCdm F)
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      A p0000
  have p0002 :=
    @gElin A (synCdm F)
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
  have p0003 :=
    @gElin A (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))
  have p0004 := @gElimasn (synCcnv (synClec)) C A
  have p0005 := (Nominal.biimpRefl (synWbr C (synCcnv (synClec)) A))
  have p0006 :=
    @gBicomi (synWbr C (synCcnv (synClec)) A)
      (.classMem (synCop C A) (synCcnv (synClec))) p0005
  have p0007 :=
    @gBitri (.classMem A (synCima (synCcnv (synClec)) (synCsn C)))
      (.classMem (synCop C A) (synCcnv (synClec))) (synWbr C (synCcnv (synClec)) A)
      p0004 p0006
  have p0008 := @gBrcnv C A (synClec)
  have p0009 :=
    @gBitri (.classMem A (synCima (synCcnv (synClec)) (synCsn C)))
      (synWbr C (synCcnv (synClec)) A) (synWbr A (synClec) C) p0007 p0008
  have p0010 :=
    @gAnbi2i (.classMem A (synCima (synCcnv (synClec)) (synCsn C)))
      (synWbr A (synClec) C) (.classMem A (synChwcards (synCvv))) p0009
  have p0011 :=
    @gBitri
      (.classMem A
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synWa (.classMem A (synChwcards (synCvv)))
        (.classMem A (synCima (synCcnv (synClec)) (synCsn C))))
      (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)) p0003 p0010
  have p0012 :=
    @gAnbi2i
      (.classMem A
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C))
      (.classMem A (synCdm F)) p0011
  have p0013 :=
    @gBitri
      (.classMem A (synCin (synCdm F) (synCin (synChwcards (synCvv))
            (synCima (synCcnv (synClec)) (synCsn C)))))
      (synWa (.classMem A (synCdm F)) (.classMem A (synCin (synChwcards (synCvv))
            (synCima (synCcnv (synClec)) (synCsn C)))))
      (synWa (.classMem A (synCdm F))
        (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)))
      p0002 p0012
  have p0014 :=
    @gBitri (.classMem A (synCwppstopact F C))
      (.classMem A (synCin (synCdm F) (synCin (synChwcards (synCvv))
            (synCima (synCcnv (synClec)) (synCsn C)))))
      (synWa (.classMem A (synCdm F))
        (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)))
      p0001 p0013
  have p0015 :=
    @gBiimpi (.classMem A (synCwppstopact F C))
      (synWa (.classMem A (synCdm F))
        (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)))
      p0014
  have p0016 :=
    @gSimpr (.classMem A (synCdm F))
      (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C))
  have p0017 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWa (.classMem A (synCdm F))
        (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)))
      (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)) p0015 p0016
  have p0018 := @gSimpr (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)
  have p0019 :=
    @gSyl (.classMem A (synCwppstopact F C))
      (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C))
      (synWbr A (synClec) C) p0017 p0018
  have p0020 :=
    @gA1i (.imp (.classMem A (synCwppstopact F C)) (synWbr A (synClec) C))
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      p0019
  have p0021 :=
    @gSimpr (.classMem A (synChwcards (synCvv)))
      (.imp (synWbr A (synClec) C) (.classMem A (synCdm F)))
  have p0022 :=
    @gSimpl (.classMem A (synChwcards (synCvv)))
      (.imp (synWbr A (synClec) C) (.classMem A (synCdm F)))
  have p0023 :=
    @gA1d
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C) p0022
  have p0024 := @gId (synWbr A (synClec) C)
  have p0025 :=
    @gA1i (.imp (synWbr A (synClec) C) (synWbr A (synClec) C))
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      p0024
  have p0026 :=
    @gJcad
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (synWbr A (synClec) C) (.classMem A (synChwcards (synCvv)))
      (synWbr A (synClec) C) p0023 p0025
  have p0027 :=
    @gJcad
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (synWbr A (synClec) C) (.classMem A (synCdm F))
      (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)) p0021 p0026
  have p0043 :=
    @gBiimpri (.classMem A (synCwppstopact F C))
      (synWa (.classMem A (synCdm F))
        (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)))
      p0014
  have p0044 :=
    @gSyl6
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (synWbr A (synClec) C)
      (synWa (.classMem A (synCdm F))
        (synWa (.classMem A (synChwcards (synCvv))) (synWbr A (synClec) C)))
      (.classMem A (synCwppstopact F C)) p0027 p0043
  have p0045 :=
    @gImpbid
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.classMem A (synCwppstopact F C)) (synWbr A (synClec) C) p0020 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepfvlecdndv`. -/
@[expose]
noncomputable def gWppstopstepfvlecdndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvlecdndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepfvlecdndv_2 : Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synChwcards (synCvv)))
          (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
        (.imp (synWbr A (synClec) C)
          (.classEq (synCfv (synCwppstopstep F C) A) (synCfv F A)))) :=
  by
  have p0000 := @gWppstopactlecbindv A C F
  have p0001 :=
    @gBiimprd
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.classMem A (synCwppstopact F C)) (synWbr A (synClec) C) p0000
  have p0002 :=
    @gWppstopstepfvactclndv A C F hyp_wppstopstepfvlecdndv_1 hyp_wppstopstepfvlecdndv_2
  have p0003 :=
    @gSyl6
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (synWbr A (synClec) C) (.classMem A (synCwppstopact F C))
      (.classEq (synCfv (synCwppstopstep F C) A) (synCfv F A)) p0001 p0002
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

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepfvnlecdndv`. -/
@[expose]
noncomputable def gWppstopstepfvnlecdndv (A : Class) (C : Class) (F : Class)
    (hyp_wppstopstepfvnlecdndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepfvnlecdndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synChwcards (synCvv)))
          (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
        (.imp (.neg (synWbr A (synClec) C))
          (.classEq (synCfv (synCwppstopstep F C) A) A))) :=
  by
  have p0000 :=
    @gSimpl (.classMem A (synChwcards (synCvv)))
      (.imp (synWbr A (synClec) C) (.classMem A (synCdm F)))
  have p0001 :=
    @gA1d
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.classMem A (synChwcards (synCvv))) (.neg (synWbr A (synClec) C)) p0000
  have p0002 := @gWppstopactlecbindv A C F
  have p0003 :=
    @gBiimpd
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.classMem A (synCwppstopact F C)) (synWbr A (synClec) C) p0002
  have p0004 :=
    @gCon3d
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.classMem A (synCwppstopact F C)) (synWbr A (synClec) C) p0003
  have p0005 :=
    @gJcad
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.neg (synWbr A (synClec) C)) (.classMem A (synChwcards (synCvv)))
      (.neg (.classMem A (synCwppstopact F C))) p0001 p0004
  have p0006 :=
    @gWppstopstepfvidleclndv A C F hyp_wppstopstepfvnlecdndv_1
      hyp_wppstopstepfvnlecdndv_2
  have p0007 :=
    @gSyl6
      (synWa (.classMem A (synChwcards (synCvv)))
        (.imp (synWbr A (synClec) C) (.classMem A (synCdm F))))
      (.neg (synWbr A (synClec) C))
      (synWa (.classMem A (synChwcards (synCvv))) (.neg (.classMem A (synCwppstopact F C))))
      (.classEq (synCfv (synCwppstopstep F C) A) A) p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppstopsteptchomdndv`. -/
@[expose]
noncomputable def gWppstopsteptchomdndv (x : Var) (C : Class) (F : Class)
    (hyp_wppstopsteptchomdndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopsteptchomdndv_2 : Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv))))
    (hyp_wppstopsteptchomdndv_3 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
          (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))))) :=
  by
  have p0000 :=
    @gSimpr
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C)
  have p0001 :=
    @gSimpl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C)
  have p0002 :=
    @gN3simpa (.classMem (.cv x) (synChwcards (synCvv)))
      (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
          (.classMem (synCtc (.cv x)) (synCdm F))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x)))))
  have p0003 :=
    @gSimpl (.classMem (.cv x) (synChwcards (synCvv)))
      (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
          (.classMem (synCtc (.cv x)) (synCdm F))))
  have p0004 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F)))))
      (.classMem (.cv x) (synChwcards (synCvv))) p0002 p0003
  have p0006 :=
    @gSimpr (.classMem (.cv x) (synChwcards (synCvv)))
      (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
          (.classMem (synCtc (.cv x)) (synCdm F))))
  have p0007 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F)))))
      (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
          (.classMem (synCtc (.cv x)) (synCdm F))))
      p0002 p0006
  have p0008 :=
    @gSimpl (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))
  have p0009 :=
    @gSyl6
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C)
      (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F)))
      (.classMem (.cv x) (synCdm F)) p0007 p0008
  have p0010 :=
    @gJca
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.classMem (.cv x) (synChwcards (synCvv)))
      (.imp (synWbr (.cv x) (synClec) C) (.classMem (.cv x) (synCdm F))) p0004 p0009
  have p0011 :=
    @gWppstopstepfvlecdndv (.cv x) C F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0012 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (.cv x) (synChwcards (synCvv)))
        (.imp (synWbr (.cv x) (synClec) C) (.classMem (.cv x) (synCdm F))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (synCfv F (.cv x))))
      p0010 p0011
  have p0013 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (synCfv F (.cv x))))
      p0001 p0012
  have p0014 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synWbr (.cv x) (synClec) C)
      (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (synCfv F (.cv x))) p0000 p0013
  have p0015 := @gTceq (synCfv (synCwppstopstep F C) (.cv x)) (synCfv F (.cv x))
  have p0016 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (synCfv F (.cv x)))
      (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
        (synCtc (synCfv F (.cv x))))
      p0014 p0015
  have p0019 :=
    @gN3simpc (.classMem (.cv x) (synChwcards (synCvv)))
      (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
          (.classMem (synCtc (.cv x)) (synCdm F))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x)))))
  have p0020 :=
    @gSimpr
      (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
          (.classMem (synCtc (.cv x)) (synCdm F))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x)))))
  have p0021 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
            (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x)))))
      p0019 p0020
  have p0022 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (synWbr (.cv x) (synClec) C)
        (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x)))))
      p0001 p0021
  have p0023 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synWbr (.cv x) (synClec) C)
      (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x)))) p0000 p0022
  have p0029 := @gHwcardssnc (synCvv)
  have p0030 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv x) p0029
  have p0031 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.classMem (.cv x) (synChwcards (synCvv))) (.classMem (.cv x) (synCncs)) p0004
      p0030
  have p0033 := @gSseli (synChwcards (synCvv)) (synCncs) C p0029
  have p0034 := Nominal.mp hyp_wppstopsteptchomdndv_3 p0033
  have p0035 :=
    @gA1i (.classMem C (synCncs))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      p0034
  have p0036 :=
    @gJca
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.classMem (.cv x) (synCncs)) (.classMem C (synCncs)) p0031 p0035
  have p0037 := @gTlecg (.cv x) C
  have p0038 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (.cv x) (synCncs)) (.classMem C (synCncs)))
      (synWb (synWbr (.cv x) (synClec) C) (synWbr (synCtc (.cv x)) (synClec) (synCtc C)))
      p0036 p0037
  have p0039 :=
    @gBiimpd
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C) (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
      p0038
  have p0040 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (synWbr (.cv x) (synClec) C) (synWbr (synCtc (.cv x)) (synClec) (synCtc C)))
      p0001 p0039
  have p0041 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synWbr (.cv x) (synClec) C) (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
      p0000 p0040
  have p0046 := @gHwcardstcclndv (.cv x)
  have p0047 := @gId (.classMem (synCtc (.cv x)) (synChwcards (synCvv)))
  have p0048 :=
    @gN3syl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.classMem (.cv x) (synChwcards (synCvv)))
      (.classMem (synCtc (.cv x)) (synChwcards (synCvv)))
      (.classMem (synCtc (.cv x)) (synChwcards (synCvv))) p0004 p0046 p0047
  have p0062 :=
    @gBiimprd
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C) (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
      p0038
  have p0066 :=
    @gSyld
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (synCtc (.cv x)) (synClec) (synCtc C)) (synWbr (.cv x) (synClec) C)
      (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F)))
      p0062 p0007
  have p0067 :=
    @gSimpr (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))
  have p0068 :=
    @gSyl6
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
      (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F)))
      (.classMem (synCtc (.cv x)) (synCdm F)) p0066 p0067
  have p0069 :=
    @gJca
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.classMem (synCtc (.cv x)) (synChwcards (synCvv)))
      (.imp (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
        (.classMem (synCtc (.cv x)) (synCdm F)))
      p0048 p0068
  have p0070 :=
    @gWppstopstepfvlecdndv (synCtc (.cv x)) (synCtc C) F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0071 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (synCtc (.cv x)) (synChwcards (synCvv)))
        (.imp (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
          (.classMem (synCtc (.cv x)) (synCdm F))))
      (.imp (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
        (.classEq (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))
          (synCfv F (synCtc (.cv x)))))
      p0069 p0070
  have p0072 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
        (.classEq (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))
          (synCfv F (synCtc (.cv x)))))
      p0001 p0071
  have p0073 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
      (.classEq (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))
        (synCfv F (synCtc (.cv x))))
      p0041 p0072
  have p0074 :=
    @gEqcomd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))
      (synCfv F (synCtc (.cv x))) p0073
  have p0075 :=
    @gN3eqtrd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (synWbr (.cv x) (synClec) C))
      (synCtc (synCfv (synCwppstopstep F C) (.cv x))) (synCtc (synCfv F (.cv x)))
      (synCfv F (synCtc (.cv x)))
      (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))) p0016 p0023 p0074
  have p0076 :=
    @gEx
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C)
      (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
        (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))))
      p0075
  have p0077 :=
    @gSimpr
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.neg (synWbr (.cv x) (synClec) C))
  have p0078 :=
    @gSimpl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.neg (synWbr (.cv x) (synClec) C))
  have p0088 :=
    @gWppstopstepfvnlecdndv (.cv x) C F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0089 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (.cv x) (synChwcards (synCvv)))
        (.imp (synWbr (.cv x) (synClec) C) (.classMem (.cv x) (synCdm F))))
      (.imp (.neg (synWbr (.cv x) (synClec) C))
        (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (.cv x)))
      p0010 p0088
  have p0090 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (.neg (synWbr (.cv x) (synClec) C))
        (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (.cv x)))
      p0078 p0089
  have p0091 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (.neg (synWbr (.cv x) (synClec) C))
      (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (.cv x)) p0077 p0090
  have p0092 := @gTceq (synCfv (synCwppstopstep F C) (.cv x)) (.cv x)
  have p0093 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (.classEq (synCfv (synCwppstopstep F C) (.cv x)) (.cv x))
      (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x))) (synCtc (.cv x)))
      p0091 p0092
  have p0109 :=
    @gNotbid
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C) (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
      p0038
  have p0110 :=
    @gBiimpd
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.neg (synWbr (.cv x) (synClec) C))
      (.neg (synWbr (synCtc (.cv x)) (synClec) (synCtc C))) p0109
  have p0111 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (.neg (synWbr (.cv x) (synClec) C))
        (.neg (synWbr (synCtc (.cv x)) (synClec) (synCtc C))))
      p0078 p0110
  have p0112 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (.neg (synWbr (.cv x) (synClec) C))
      (.neg (synWbr (synCtc (.cv x)) (synClec) (synCtc C))) p0077 p0111
  have p0141 :=
    @gWppstopstepfvnlecdndv (synCtc (.cv x)) (synCtc C) F hyp_wppstopsteptchomdndv_1
      hyp_wppstopsteptchomdndv_2
  have p0142 :=
    @gSyl
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWa (.classMem (synCtc (.cv x)) (synChwcards (synCvv)))
        (.imp (synWbr (synCtc (.cv x)) (synClec) (synCtc C))
          (.classMem (synCtc (.cv x)) (synCdm F))))
      (.imp (.neg (synWbr (synCtc (.cv x)) (synClec) (synCtc C)))
        (.classEq (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))
          (synCtc (.cv x))))
      p0069 p0141
  have p0143 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.imp (.neg (synWbr (synCtc (.cv x)) (synClec) (synCtc C)))
        (.classEq (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x)))
          (synCtc (.cv x))))
      p0078 p0142
  have p0144 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (.neg (synWbr (synCtc (.cv x)) (synClec) (synCtc C)))
      (.classEq (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))) (synCtc (.cv x)))
      p0112 p0143
  have p0145 :=
    @gEqcomd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))) (synCtc (.cv x)) p0144
  have p0146 :=
    @gEqtrd
      (synWa (synW3a (.classMem (.cv x) (synChwcards (synCvv)))
          (.imp (synWbr (.cv x) (synClec) C) (synWa (.classMem (.cv x) (synCdm F))
              (.classMem (synCtc (.cv x)) (synCdm F)))) (.imp (synWbr (.cv x) (synClec) C)
            (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
        (.neg (synWbr (.cv x) (synClec) C)))
      (synCtc (synCfv (synCwppstopstep F C) (.cv x))) (synCtc (.cv x))
      (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))) p0093 p0145
  have p0147 :=
    @gEx
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (.neg (synWbr (.cv x) (synClec) C))
      (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
        (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))))
      p0146
  have p0148 :=
    @gPm261d
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec) C)
          (synWa (.classMem (.cv x) (synCdm F)) (.classMem (synCtc (.cv x)) (synCdm F))))
        (.imp (synWbr (.cv x) (synClec) C)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv F (synCtc (.cv x))))))
      (synWbr (.cv x) (synClec) C)
      (.classEq (synCtc (synCfv (synCwppstopstep F C) (.cv x)))
        (synCfv (synCwppstopstep F (synCtc C)) (synCtc (.cv x))))
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

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6stoppedtchomndv`. -/
@[expose]
noncomputable def gWppconcrete6stoppedtchomndv (x : Var)
    (hyp_wppconcrete6stoppedtchomndv_1 :
      Nominal.NPrf (synWss (synCrn (synCwppconcrete6fn)) (synChwcards (synCvv))))
    (hyp_wppconcrete6stoppedtchomndv_2 : Nominal.NPrf (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWral x (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (.classEq (synCtc (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv x)))
          (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synCtc (.cv x))))) :=
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
  have dv_cache_0002 : p ∉ ((synChwcards (synCvv))).fv :=
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
      ((Wff.imp (synWbr (.cv x) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
            (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn)))))).fv :=
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
  have p0000 := @gWppconcrete6fnfunsndv
  have p0001 :=
    @gWppstopstepdmndv
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCwppconcrete6fn) p0000 hyp_wppconcrete6stoppedtchomndv_1
  have p0002 :=
    @gEleq2i
      (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synChwcards (synCvv)) (.cv x) p0001
  have p0003 :=
    @gBiimpi
      (.classMem (.cv x) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.classMem (.cv x) (synChwcards (synCvv))) p0002
  have p0004 := @gId (.classMem (.cv x) (synChwcards (synCvv)))
  have p0005 := @gWppconcrete6thresholdtclecndv
  have p0006 := @gWppconcrete6hncard1dmpaircovndv p p0005
  have p0007 :=
    @gA1i
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
            (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))))
      (.classMem (.cv x) (synChwcards (synCvv))) p0006
  have p0008 := @gId (.classEq (.cv p) (.cv x))
  have p0009 :=
    @gBreq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synClec) p0008
  have p0011 :=
    @gEleq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x) (synCdm (synCwppconcrete6fn))
      p0008
  have p0013 := @gTceq (.cv p) (.cv x)
  have p0014 :=
    @gSyl (.classEq (.cv p) (.cv x)) (.classEq (.cv p) (.cv x))
      (.classEq (synCtc (.cv p)) (synCtc (.cv x))) p0008 p0013
  have p0015 :=
    @gEleq1d (.classEq (.cv p) (.cv x)) (synCtc (.cv p)) (synCtc (.cv x))
      (synCdm (synCwppconcrete6fn)) p0014
  have p0016 :=
    @gAnbi12d (.classEq (.cv p) (.cv x))
      (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
      (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn)))
      (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn))) p0011 p0015
  have p0017 :=
    @gImbi12d (.classEq (.cv p) (.cv x))
      (synWbr (.cv p) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (.cv x) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
        (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))
      (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
        (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn))))
      p0009 p0016
  have p0018 :=
    @gRspcv
      (.imp (synWbr (.cv p) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
          (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn)))))
      (.imp (synWbr (.cv x) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
          (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn)))))
      p (.cv x) (synChwcards (synCvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0017
  have p0019 :=
    @gMpd (.classMem (.cv x) (synChwcards (synCvv)))
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synWa (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
            (.classMem (synCtc (.cv p)) (synCdm (synCwppconcrete6fn))))))
      (.imp (synWbr (.cv x) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
          (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn)))))
      p0007 p0018
  have p0035 :=
    @gSimpl (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn)))
  have p0036 :=
    @gSyl6 (.classMem (.cv x) (synChwcards (synCvv)))
      (synWbr (.cv x) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
        (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn))))
      (.classMem (.cv x) (synCdm (synCwppconcrete6fn))) p0019 p0035
  have p0037 := @gWppconcrete6tchomdmndv x
  have p0038 :=
    @gSyl6 (.classMem (.cv x) (synChwcards (synCvv)))
      (synWbr (.cv x) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
        (synCfv (synCwppconcrete6fn) (synCtc (.cv x))))
      p0036 p0037
  have p0039 :=
    @gN3jca (.classMem (.cv x) (synChwcards (synCvv)))
      (.classMem (.cv x) (synChwcards (synCvv)))
      (.imp (synWbr (.cv x) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
          (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn)))))
      (.imp (synWbr (.cv x) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
          (synCfv (synCwppconcrete6fn) (synCtc (.cv x)))))
      p0004 p0019 p0038
  have p0041 :=
    @gWppstopsteptchomdndv x
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCwppconcrete6fn) p0000 hyp_wppconcrete6stoppedtchomndv_1
      hyp_wppconcrete6stoppedtchomndv_2
  have p0042 :=
    @gSyl (.classMem (.cv x) (synChwcards (synCvv)))
      (synW3a (.classMem (.cv x) (synChwcards (synCvv))) (.imp (synWbr (.cv x) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synWa (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
            (.classMem (synCtc (.cv x)) (synCdm (synCwppconcrete6fn))))) (.imp
          (synWbr (.cv x) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.classEq (synCtc (synCfv (synCwppconcrete6fn) (.cv x)))
            (synCfv (synCwppconcrete6fn) (synCtc (.cv x))))))
      (.classEq (synCtc (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv x)))
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCtc (.cv x))))
      p0039 p0041
  have p0043 :=
    @gSyl
      (.classMem (.cv x) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.classMem (.cv x) (synChwcards (synCvv)))
      (.classEq (synCtc (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv x)))
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCtc (.cv x))))
      p0003 p0042
  have p0044 :=
    @gRgen
      (.classEq (synCtc (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv x)))
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCtc (.cv x))))
      x
      (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6rnhwcardsredndv`. -/
@[expose]
noncomputable def gWppconcrete6rnhwcardsredndv (u : Var)
    (hyp_wppconcrete6rnhwcardsredndv_1 : Nominal.NPrf (synWral u (synCvv)
          (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
            (synChwcards (synCvv))))) :
    Nominal.NPrf (synWss (synCrn (synCwppconcrete6fn)) (synChwcards (synCvv))) :=
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
  have dv_cache_0003 : u ∉ ((synCvv)).fv :=
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
      ((Wff.classMem (synChncard (synChnord (synCpw (synCpw (.cv z)))))
          (synChwcards (synCvv)))).fv :=
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
      ((Wff.classMem (synCfv (synCwppconcrete6fn) (.cv x)) (synChwcards (synCvv)))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCrn (synCwppcardt6fn))).fv :=
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
  have dv_cache_0007 : x ∉ ((synChwcards (synCvv))).fv :=
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
  have dv_cache_0008 : x ∉ ((synCwppconcrete6fn)).fv :=
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
  have p0000 := @gWppconcrete6fnfnndv
  have p0001 := @gWppconcrete6fndmndv
  have p0002 :=
    @gEleq2i (synCdm (synCwppconcrete6fn)) (synCrn (synCwppcardt6fn)) (.cv x) p0001
  have p0003 :=
    @gBiimpri (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classMem (.cv x) (synCrn (synCwppcardt6fn))) p0002
  have p0004 := @gWppconcrete6dmrepdndv x z dv_cache_0001
  have p0005 :=
    @gId
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
  have p0006 :=
    @gFveq2d
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.cv x)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (synCwppconcrete6fn) p0005
  have p0007 := @gVex z
  have p0008 := @gWppconcrete6fnvalndv (.cv z) p0007
  have p0009 :=
    @gA1i
      (.classEq (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
        (synChncard (synChnord (synCpw (synCpw (.cv z))))))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0008
  have p0010 :=
    @gEqtrd
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCfv (synCwppconcrete6fn) (.cv x))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synChncard (synChnord (synCpw (synCpw (.cv z))))) p0006 p0009
  have p0012 := @gId (.classEq (.cv u) (.cv z))
  have p0013 := @gPweqd (.classEq (.cv u) (.cv z)) (.cv u) (.cv z) p0012
  have p0014 :=
    @gPweqd (.classEq (.cv u) (.cv z)) (synCpw (.cv u)) (synCpw (.cv z)) p0013
  have p0015 := @gHnordeqdndv (synCpw (synCpw (.cv u))) (synCpw (synCpw (.cv z)))
  have p0016 :=
    @gSyl (.classEq (.cv u) (.cv z))
      (.classEq (synCpw (synCpw (.cv u))) (synCpw (synCpw (.cv z))))
      (.classEq (synChnord (synCpw (synCpw (.cv u))))
        (synChnord (synCpw (synCpw (.cv z)))))
      p0014 p0015
  have p0017 :=
    @gHncardeqdndv (synChnord (synCpw (synCpw (.cv u))))
      (synChnord (synCpw (synCpw (.cv z))))
  have p0018 :=
    @gSyl (.classEq (.cv u) (.cv z))
      (.classEq (synChnord (synCpw (synCpw (.cv u))))
        (synChnord (synCpw (synCpw (.cv z)))))
      (.classEq (synChncard (synChnord (synCpw (synCpw (.cv u)))))
        (synChncard (synChnord (synCpw (synCpw (.cv z))))))
      p0016 p0017
  have p0019 :=
    @gEleq1d (.classEq (.cv u) (.cv z))
      (synChncard (synChnord (synCpw (synCpw (.cv u)))))
      (synChncard (synChnord (synCpw (synCpw (.cv z))))) (synChwcards (synCvv))
      p0018
  have p0020 :=
    @gRspcv
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
        (synChwcards (synCvv)))
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv z)))))
        (synChwcards (synCvv)))
      u (.cv z) (synCvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0019
  have p0021 :=
    @gMpi (.classMem (.cv z) (synCvv))
      (synWral u (synCvv) (.classMem (synChncard (synChnord (synCpw (synCpw (.cv u)))))
          (synChwcards (synCvv))))
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv z)))))
        (synChwcards (synCvv)))
      hyp_wppconcrete6rnhwcardsredndv_1 p0020
  have p0022 := Nominal.mp p0007 p0021
  have p0023 :=
    @gA1i
      (.classMem (synChncard (synChnord (synCpw (synCpw (.cv z)))))
        (synChwcards (synCvv)))
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0022
  have p0024 :=
    @gEqeltrd
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCfv (synCwppconcrete6fn) (.cv x))
      (synChncard (synChnord (synCpw (synCpw (.cv z))))) (synChwcards (synCvv))
      p0010 p0023
  have p0025 :=
    @gExlimiv
      (.classEq (.cv x)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv x)) (synChwcards (synCvv))) z
      dv_cache_0005 p0024
  have p0026 :=
    @gSyl (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (synWex z (.classEq (.cv x)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv x)) (synChwcards (synCvv))) p0004
      p0025
  have p0027 :=
    @gSyl (.classMem (.cv x) (synCrn (synCwppcardt6fn)))
      (.classMem (.cv x) (synCdm (synCwppconcrete6fn)))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv x)) (synChwcards (synCvv))) p0003
      p0026
  have p0028 :=
    @gRgen (.classMem (synCfv (synCwppconcrete6fn) (.cv x)) (synChwcards (synCvv))) x
      (synCrn (synCwppcardt6fn)) p0027
  have p0029 :=
    @gPm32i (synWfn (synCwppconcrete6fn) (synCrn (synCwppcardt6fn)))
      (synWral x (synCrn (synCwppcardt6fn))
        (.classMem (synCfv (synCwppconcrete6fn) (.cv x)) (synChwcards (synCvv))))
      p0000 p0028
  have p0030 :=
    @gFnfvrnss x (synCrn (synCwppcardt6fn)) (synChwcards (synCvv))
      (synCwppconcrete6fn) dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0031 := Nominal.mp p0029 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_wppfreceqexndv`. -/
@[expose]
noncomputable def gWppfreceqexndv (F : Class) (G : Class) (I : Class)
    (hyp_wppfreceqexndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppfreceqexndv_2 : Nominal.NPrf (.classMem G (synCfuns))) :
    Nominal.NPrf (.classMem (synCwppfreceq F G I) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppfreceq F G I))
  have p0001 := @gEqid (synCfrec F I)
  have p0002 := @gElex F (synCfuns)
  have p0003 := Nominal.mp hyp_wppfreceqexndv_1 p0002
  have p0004 := @gFrecex (synCfrec F I) F I p0001 p0003
  have p0005 := @gCnvexg (synCfrec F I) (synCvv)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gEqid (synCfrec G I)
  have p0008 := @gElex G (synCfuns)
  have p0009 := Nominal.mp hyp_wppfreceqexndv_2 p0008
  have p0010 := @gFrecex (synCfrec G I) G I p0007 p0009
  have p0011 :=
    @gPm32i (.classMem (synCcnv (synCfrec F I)) (synCvv))
      (.classMem (synCfrec G I) (synCvv)) p0006 p0010
  have p0012 := @gCoexg (synCcnv (synCfrec F I)) (synCfrec G I) (synCvv) (synCvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gFixexg (synCcom (synCcnv (synCfrec F I)) (synCfrec G I)) (synCvv)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gEqeltri (synCwppfreceq F G I)
      (synCfix (synCcom (synCcnv (synCfrec F I)) (synCfrec G I))) (synCvv) p0000
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_wppfreceqvalndv`. -/
@[expose]
noncomputable def gWppfreceqvalndv (n : Var) (F : Class) (G : Class) (I : Class)
    (hyp_wppfreceqvalndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppfreceqvalndv_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_wppfreceqvalndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppfreceqvalndv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppfreceqvalndv_5 : Nominal.NPrf (.classMem I (synCdm G)))
    (hyp_wppfreceqvalndv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwppfreceq F G I))
          (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppfreceq F G I))
  have p0001 :=
    @gEleq2i (synCwppfreceq F G I)
      (synCfix (synCcom (synCcnv (synCfrec F I)) (synCfrec G I))) (.cv n) p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (.cv n) (synCwppfreceq F G I)) (.classMem (.cv n)
          (synCfix (synCcom (synCcnv (synCfrec F I)) (synCfrec G I)))))
      (.classMem (.cv n) (synCnnc)) p0001
  have p0003 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wppfreceqvalndv_1 hyp_wppfreceqvalndv_2
      hyp_wppfreceqvalndv_3
  have p0004 := @gWpporbitfnndv F I
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gFnfun (synCnnc) (synCfrec F I)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gA1i (synWfun (synCfrec F I)) (.classMem (.cv n) (synCnnc)) p0007
  have p0009 :=
    @gN3pm32i (.classMem G (synCfuns)) (.classMem I (synCdm G))
      (synWss (synCrn G) (synCdm G)) hyp_wppfreceqvalndv_4 hyp_wppfreceqvalndv_5
      hyp_wppfreceqvalndv_6
  have p0010 := @gWpporbitfnndv G I
  have p0011 := Nominal.mp p0009 p0010
  have p0012 := @gFnfun (synCnnc) (synCfrec G I)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gA1i (synWfun (synCfrec G I)) (.classMem (.cv n) (synCnnc)) p0013
  have p0018 := @gFndm (synCnnc) (synCfrec F I)
  have p0019 := Nominal.mp p0005 p0018
  have p0020 := @gEleq2i (synCdm (synCfrec F I)) (synCnnc) (.cv n) p0019
  have p0021 :=
    @gBiimpri (.classMem (.cv n) (synCdm (synCfrec F I)))
      (.classMem (.cv n) (synCnnc)) p0020
  have p0025 := @gFndm (synCnnc) (synCfrec G I)
  have p0026 := Nominal.mp p0011 p0025
  have p0027 := @gEleq2i (synCdm (synCfrec G I)) (synCnnc) (.cv n) p0026
  have p0028 :=
    @gBiimpri (.classMem (.cv n) (synCdm (synCfrec G I)))
      (.classMem (.cv n) (synCnnc)) p0027
  have p0029 :=
    @gJca (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCdm (synCfrec F I)))
      (.classMem (.cv n) (synCdm (synCfrec G I))) p0021 p0028
  have p0030 :=
    @gN3jca (.classMem (.cv n) (synCnnc)) (synWfun (synCfrec F I))
      (synWfun (synCfrec G I))
      (synWa (.classMem (.cv n) (synCdm (synCfrec F I)))
        (.classMem (.cv n) (synCdm (synCfrec G I))))
      p0008 p0014 p0029
  have p0031 := @gFuneqfix (.cv n) (synCfrec F I) (synCfrec G I)
  have p0032 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synW3a (synWfun (synCfrec F I)) (synWfun (synCfrec G I))
        (synWa (.classMem (.cv n) (synCdm (synCfrec F I)))
          (.classMem (.cv n) (synCdm (synCfrec G I)))))
      (synWb (.classMem (.cv n)
          (synCfix (synCcom (synCcnv (synCfrec F I)) (synCfrec G I))))
        (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))
      p0030 p0031
  have p0033 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwppfreceq F G I))
      (.classMem (.cv n) (synCfix (synCcom (synCcnv (synCfrec F I)) (synCfrec G I))))
      (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))) p0002
      p0032
  exact p0033

/-- Checked nominal proof certificate identified upstream as `g_wppfreceqvalclndv`. -/
@[expose]
noncomputable def gWppfreceqvalclndv (B : Class) (F : Class) (G : Class) (I : Class)
    (hyp_wppfreceqvalclndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppfreceqvalclndv_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_wppfreceqvalclndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppfreceqvalclndv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppfreceqvalclndv_5 : Nominal.NPrf (.classMem I (synCdm G)))
    (hyp_wppfreceqvalclndv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwppfreceq F G I))
          (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))) :=
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
  have dv_cache_0002 : n ∉ ((synCnnc)).fv :=
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
      ((synWb (.classMem B (synCwppfreceq F G I))
          (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))).fv :=
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
    @gWppfreceqvalndv n F G I hyp_wppfreceqvalclndv_1 hyp_wppfreceqvalclndv_2
      hyp_wppfreceqvalclndv_3 hyp_wppfreceqvalclndv_4 hyp_wppfreceqvalclndv_5
      hyp_wppfreceqvalclndv_6
  have p0001 :=
    @gRgen
      (synWb (.classMem (.cv n) (synCwppfreceq F G I))
        (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))
      n (synCnnc) p0000
  have p0002 := @gId (.classEq (.cv n) B)
  have p0003 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCwppfreceq F G I) p0002
  have p0005 := @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec F I) p0002
  have p0007 := @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec G I) p0002
  have p0008 :=
    @gEqeq12d (.classEq (.cv n) B) (synCfv (synCfrec F I) (.cv n))
      (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) (.cv n))
      (synCfv (synCfrec G I) B) p0005 p0007
  have p0009 :=
    @gBibi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCwppfreceq F G I))
      (.classMem B (synCwppfreceq F G I))
      (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n)))
      (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)) p0003 p0008
  have p0010 :=
    @gRspcv
      (synWb (.classMem (.cv n) (synCwppfreceq F G I))
        (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))
      (synWb (.classMem B (synCwppfreceq F G I))
        (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
      n B (synCnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009
  have p0011 :=
    @gMpi (.classMem B (synCnnc))
      (synWral n (synCnnc) (synWb (.classMem (.cv n) (synCwppfreceq F G I))
          (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n)))))
      (synWb (.classMem B (synCwppfreceq F G I))
        (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
      p0001 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wppfrecprefixeqexndv`. -/
@[expose]
noncomputable def gWppfrecprefixeqexndv (k : Var) (F : Class) (G : Class) (I : Class)
    (hyp_wppfrecprefixeqexndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppfrecprefixeqexndv_2 : Nominal.NPrf (.classMem G (synCfuns))) :
    Nominal.NPrf (.classMem (synCwppfrecprefixeq F G I k) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppfrecprefixeq F G I k))
  have p0001 := @gNncex
  have p0002 := @gLefinex
  have p0003 := @gKqrelex (synClefin) p0002
  have p0004 := @gCnvexg (synCkqrel (synClefin)) (synCvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gSnex (.cv k)
  have p0007 :=
    @gImaex (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)) p0005 p0006
  have p0008 :=
    @gDifex (synCnnc) (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))
      p0001 p0007
  have p0009 :=
    @gWppfreceqexndv F G I hyp_wppfrecprefixeqexndv_1 hyp_wppfrecprefixeqexndv_2
  have p0010 :=
    @gUnex
      (synCdif (synCnnc) (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
      (synCwppfreceq F G I) p0008 p0009
  have p0011 :=
    @gEqeltri (synCwppfrecprefixeq F G I k)
      (synCun (synCdif (synCnnc)
          (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
        (synCwppfreceq F G I))
      (synCvv) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wppfrecprefixeqvalndv`. -/
@[expose]
noncomputable def gWppfrecprefixeqvalndv (B : Class) (k : Var) (F : Class) (G : Class)
    (I : Class) (hyp_wppfrecprefixeqvalndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppfrecprefixeqvalndv_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_wppfrecprefixeqvalndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppfrecprefixeqvalndv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppfrecprefixeqvalndv_5 : Nominal.NPrf (.classMem I (synCdm G)))
    (hyp_wppfrecprefixeqvalndv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwppfrecprefixeq F G I k))
          (.imp (synWbr B (synCkqrel (synClefin)) (.cv k))
            (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppfrecprefixeq F G I k))
  have p0001 :=
    @gEleq2i (synCwppfrecprefixeq F G I k)
      (synCun (synCdif (synCnnc)
          (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
        (synCwppfreceq F G I))
      B p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem B (synCwppfrecprefixeq F G I k)) (.classMem B (synCun
            (synCdif (synCnnc)
              (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
            (synCwppfreceq F G I))))
      (.classMem B (synCnnc)) p0001
  have p0003 :=
    @gElun B
      (synCdif (synCnnc) (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
      (synCwppfreceq F G I)
  have p0004 :=
    @gA1i
      (synWb (.classMem B (synCun (synCdif (synCnnc)
              (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
            (synCwppfreceq F G I))) (synWo (.classMem B (synCdif (synCnnc)
              (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
          (.classMem B (synCwppfreceq F G I))))
      (.classMem B (synCnnc)) p0003
  have p0005 :=
    @gEldif B (synCnnc)
      (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))
  have p0006 :=
    @gA1i
      (synWb (.classMem B (synCdif (synCnnc)
            (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
        (synWa (.classMem B (synCnnc)) (.neg (.classMem B
              (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))))
      (.classMem B (synCnnc)) p0005
  have p0007 := @gId (.classMem B (synCnnc))
  have p0008 :=
    @gBiantrurd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (.neg (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
      p0007
  have p0009 :=
    @gBitr4d (.classMem B (synCnnc))
      (.classMem B (synCdif (synCnnc)
          (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
      (synWa (.classMem B (synCnnc)) (.neg (.classMem B
            (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))))
      (.neg (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
      p0006 p0008
  have p0010 := @gElimasn (synCcnv (synCkqrel (synClefin))) (.cv k) B
  have p0011 :=
    (Nominal.biimpRefl (synWbr (.cv k) (synCcnv (synCkqrel (synClefin))) B))
  have p0012 :=
    @gBitr4i
      (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
      (.classMem (synCop (.cv k) B) (synCcnv (synCkqrel (synClefin))))
      (synWbr (.cv k) (synCcnv (synCkqrel (synClefin))) B) p0010 p0011
  have p0013 := @gBrcnv (.cv k) B (synCkqrel (synClefin))
  have p0014 :=
    @gBitri
      (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
      (synWbr (.cv k) (synCcnv (synCkqrel (synClefin))) B)
      (synWbr B (synCkqrel (synClefin)) (.cv k)) p0012 p0013
  have p0015 :=
    @gNotbi
      (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
      (synWbr B (synCkqrel (synClefin)) (.cv k))
  have p0016 :=
    @gMpbi
      (synWb (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
        (synWbr B (synCkqrel (synClefin)) (.cv k)))
      (synWb (.neg
          (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
        (.neg (synWbr B (synCkqrel (synClefin)) (.cv k))))
      p0014 p0015
  have p0017 :=
    @gA1i
      (synWb (.neg
          (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
        (.neg (synWbr B (synCkqrel (synClefin)) (.cv k))))
      (.classMem B (synCnnc)) p0016
  have p0018 :=
    @gBitrd (.classMem B (synCnnc))
      (.classMem B (synCdif (synCnnc)
          (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
      (.neg (.classMem B (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
      (.neg (synWbr B (synCkqrel (synClefin)) (.cv k))) p0009 p0017
  have p0019 :=
    @gWppfreceqvalclndv B F G I hyp_wppfrecprefixeqvalndv_1 hyp_wppfrecprefixeqvalndv_2
      hyp_wppfrecprefixeqvalndv_3 hyp_wppfrecprefixeqvalndv_4 hyp_wppfrecprefixeqvalndv_5
      hyp_wppfrecprefixeqvalndv_6
  have p0020 :=
    @gOrbi12d (.classMem B (synCnnc))
      (.classMem B (synCdif (synCnnc)
          (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
      (.neg (synWbr B (synCkqrel (synClefin)) (.cv k)))
      (.classMem B (synCwppfreceq F G I))
      (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)) p0018 p0019
  have p0021 :=
    @gBitrd (.classMem B (synCnnc))
      (.classMem B (synCun (synCdif (synCnnc)
            (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
          (synCwppfreceq F G I)))
      (synWo (.classMem B (synCdif (synCnnc)
            (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k)))))
        (.classMem B (synCwppfreceq F G I)))
      (synWo (.neg (synWbr B (synCkqrel (synClefin)) (.cv k)))
        (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
      p0004 p0020
  have p0022 :=
    @gImor (synWbr B (synCkqrel (synClefin)) (.cv k))
      (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B))
  have p0023 :=
    @gA1i
      (synWb (.imp (synWbr B (synCkqrel (synClefin)) (.cv k))
          (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
        (synWo (.neg (synWbr B (synCkqrel (synClefin)) (.cv k)))
          (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B))))
      (.classMem B (synCnnc)) p0022
  have p0024 :=
    @gBitr4d (.classMem B (synCnnc))
      (.classMem B (synCun (synCdif (synCnnc)
            (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
          (synCwppfreceq F G I)))
      (synWo (.neg (synWbr B (synCkqrel (synClefin)) (.cv k)))
        (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
      (.imp (synWbr B (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
      p0021 p0023
  have p0025 :=
    @gBitrd (.classMem B (synCnnc)) (.classMem B (synCwppfrecprefixeq F G I k))
      (.classMem B (synCun (synCdif (synCnnc)
            (synCima (synCcnv (synCkqrel (synClefin))) (synCsn (.cv k))))
          (synCwppfreceq F G I)))
      (.imp (synWbr B (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) B) (synCfv (synCfrec G I) B)))
      p0002 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_wppstopstepsamebelowdndv`. -/
@[expose]
noncomputable def gWppstopstepsamebelowdndv (y : Var) (C : Class) (F : Class) (p : Var)
    (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_p_y : p ≠ y)
    (hyp_wppstopstepsamebelowdndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppstopstepsamebelowdndv_2 :
      Nominal.NPrf (synWss (synCrn F) (synChwcards (synCvv))))
    (hyp_wppstopstepsamebelowdndv_3 : Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppstopstepsamebelowdndv_4 : Nominal.NPrf (synWbr (synCtc C) (synClec) C))
    (hyp_wppstopstepsamebelowdndv_5 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F))))) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (synChwcards (synCvv)))
        (.imp (synWbr (.cv y) (synClec) (synCtc C))
          (.classEq (synCfv (synCwppstopstep F C) (.cv y))
            (synCfv (synCwppstopstep F (synCtc C)) (.cv y))))) :=
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
  have dv_cache_0002 : p ∉ ((synChwcards (synCvv))).fv :=
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
    p ∉ ((Wff.imp (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F)))).fv :=
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
    @gSimpr (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc C))
  have p0001 :=
    @gA1i (synWbr (synCtc C) (synClec) C)
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      hyp_wppstopstepsamebelowdndv_4
  have p0002 :=
    @gJca
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWbr (.cv y) (synClec) (synCtc C)) (synWbr (synCtc C) (synClec) C) p0000
      p0001
  have p0003 :=
    @gSimpl (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc C))
  have p0004 := @gHwcardssnc (synCvv)
  have p0005 := @gSsel (synChwcards (synCvv)) (synCncs) (.cv y)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (.classMem (.cv y) (synChwcards (synCvv))) (.classMem (.cv y) (synCncs)) p0003
      p0006
  have p0009 :=
    @gSselii (synChwcards (synCvv)) (synCncs) C p0004 hyp_wppstopstepsamebelowdndv_3
  have p0010 := @gTccl C
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gA1i (.classMem (synCtc C) (synCncs))
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      p0011
  have p0015 :=
    @gA1i (.classMem C (synCncs))
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      p0009
  have p0016 :=
    @gN3jca
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (.classMem (.cv y) (synCncs)) (.classMem (synCtc C) (synCncs))
      (.classMem C (synCncs)) p0007 p0012 p0015
  have p0017 := @gLectr (.cv y) (synCtc C) C
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synW3a (.classMem (.cv y) (synCncs)) (.classMem (synCtc C) (synCncs))
        (.classMem C (synCncs)))
      (.imp (synWa (synWbr (.cv y) (synClec) (synCtc C)) (synWbr (synCtc C) (synClec) C))
        (synWbr (.cv y) (synClec) C))
      p0016 p0017
  have p0019 :=
    @gMpd
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWa (synWbr (.cv y) (synClec) (synCtc C)) (synWbr (synCtc C) (synClec) C))
      (synWbr (.cv y) (synClec) C) p0002 p0018
  have p0022 := @gId (.classEq (.cv p) (.cv y))
  have p0023 := @gBreq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) C (synClec) p0022
  have p0025 := @gEleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (synCdm F) p0022
  have p0026 :=
    @gImbi12d (.classEq (.cv p) (.cv y)) (synWbr (.cv p) (synClec) C)
      (synWbr (.cv y) (synClec) C) (.classMem (.cv p) (synCdm F))
      (.classMem (.cv y) (synCdm F)) p0023 p0025
  have p0027 :=
    @gRspcv (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))
      (.imp (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F))) p (.cv y)
      (synChwcards (synCvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0026
  have p0028 :=
    @gMpi (.classMem (.cv y) (synChwcards (synCvv)))
      (synWral p (synChwcards (synCvv))
        (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F))))
      (.imp (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F)))
      hyp_wppstopstepsamebelowdndv_5 p0027
  have p0029 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F))) p0003 p0028
  have p0030 :=
    @gJca
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F))) p0003 p0029
  have p0031 :=
    @gWppstopstepfvlecdndv (.cv y) C F hyp_wppstopstepsamebelowdndv_1
      hyp_wppstopstepsamebelowdndv_2
  have p0032 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (.imp (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F))))
      (.imp (synWbr (.cv y) (synClec) C)
        (.classEq (synCfv (synCwppstopstep F C) (.cv y)) (synCfv F (.cv y))))
      p0030 p0031
  have p0033 :=
    @gMpd
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWbr (.cv y) (synClec) C)
      (.classEq (synCfv (synCwppstopstep F C) (.cv y)) (synCfv F (.cv y))) p0019 p0032
  have p0066 :=
    @gMpd
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWbr (.cv y) (synClec) C) (.classMem (.cv y) (synCdm F)) p0019 p0029
  have p0067 :=
    @gEx (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc C)) (.classMem (.cv y) (synCdm F)) p0066
  have p0068 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) (synCtc C)) (.classMem (.cv y) (synCdm F)))
      p0003 p0067
  have p0069 :=
    @gJca
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) (synCtc C)) (.classMem (.cv y) (synCdm F)))
      p0003 p0068
  have p0070 :=
    @gWppstopstepfvlecdndv (.cv y) (synCtc C) F hyp_wppstopstepsamebelowdndv_1
      hyp_wppstopstepsamebelowdndv_2
  have p0071 :=
    @gSyl
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (.imp (synWbr (.cv y) (synClec) (synCtc C)) (.classMem (.cv y) (synCdm F))))
      (.imp (synWbr (.cv y) (synClec) (synCtc C))
        (.classEq (synCfv (synCwppstopstep F (synCtc C)) (.cv y)) (synCfv F (.cv y))))
      p0069 p0070
  have p0072 :=
    @gMpd
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synWbr (.cv y) (synClec) (synCtc C))
      (.classEq (synCfv (synCwppstopstep F (synCtc C)) (.cv y)) (synCfv F (.cv y)))
      p0000 p0071
  have p0073 :=
    @gEqcomd
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synCfv (synCwppstopstep F (synCtc C)) (.cv y)) (synCfv F (.cv y)) p0072
  have p0074 :=
    @gEqtrd
      (synWa (.classMem (.cv y) (synChwcards (synCvv)))
        (synWbr (.cv y) (synClec) (synCtc C)))
      (synCfv (synCwppstopstep F C) (.cv y)) (synCfv F (.cv y))
      (synCfv (synCwppstopstep F (synCtc C)) (.cv y)) p0033 p0073
  have p0075 :=
    @gEx (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc C))
      (.classEq (synCfv (synCwppstopstep F C) (.cv y))
        (synCfv (synCwppstopstep F (synCtc C)) (.cv y)))
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

/-- Checked nominal proof certificate identified upstream as `g_wppreachtchwboundedndv`. -/
@[expose]
noncomputable def gWppreachtchwboundedndv (x : Var) (C : Class) (F : Class) (G : Class)
    (r : Var) (p : Var) (d : Var) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv)
    (dv_C_x : x ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_G_p : p ∉ G.fv) (_dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_d_p : d ≠ p)
    (dv_d_r : d ≠ r) (dv_d_x : d ≠ x) (dv_p_r : p ≠ r) (_dv_p_x : p ≠ x) (_dv_r_x : r ≠ x)
    (hyp_wppreachtchwboundedndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachtchwboundedndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachtchwboundedndv_3 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppreachtchwboundedndv_4 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppreachtchwboundedndv_5 : Nominal.NPrf (synWral x (synCdm F)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x))))))
    (hyp_wppreachtchwboundedndv_6 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (synWa (.classMem (.cv p) (synCdm F))
              (.classMem (synCtc (.cv p)) (synCdm G))))))
    (hyp_wppreachtchwboundedndv_7 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (synWral r (synCnnc)
              (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs))))))
    (hyp_wppreachtchwboundedndv_8 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
        (synWb (.classMem (.cv d) (synCwppreach F C))
          (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))))) :=
  by
  have dv_cache_0001 :
    p ∉
      ((synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C)).fv :=
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
  have dv_cache_0002 : p ∉ ((synChwcards (synCvv))).fv :=
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
      ((Wff.imp (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C) (synWa (.classMem
              (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                  (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCdm F)) (.classMem (synCtc
                (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                    (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCdm G))))).fv :=
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
      ((Wff.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C))).fv :=
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
      ((Wff.imp (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C) (synWral r (synCnnc)
            (.classMem (synCfv (synCfrec F (synCif
                    (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                      (synWbr (.cv d) (synClec) C)) (.cv d) C)) (.cv r)) (synCncs))))).fv :=
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
      ((synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C)).fv :=
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
      ((synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C)).fv :=
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
    @gId
      (.classEq (.cv d) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
  have p0001 :=
    @gEleq1d
      (.classEq (.cv d) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.cv d)
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      (synCwppreach F C) p0000
  have p0002 :=
    @gTceq (.cv d)
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
  have p0003 :=
    @gEleq1d
      (.classEq (.cv d) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synCtc (.cv d))
      (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synCwppreach G (synCtc C)) p0002
  have p0004 :=
    @gBibi12d
      (.classEq (.cv d) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.classMem (.cv d) (synCwppreach F C))
      (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCwppreach F C))
      (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C)))
      (.classMem (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCwppreach G (synCtc C)))
      p0001 p0003
  have p0005 :=
    @gSimpr (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C)
  have p0006 :=
    @gIftrue
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.cv d) C
  have p0007 :=
    @gBreq1d
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      (.cv d) C (synClec) p0006
  have p0008 :=
    @gMpbird
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C)
      (synWbr (.cv d) (synClec) C) p0005 p0007
  have p0009 := @gHwcardssnc (synCvv)
  have p0010 := @gSseli (synChwcards (synCvv)) (synCncs) C p0009
  have p0011 := Nominal.mp hyp_wppreachtchwboundedndv_8 p0010
  have p0012 := @gNclecid C
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gA1i (synWbr C (synClec) C)
      (.neg (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)))
      p0013
  have p0015 :=
    @gIffalse
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.cv d) C
  have p0016 :=
    @gBreq1d
      (.neg (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)))
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      C C (synClec) p0015
  have p0017 :=
    @gMpbird
      (.neg (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)))
      (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C)
      (synWbr C (synClec) C) p0014 p0016
  have p0018 :=
    @gPm261i
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C)
      p0008 p0017
  have p0019 := @gTru
  have p0020 :=
    @gSimpr synWtru
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
  have p0021 :=
    @gSimpl (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C)
  have p0022 :=
    @gSyl
      (synWa synWtru (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synChwcards (synCvv))) p0020 p0021
  have p0023 :=
    @gA1i (.classMem C (synChwcards (synCvv)))
      (synWa synWtru (.neg (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C))))
      hyp_wppreachtchwboundedndv_8
  have p0024 :=
    @gIfclda synWtru
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.cv d) C (synChwcards (synCvv)) p0022 p0023
  have p0025 := Nominal.mp p0019 p0024
  have p0026 :=
    @gPm32i
      (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synChwcards (synCvv)))
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) C)
          (synWa (.classMem (.cv p) (synCdm F)) (.classMem (synCtc (.cv p)) (synCdm G)))))
      p0025 hyp_wppreachtchwboundedndv_6
  have p0027 :=
    @gId
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
  have p0028 :=
    @gBreq1d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.cv p)
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      C (synClec) p0027
  have p0030 :=
    @gEleq1d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.cv p)
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      (synCdm F) p0027
  have p0031 :=
    @gTceq (.cv p)
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
  have p0032 :=
    @gEleq1d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synCtc (.cv p))
      (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synCdm G) p0031
  have p0033 :=
    @gAnbi12d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.classMem (.cv p) (synCdm F))
      (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCdm F))
      (.classMem (synCtc (.cv p)) (synCdm G))
      (.classMem (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCdm G))
      p0030 p0032
  have p0034 :=
    @gImbi12d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synWbr (.cv p) (synClec) C)
      (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C)
      (synWa (.classMem (.cv p) (synCdm F)) (.classMem (synCtc (.cv p)) (synCdm G)))
      (synWa (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCdm F)) (.classMem (synCtc
            (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCdm G)))
      p0028 p0033
  have p0035 :=
    @gRspcva
      (.imp (synWbr (.cv p) (synClec) C) (synWa (.classMem (.cv p) (synCdm F))
          (.classMem (synCtc (.cv p)) (synCdm G))))
      (.imp (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C) (synWa (.classMem
            (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCdm F)) (.classMem (synCtc
              (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                  (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCdm G))))
      p
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      (synChwcards (synCvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0034
  have p0036 := Nominal.mp p0026 p0035
  have p0037 := Nominal.mp p0018 p0036
  have p0038 :=
    @gSimpl
      (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCdm F))
      (.classMem (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCdm G))
  have p0039 := Nominal.mp p0037 p0038
  have p0073 :=
    @gSimpr
      (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCdm F))
      (.classMem (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCdm G))
  have p0074 := Nominal.mp p0037 p0073
  have p0099 :=
    @gPm32i
      (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synChwcards (synCvv)))
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) C)
          (synWral r (synCnnc)
            (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs)))))
      p0025 hyp_wppreachtchwboundedndv_7
  have p0102 :=
    @gEqidd
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      F
  have p0104 :=
    @gJca
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.classEq F F)
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      p0102 p0027
  have p0105 :=
    @gFreceq12 F F (.cv p)
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
  have p0106 :=
    @gSyl
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synWa (.classEq F F) (.classEq (.cv p) (synCif
            (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
            (.cv d) C)))
      (.classEq (synCfrec F (.cv p)) (synCfrec F (synCif
            (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
            (.cv d) C)))
      p0104 p0105
  have p0107 :=
    @gFveq1d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.cv r) (synCfrec F (.cv p))
      (synCfrec F (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      p0106
  have p0108 :=
    @gEleq1d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synCfv (synCfrec F (.cv p)) (.cv r))
      (synCfv (synCfrec F (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C)) (.cv r))
      (synCncs) p0107
  have p0109 :=
    @gRalbidv
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs))
      (.classMem (synCfv (synCfrec F (synCif
              (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                (synWbr (.cv d) (synClec) C)) (.cv d) C)) (.cv r)) (synCncs))
      r (synCnnc) dv_cache_0004 p0108
  have p0110 :=
    @gImbi12d
      (.classEq (.cv p) (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C))
      (synWbr (.cv p) (synClec) C)
      (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
            (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C)
      (synWral r (synCnnc) (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs)))
      (synWral r (synCnnc) (.classMem (synCfv (synCfrec F (synCif
                (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                  (synWbr (.cv d) (synClec) C)) (.cv d) C)) (.cv r)) (synCncs)))
      p0028 p0109
  have p0111 :=
    @gRspcva
      (.imp (synWbr (.cv p) (synClec) C) (synWral r (synCnnc)
          (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs))))
      (.imp (synWbr (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C) (synClec) C) (synWral r (synCnnc)
          (.classMem (synCfv (synCfrec F (synCif
                  (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                    (synWbr (.cv d) (synClec) C)) (.cv d) C)) (.cv r)) (synCncs))))
      p
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      (synChwcards (synCvv)) dv_cache_0001 dv_cache_0002 dv_cache_0005 p0110
  have p0112 := Nominal.mp p0099 p0111
  have p0113 := Nominal.mp p0018 p0112
  have p0114 :=
    @gWppreachtcbidv x C
      (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.cv d) C)
      F G r dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      hyp_wppreachtchwboundedndv_1 p0039 hyp_wppreachtchwboundedndv_2
      hyp_wppreachtchwboundedndv_3 p0074 hyp_wppreachtchwboundedndv_4
      hyp_wppreachtchwboundedndv_5 p0011 p0113
  have p0115 :=
    @gDedth
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (synWb (.classMem (.cv d) (synCwppreach F C))
        (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))))
      (synWb (.classMem (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
              (synWbr (.cv d) (synClec) C)) (.cv d) C) (synCwppreach F C)) (.classMem
          (synCtc (synCif (synWa (.classMem (.cv d) (synChwcards (synCvv)))
                (synWbr (.cv d) (synClec) C)) (.cv d) C)) (synCwppreach G (synCtc C))))
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

/-- Checked nominal proof certificate identified upstream as `g_wppcandtchwboundedimagebindv`. -/
@[expose]
noncomputable def gWppcandtchwboundedimagebindv (x : Var) (C : Class) (k : Var)
    (F : Class) (G : Class) (r : Var) (p : Var) (d : Var) (dv_C_d : d ∉ C.fv)
    (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_d : d ∉ F.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_d : d ∉ G.fv)
    (dv_G_p : p ∉ G.fv) (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_d_k : d ≠ k)
    (dv_d_p : d ≠ p) (dv_d_r : d ≠ r) (dv_d_x : d ≠ x) (_dv_k_p : k ≠ p) (_dv_k_r : k ≠ r)
    (_dv_k_x : k ≠ x) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x) (dv_r_x : r ≠ x)
    (hyp_wppcandtchwboundedimagebindv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppcandtchwboundedimagebindv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppcandtchwboundedimagebindv_3 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppcandtchwboundedimagebindv_4 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppcandtchwboundedimagebindv_5 : Nominal.NPrf (synWral x (synCdm F)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x))))))
    (hyp_wppcandtchwboundedimagebindv_6 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (synWa (.classMem (.cv p) (synCdm F))
              (.classMem (synCtc (.cv p)) (synCdm G))))))
    (hyp_wppcandtchwboundedimagebindv_7 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (synWral r (synCnnc)
              (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs))))))
    (hyp_wppcandtchwboundedimagebindv_8 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWb (.classMem (.cv k) (synCwppcand G (synCtc C))) (synWex d
          (synWa (.classMem (.cv d) (synCwppcand F C))
            (.classEq (.cv k) (synCtc (.cv d)))))) :=
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
      ((synWa (.classMem (.cv q) (synCwppcand F C))
          (.classEq (.cv k) (synCtc (.cv q))))).fv :=
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
      ((synWex d (synWa (.classMem (.cv d) (synCwppcand F C))
            (.classEq (.cv k) (synCtc (.cv d)))))).fv :=
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
  have dv_cache_0020 : q ∉ ((Wff.classMem (.cv k) (synCwppcand G (synCtc C)))).fv :=
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
  have dv_cache_0024 : d ∉ ((Wff.classMem (.cv k) (synCwppcand G (synCtc C)))).fv :=
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
  have p0000 := @gElwppcand (synCtc C) (.cv k) G
  have p0001 :=
    @gBiimpi (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) (synCtc C)))
        (.classMem (.cv k) (synCwppreach G (synCtc C))))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (synWbr (.cv k) (synClec) (synCtc C)))
      (.classMem (.cv k) (synCwppreach G (synCtc C)))
  have p0003 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) (synCtc C)))
        (.classMem (.cv k) (synCwppreach G (synCtc C))))
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (synWbr (.cv k) (synClec) (synCtc C)))
      p0001 p0002
  have p0004 :=
    @gSimpl (.classMem (.cv k) (synChwcards (synCvv)))
      (synWbr (.cv k) (synClec) (synCtc C))
  have p0005 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (synWbr (.cv k) (synClec) (synCtc C)))
      (.classMem (.cv k) (synChwcards (synCvv))) p0003 p0004
  have p0006 := @gHwcardssnc (synCvv)
  have p0007 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv k) p0006
  have p0008 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (.classMem (.cv k) (synChwcards (synCvv))) (.classMem (.cv k) (synCncs)) p0005
      p0007
  have p0010 := @gSseli (synChwcards (synCvv)) (synCncs) C p0006
  have p0011 := Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0010
  have p0012 :=
    @gA1i (.classMem C (synCncs)) (.classMem (.cv k) (synCwppcand G (synCtc C))) p0011
  have p0017 :=
    @gSimpr (.classMem (.cv k) (synChwcards (synCvv)))
      (synWbr (.cv k) (synClec) (synCtc C))
  have p0018 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (synWbr (.cv k) (synClec) (synCtc C)))
      (synWbr (.cv k) (synClec) (synCtc C)) p0003 p0017
  have p0019 :=
    @gN3jca (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (.classMem (.cv k) (synCncs)) (.classMem C (synCncs))
      (synWbr (.cv k) (synClec) (synCtc C)) p0008 p0012 p0018
  have p0020 := @gLetc (.cv k) C q dv_cache_0001
  have p0021 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synW3a (.classMem (.cv k) (synCncs)) (.classMem C (synCncs))
        (synWbr (.cv k) (synClec) (synCtc C)))
      (synWrex q (synCncs) (.classEq (.cv k) (synCtc (.cv q)))) p0019 p0020
  have p0022 :=
    @gSimpr (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q))))
  have p0023 :=
    @gSimpl (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))
  have p0024 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q))))
      (.classMem (.cv q) (synCncs)) p0022 p0023
  have p0025 :=
    @gA1i (.classMem C (synChwcards (synCvv)))
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      hyp_wppcandtchwboundedimagebindv_8
  have p0026 :=
    @gJca
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv q) (synCncs)) (.classMem C (synChwcards (synCvv))) p0024 p0025
  have p0027 :=
    @gSimpl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q))))
  have p0034 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWbr (.cv k) (synClec) (synCtc C)) p0027 p0018
  have p0036 :=
    @gSimpr (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))
  have p0037 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q))))
      (.classEq (.cv k) (synCtc (.cv q))) p0022 p0036
  have p0038 := @gId (.classEq (.cv k) (synCtc (.cv q)))
  have p0039 :=
    @gBreq1d (.classEq (.cv k) (synCtc (.cv q))) (.cv k) (synCtc (.cv q)) (synCtc C)
      (synClec) p0038
  have p0040 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classEq (.cv k) (synCtc (.cv q)))
      (synWb (synWbr (.cv k) (synClec) (synCtc C))
        (synWbr (synCtc (.cv q)) (synClec) (synCtc C)))
      p0037 p0039
  have p0041 :=
    @gMpbid
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWbr (.cv k) (synClec) (synCtc C))
      (synWbr (synCtc (.cv q)) (synClec) (synCtc C)) p0034 p0040
  have p0048 :=
    @gA1i (.classMem C (synCncs))
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      p0011
  have p0049 :=
    @gJca
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv q) (synCncs)) (.classMem C (synCncs)) p0024 p0048
  have p0050 := @gTlecg (.cv q) C
  have p0051 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synCncs)) (.classMem C (synCncs)))
      (synWb (synWbr (.cv q) (synClec) C) (synWbr (synCtc (.cv q)) (synClec) (synCtc C)))
      p0049 p0050
  have p0052 :=
    @gMpbird
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWbr (.cv q) (synClec) C) (synWbr (synCtc (.cv q)) (synClec) (synCtc C))
      p0041 p0051
  have p0053 :=
    @gJca
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synCncs)) (.classMem C (synChwcards (synCvv))))
      (synWbr (.cv q) (synClec) C) p0026 p0052
  have p0054 := @gHwcardsdownltcndv C q
  have p0055 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (synWa (.classMem (.cv q) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv q) (synClec) C))
      (.classMem (.cv q) (synChwcards (synCvv))) p0053 p0054
  have p0082 :=
    @gJca
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv q) (synChwcards (synCvv))) (synWbr (.cv q) (synClec) C) p0055
      p0052
  have p0086 :=
    @gSimpr
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (synWbr (.cv k) (synClec) (synCtc C)))
      (.classMem (.cv k) (synCwppreach G (synCtc C)))
  have p0087 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) (synCtc C)))
        (.classMem (.cv k) (synCwppreach G (synCtc C))))
      (.classMem (.cv k) (synCwppreach G (synCtc C))) p0001 p0086
  have p0088 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (.classMem (.cv k) (synCwppreach G (synCtc C))) p0027 p0087
  have p0093 :=
    @gEleq1d (.classEq (.cv k) (synCtc (.cv q))) (.cv k) (synCtc (.cv q))
      (synCwppreach G (synCtc C)) p0038
  have p0094 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classEq (.cv k) (synCtc (.cv q)))
      (synWb (.classMem (.cv k) (synCwppreach G (synCtc C)))
        (.classMem (synCtc (.cv q)) (synCwppreach G (synCtc C))))
      p0037 p0093
  have p0095 :=
    @gMpbid
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv k) (synCwppreach G (synCtc C)))
      (.classMem (synCtc (.cv q)) (synCwppreach G (synCtc C))) p0088 p0094
  have p0157 :=
    @gWppreachtchwboundedndv x C F G r p q dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      hyp_wppcandtchwboundedimagebindv_1 hyp_wppcandtchwboundedimagebindv_2
      hyp_wppcandtchwboundedimagebindv_3 hyp_wppcandtchwboundedimagebindv_4
      hyp_wppcandtchwboundedimagebindv_5 hyp_wppcandtchwboundedimagebindv_6
      hyp_wppcandtchwboundedimagebindv_7 hyp_wppcandtchwboundedimagebindv_8
  have p0158 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synChwcards (synCvv))) (synWbr (.cv q) (synClec) C))
      (synWb (.classMem (.cv q) (synCwppreach F C))
        (.classMem (synCtc (.cv q)) (synCwppreach G (synCtc C))))
      p0082 p0157
  have p0159 :=
    @gMpbird
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv q) (synCwppreach F C))
      (.classMem (synCtc (.cv q)) (synCwppreach G (synCtc C))) p0095 p0158
  have p0160 :=
    @gJca
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synChwcards (synCvv))) (synWbr (.cv q) (synClec) C))
      (.classMem (.cv q) (synCwppreach F C)) p0082 p0159
  have p0161 := @gElwppcand C (.cv q) F
  have p0162 :=
    @gBiimpri (.classMem (.cv q) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv q) (synChwcards (synCvv)))
          (synWbr (.cv q) (synClec) C)) (.classMem (.cv q) (synCwppreach F C)))
      p0161
  have p0163 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (synWa (.classMem (.cv q) (synChwcards (synCvv)))
          (synWbr (.cv q) (synClec) C)) (.classMem (.cv q) (synCwppreach F C)))
      (.classMem (.cv q) (synCwppcand F C)) p0160 p0162
  have p0167 :=
    @gJca
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (.classMem (.cv q) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv q))) p0163
      p0037
  have p0168 := @gVex q
  have p0169 := @gId (.classEq (.cv d) (.cv q))
  have p0170 :=
    @gEleq1d (.classEq (.cv d) (.cv q)) (.cv d) (.cv q) (synCwppcand F C) p0169
  have p0171 := @gTceq (.cv d) (.cv q)
  have p0172 :=
    @gEqeq2d (.classEq (.cv d) (.cv q)) (synCtc (.cv d)) (synCtc (.cv q)) (.cv k) p0171
  have p0173 :=
    @gAnbi12d (.classEq (.cv d) (.cv q)) (.classMem (.cv d) (synCwppcand F C))
      (.classMem (.cv q) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d)))
      (.classEq (.cv k) (synCtc (.cv q))) p0170 p0172
  have p0174 :=
    @gSpcev
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (.cv q) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv q))))
      d (.cv q) dv_cache_0017 dv_cache_0018 p0168 p0173
  have p0175 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWa (.classMem (.cv q) (synCncs)) (.classEq (.cv k) (synCtc (.cv q)))))
      (synWa (.classMem (.cv q) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv q))))
      (synWex d (synWa (.classMem (.cv d) (synCwppcand F C))
          (.classEq (.cv k) (synCtc (.cv d)))))
      p0167 p0174
  have p0176 :=
    @gRexlimddv (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (.classEq (.cv k) (synCtc (.cv q)))
      (synWex d (synWa (.classMem (.cv d) (synCwppcand F C))
          (.classEq (.cv k) (synCtc (.cv d)))))
      q (synCncs) dv_cache_0019 dv_cache_0020 p0021 p0175
  have p0177 :=
    @gSimpl (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d)))
  have p0178 := @gElwppcand C (.cv d) F
  have p0179 :=
    @gBiimpi (.classMem (.cv d) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      p0178
  have p0180 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      p0177 p0179
  have p0181 :=
    @gSimpl
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synCwppreach F C))
  have p0182 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      p0180 p0181
  have p0183 :=
    @gSimpl (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C)
  have p0184 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synChwcards (synCvv))) p0182 p0183
  have p0185 := @gHwcardstcclndv (.cv d)
  have p0186 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synChwcards (synCvv)))
      (.classMem (synCtc (.cv d)) (synChwcards (synCvv))) p0184 p0185
  have p0193 :=
    @gSimpr (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C)
  have p0194 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (synWbr (.cv d) (synClec) C) p0182 p0193
  have p0204 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv d) p0006
  have p0205 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synChwcards (synCvv))) (.classMem (.cv d) (synCncs)) p0184
      p0204
  have p0209 :=
    @gA1i (.classMem C (synCncs))
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      p0011
  have p0210 :=
    @gJca
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synCncs)) (.classMem C (synCncs)) p0205 p0209
  have p0211 := @gTlecg (.cv d) C
  have p0212 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synCncs)))
      (synWb (synWbr (.cv d) (synClec) C) (synWbr (synCtc (.cv d)) (synClec) (synCtc C)))
      p0210 p0211
  have p0213 :=
    @gMpbid
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWbr (.cv d) (synClec) C) (synWbr (synCtc (.cv d)) (synClec) (synCtc C))
      p0194 p0212
  have p0214 :=
    @gJca
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (synCtc (.cv d)) (synChwcards (synCvv)))
      (synWbr (synCtc (.cv d)) (synClec) (synCtc C)) p0186 p0213
  have p0219 :=
    @gSimpr
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synCwppreach F C))
  have p0220 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      (.classMem (.cv d) (synCwppreach F C)) p0180 p0219
  have p0237 :=
    @gJca
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C) p0184
      p0194
  have p0238 :=
    @gWppreachtchwboundedndv x C F G r p d dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0014 dv_cache_0015 dv_cache_0016
      hyp_wppcandtchwboundedimagebindv_1 hyp_wppcandtchwboundedimagebindv_2
      hyp_wppcandtchwboundedimagebindv_3 hyp_wppcandtchwboundedimagebindv_4
      hyp_wppcandtchwboundedimagebindv_5 hyp_wppcandtchwboundedimagebindv_6
      hyp_wppcandtchwboundedimagebindv_7 hyp_wppcandtchwboundedimagebindv_8
  have p0239 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (synWb (.classMem (.cv d) (synCwppreach F C))
        (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))))
      p0237 p0238
  have p0240 :=
    @gMpbid
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synCwppreach F C))
      (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))) p0220 p0239
  have p0241 :=
    @gJca
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (synCtc (.cv d)) (synChwcards (synCvv)))
        (synWbr (synCtc (.cv d)) (synClec) (synCtc C)))
      (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))) p0214 p0240
  have p0242 := @gElwppcand (synCtc C) (synCtc (.cv d)) G
  have p0243 :=
    @gBiimpri (.classMem (synCtc (.cv d)) (synCwppcand G (synCtc C)))
      (synWa (synWa (.classMem (synCtc (.cv d)) (synChwcards (synCvv)))
          (synWbr (synCtc (.cv d)) (synClec) (synCtc C)))
        (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))))
      p0242
  have p0244 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (synWa (.classMem (synCtc (.cv d)) (synChwcards (synCvv)))
          (synWbr (synCtc (.cv d)) (synClec) (synCtc C)))
        (.classMem (synCtc (.cv d)) (synCwppreach G (synCtc C))))
      (.classMem (synCtc (.cv d)) (synCwppcand G (synCtc C))) p0241 p0243
  have p0245 :=
    @gSimpr (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d)))
  have p0246 := @gId (.classEq (.cv k) (synCtc (.cv d)))
  have p0247 :=
    @gEleq1d (.classEq (.cv k) (synCtc (.cv d))) (.cv k) (synCtc (.cv d))
      (synCwppcand G (synCtc C)) p0246
  have p0248 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classEq (.cv k) (synCtc (.cv d)))
      (synWb (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (.classMem (synCtc (.cv d)) (synCwppcand G (synCtc C))))
      p0245 p0247
  have p0249 :=
    @gMpbird
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (.classMem (synCtc (.cv d)) (synCwppcand G (synCtc C))) p0244 p0248
  have p0250 :=
    @gExlimiv
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv k) (synCwppcand G (synCtc C))) d dv_cache_0024 p0249
  have p0251 :=
    @gImpbii (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWex d (synWa (.classMem (.cv d) (synCwppcand F C))
          (.classEq (.cv k) (synCtc (.cv d)))))
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

/-- Checked nominal proof certificate identified upstream as `g_wppgammatchwboundedeqndv`. -/
@[expose]
noncomputable def gWppgammatchwboundedeqndv (x : Var) (C : Class) (F : Class) (G : Class)
    (r : Var) (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_p : p ∉ G.fv)
    (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x)
    (dv_r_x : r ≠ x)
    (hyp_wppgammatchwboundedeqndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppgammatchwboundedeqndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppgammatchwboundedeqndv_3 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppgammatchwboundedeqndv_4 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppgammatchwboundedeqndv_5 : Nominal.NPrf (synWral x (synCdm F)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x))))))
    (hyp_wppgammatchwboundedeqndv_6 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (synWa (.classMem (.cv p) (synCdm F))
              (.classMem (synCtc (.cv p)) (synCdm G))))))
    (hyp_wppgammatchwboundedeqndv_7 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (synWral r (synCnnc)
              (.classMem (synCfv (synCfrec F (.cv p)) (.cv r)) (synCncs))))))
    (hyp_wppgammatchwboundedeqndv_8 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf (.classEq (synCtc (synCwppgamma F C)) (synCwppgamma G (synCtc C))) :=
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
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wppgammatchwboundedeqndv_1 p0000
  have p0002 := @gElex G (synCfuns)
  have p0003 := Nominal.mp hyp_wppgammatchwboundedeqndv_3 p0002
  have p0004 := @gHwcardstcclndv C
  have p0005 := Nominal.mp hyp_wppgammatchwboundedeqndv_8 p0004
  have p0006 :=
    @gWppcandtchwboundedimagebindv x C k F G r p d dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 hyp_wppgammatchwboundedeqndv_1
      hyp_wppgammatchwboundedeqndv_2 hyp_wppgammatchwboundedeqndv_3
      hyp_wppgammatchwboundedeqndv_4 hyp_wppgammatchwboundedeqndv_5
      hyp_wppgammatchwboundedeqndv_6 hyp_wppgammatchwboundedeqndv_7
      hyp_wppgammatchwboundedeqndv_8
  have p0007 :=
    (Nominal.biimpRefl (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d)))))
  have p0008 :=
    @gBitr4i (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWex d (synWa (.classMem (.cv d) (synCwppcand F C))
          (.classEq (.cv k) (synCtc (.cv d)))))
      (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d)))) p0006 p0007
  have p0009 := Nominal.gen p0008 k
  have p0010 :=
    @gWppgammaimagetceqndv C k F G d dv_cache_0001 dv_cache_0023 dv_cache_0005
      dv_cache_0024 dv_cache_0009 dv_cache_0025 dv_cache_0013 p0001
      hyp_wppgammatchwboundedeqndv_8 p0003 p0005 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wppgammadomhwndv`. -/
@[expose]
noncomputable def gWppgammadomhwndv (C : Class) (F : Class) (p : Var) (dv_C_p : p ∉ C.fv)
    (dv_F_p : p ∉ F.fv) (hyp_wppgammadomhwndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppgammadomhwndv_2 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))))
    (hyp_wppgammadomhwndv_3 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf (.classMem (synCwppgamma F C) (synCdm F)) :=
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
  have dv_cache_0003 : p ∉ ((synCwppgamma F C)).fv :=
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
  have dv_cache_0004 : p ∉ ((synChwcards (synCvv))).fv :=
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
      ((Wff.imp (synWbr (synCwppgamma F C) (synClec) C)
          (.classMem (synCwppgamma F C) (synCdm F)))).fv :=
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
    @gPm32i (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv)))
      hyp_wppgammadomhwndv_1 hyp_wppgammadomhwndv_3
  have p0001 := @gWppgammaminhwndv C k F dv_cache_0001 dv_cache_0002
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gSimpl (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gElwppcand C (synCwppgamma F C) F
  have p0006 :=
    @gBiimpi (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWa (synWa (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
          (synWbr (synCwppgamma F C) (synClec) C))
        (.classMem (synCwppgamma F C) (synCwppreach F C)))
      p0005
  have p0007 := Nominal.mp p0004 p0006
  have p0008 :=
    @gSimpl
      (synWa (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
        (synWbr (synCwppgamma F C) (synClec) C))
      (.classMem (synCwppgamma F C) (synCwppreach F C))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gSimpr (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
      (synWbr (synCwppgamma F C) (synClec) C)
  have p0011 := Nominal.mp p0009 p0010
  have p0022 :=
    @gSimpl (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
      (synWbr (synCwppgamma F C) (synClec) C)
  have p0023 := Nominal.mp p0009 p0022
  have p0024 :=
    @gPm32i (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
      (synWral p (synChwcards (synCvv))
        (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F))))
      p0023 hyp_wppgammadomhwndv_2
  have p0025 := @gId (.classEq (.cv p) (synCwppgamma F C))
  have p0026 :=
    @gBreq1d (.classEq (.cv p) (synCwppgamma F C)) (.cv p) (synCwppgamma F C) C
      (synClec) p0025
  have p0028 :=
    @gEleq1d (.classEq (.cv p) (synCwppgamma F C)) (.cv p) (synCwppgamma F C)
      (synCdm F) p0025
  have p0029 :=
    @gImbi12d (.classEq (.cv p) (synCwppgamma F C)) (synWbr (.cv p) (synClec) C)
      (synWbr (synCwppgamma F C) (synClec) C) (.classMem (.cv p) (synCdm F))
      (.classMem (synCwppgamma F C) (synCdm F)) p0026 p0028
  have p0030 :=
    @gRspcva (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))
      (.imp (synWbr (synCwppgamma F C) (synClec) C)
        (.classMem (synCwppgamma F C) (synCdm F)))
      p (synCwppgamma F C) (synChwcards (synCvv)) dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0029
  have p0031 := Nominal.mp p0024 p0030
  have p0032 := Nominal.mp p0011 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_wppgammareachexhwndv`. -/
@[expose]
noncomputable def gWppgammareachexhwndv (C : Class) (n : Var) (F : Class) (p : Var)
    (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv)
    (_dv_n_p : n ≠ p)
    (hyp_wppgammareachexhwndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppgammareachexhwndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppgammareachexhwndv_3 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))))
    (hyp_wppgammareachexhwndv_4 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWrex n (synCnnc)
        (synWbr C (synClec) (synCfv (synCfrec F (synCwppgamma F C)) (.cv n)))) :=
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
  have dv_cache_0004 : n ∉ ((synCwppgamma F C)).fv :=
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
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wppgammareachexhwndv_1 p0000
  have p0002 := @gWppgammareachndv C F p0001 hyp_wppgammareachexhwndv_4
  have p0005 :=
    @gWppgammadomhwndv C F p dv_cache_0001 dv_cache_0002 p0001 hyp_wppgammareachexhwndv_3
      hyp_wppgammareachexhwndv_4
  have p0006 := @gElex C (synChwcards (synCvv))
  have p0007 := Nominal.mp hyp_wppgammareachexhwndv_4 p0006
  have p0008 :=
    @gWppreachfwdrexvndv C (synCwppgamma F C) n F dv_cache_0003 dv_cache_0004
      dv_cache_0005 hyp_wppgammareachexhwndv_1 p0005 hyp_wppgammareachexhwndv_2 p0007
  have p0009 :=
    @gBiimpi (.classMem (synCwppgamma F C) (synCwppreach F C))
      (synWrex n (synCnnc)
        (synWbr C (synClec) (synCfv (synCfrec F (synCwppgamma F C)) (.cv n))))
      p0008
  have p0010 := Nominal.mp p0002 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wppgammaleasthithwndv`. -/
@[expose]
noncomputable def gWppgammaleasthithwndv (C : Class) (m : Var) (n : Var) (F : Class)
    (p : Var) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_m_n : m ≠ n)
    (hyp_wppgammaleasthithwndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppgammaleasthithwndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppgammaleasthithwndv_3 : Nominal.NPrf (synWral p (synChwcards (synCvv))
          (.imp (synWbr (.cv p) (synClec) C) (.classMem (.cv p) (synCdm F)))))
    (hyp_wppgammaleasthithwndv_4 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf
      (synWrex m (synCnnc) (synWa (.classMem (.cv m) (synCwpphit F (synCwppgamma F C) C))
          (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F (synCwppgamma F C) C))
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))))) :=
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
  have dv_cache_0010 : m ∉ ((synCwppgamma F C)).fv :=
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
  have dv_cache_0011 : n ∉ ((synCwppgamma F C)).fv :=
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
  have dv_cache_0012 : q ∉ ((synCwppgamma F C)).fv :=
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
  have dv_cache_0013 : m ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0014 : n ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0015 : q ∉ ((synCkqrel (synClefin))).fv :=
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
  have p0000 := @gFinlewe
  have p0001 :=
    @gWppgammareachexhwndv C q F p dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_wppgammaleasthithwndv_1 hyp_wppgammaleasthithwndv_2
      hyp_wppgammaleasthithwndv_3 hyp_wppgammaleasthithwndv_4
  have p0002 := @gElex F (synCfuns)
  have p0003 := Nominal.mp hyp_wppgammaleasthithwndv_1 p0002
  have p0004 :=
    @gWppgammadomhwndv C F p dv_cache_0002 dv_cache_0004 p0003
      hyp_wppgammaleasthithwndv_3 hyp_wppgammaleasthithwndv_4
  have p0005 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem (synCwppgamma F C) (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wppgammaleasthithwndv_1 p0004
      hyp_wppgammaleasthithwndv_2
  have p0006 := @gElwpphitvndv C F (synCwppgamma F C) (.cv q)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gBiimpri (.classMem (.cv q) (synCwpphit F (synCwppgamma F C) C))
      (synWa (.classMem (.cv q) (synCnnc))
        (synWbr C (synClec) (synCfv (synCfrec F (synCwppgamma F C)) (.cv q))))
      p0007
  have p0009 :=
    @gExpcom (.classMem (.cv q) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F (synCwppgamma F C)) (.cv q)))
      (.classMem (.cv q) (synCwpphit F (synCwppgamma F C) C)) p0008
  have p0010 :=
    @gCom12 (synWbr C (synClec) (synCfv (synCfrec F (synCwppgamma F C)) (.cv q)))
      (.classMem (.cv q) (synCnnc))
      (.classMem (.cv q) (synCwpphit F (synCwppgamma F C) C)) p0009
  have p0011 :=
    @gReximia (synWbr C (synClec) (synCfv (synCfrec F (synCwppgamma F C)) (.cv q)))
      (.classMem (.cv q) (synCwpphit F (synCwppgamma F C) C)) q (synCnnc) p0010
  have p0012 := Nominal.mp p0001 p0011
  have p0013 :=
    @gPm32i (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWrex q (synCnnc) (.classMem (.cv q) (synCwpphit F (synCwppgamma F C) C)))
      p0000 p0012
  have p0016 :=
    @gWpphitminexvndv q C (synCkqrel (synClefin)) m n F (synCwppgamma F C)
      dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0003
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 p0003
  have p0017 := Nominal.mp p0013 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end
