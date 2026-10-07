/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wpppostcompfv`. -/
@[expose]
noncomputable def gWpppostcompfv (R : Class) (F : Class)
    (hyp_wpppostcompfv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wpppostcompfv_2 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCwpppostcomp F) R) (synCcom F R)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppostcomp F))
  have p0001 :=
    @gFveq1i R (synCwpppostcomp F)
      (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))) p0000
  have p0002 := @gFnconstg (synCvv) F (synCvv)
  have p0003 := Nominal.mp hyp_wpppostcompfv_1 p0002
  have p0004 := @gF1ovi
  have p0005 := @gF1ofn (synCvv) (synCvv) (synCid)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gPm32i (synWfn (synCxp (synCvv) (synCsn F)) (synCvv))
      (synWfn (synCid) (synCvv)) p0003 p0006
  have p0008 := @gFntxp (synCvv) (synCvv) (synCxp (synCvv) (synCsn F)) (synCid)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gInidm (synCvv)
  have p0011 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) p0010
  have p0012 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) (synCvv)) p0009 p0011
  have p0013 :=
    @gPm32i (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) (synCvv))
      (.classMem R (synCvv)) p0012 hyp_wpppostcompfv_2
  have p0014 :=
    @gFvco2 (synCvv) R (synCcompose)
      (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))
  have p0015 := Nominal.mp p0013 p0014
  have p0021 :=
    @gFvtxpvv R (synCxp (synCvv) (synCsn F)) (synCid) p0003 p0006 hyp_wpppostcompfv_2
  have p0022 := @gFvconst2 (synCvv) F R hyp_wpppostcompfv_1
  have p0023 := Nominal.mp hyp_wpppostcompfv_2 p0022
  have p0024 := @gFvi R (synCvv)
  have p0025 := Nominal.mp hyp_wpppostcompfv_2 p0024
  have p0026 :=
    @gOpeq12i (synCfv (synCxp (synCvv) (synCsn F)) R) F (synCfv (synCid) R) R p0023
      p0025
  have p0027 :=
    @gEqtri (synCfv (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) R)
      (synCop (synCfv (synCxp (synCvv) (synCsn F)) R) (synCfv (synCid) R))
      (synCop F R) p0021 p0026
  have p0028 :=
    @gFveq2i (synCfv (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) R)
      (synCop F R) (synCcompose) p0027
  have p0029 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))) R)
      (synCfv (synCcompose) (synCfv (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) R))
      (synCfv (synCcompose) (synCop F R)) p0015 p0028
  have p0030 := (Nominal.classEqRefl (synCo F (synCcompose) R))
  have p0031 :=
    @gEqcomi (synCo F (synCcompose) R) (synCfv (synCcompose) (synCop F R)) p0030
  have p0032 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))) R)
      (synCfv (synCcompose) (synCop F R)) (synCo F (synCcompose) R) p0029 p0031
  have p0033 :=
    @gPm32i (.classMem F (synCvv)) (.classMem R (synCvv)) hyp_wpppostcompfv_1
      hyp_wpppostcompfv_2
  have p0034 := @gComposevalg F R (synCvv) (synCvv)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))) R)
      (synCo F (synCcompose) R) (synCcom F R) p0032 p0035
  have p0037 :=
    @gEqtri (synCfv (synCwpppostcomp F) R)
      (synCfv (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))) R)
      (synCcom F R) p0001 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_wppupperpreopfn`. -/
@[expose]
noncomputable def gWppupperpreopfn (C : Class) :
    Nominal.NPrf (synWfn (synCwppupperpreop C) (synCvv)) :=
  by
  have p0000 := @gLnimageopfn
  have p0001 := @gImageswapfn
  have p0002 := @gWppreachupperex C
  have p0003 := @gFnconstg (synCvv) (synCima (synClec) (synCsn C)) (synCvv)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gPm32i (synWfn (synCimage (synCswap)) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))) (synCvv))
      p0001 p0004
  have p0006 :=
    @gFntxp (synCvv) (synCvv) (synCimage (synCswap))
      (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gInidm (synCvv)
  have p0009 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCimage (synCswap))
        (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
      p0008
  have p0010 :=
    @gMpbi
      (synWfn (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))) (synCvv))
      p0007 p0009
  have p0011 :=
    @gFncovv (synClnimageop)
      (synCtxp (synCimage (synCswap))
        (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
      p0000 p0010
  have p0012 := (Nominal.classEqRefl (synCwppupperpreop C))
  have p0013 :=
    @gFneq1i (synCvv) (synCwppupperpreop C)
      (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))))
      p0012
  have p0014 :=
    @gMpbir (synWfn (synCwppupperpreop C) (synCvv))
      (synWfn (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
            (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))) (synCvv))
      p0011 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_wppimageswapfv`. -/
@[expose]
noncomputable def gWppimageswapfv (R : Class)
    (hyp_wppimageswapfv_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCimage (synCswap)) R) (synCcnv R)) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0002 :
    x ∉ ((Wff.classEq (synCfv (synCimage (synCswap)) R) (synCcnv R))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gId (.classEq (.cv x) R)
  have p0001 := @gFveq2d (.classEq (.cv x) R) (.cv x) R (synCimage (synCswap)) p0000
  have p0003 := @gCnveqd (.classEq (.cv x) R) (.cv x) R p0000
  have p0004 :=
    @gEqeq12d (.classEq (.cv x) R) (synCfv (synCimage (synCswap)) (.cv x))
      (synCfv (synCimage (synCswap)) R) (synCcnv (.cv x)) (synCcnv R) p0001 p0003
  have p0005 := @gImageswapval x
  have p0006 :=
    @gVtoclg (.classEq (synCfv (synCimage (synCswap)) (.cv x)) (synCcnv (.cv x)))
      (.classEq (synCfv (synCimage (synCswap)) R) (synCcnv R)) x R (synCvv)
      dv_cache_0001 dv_cache_0002 p0004 p0005
  have p0007 := Nominal.mp hyp_wppimageswapfv_1 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppupperpreopfv`. -/
@[expose]
noncomputable def gWppupperpreopfv (C : Class) (R : Class)
    (hyp_wppupperpreopfv_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppupperpreop C) R)
        (synCima (synCcnv R) (synCima (synClec) (synCsn C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppupperpreop C))
  have p0001 :=
    @gFveq1i R (synCwppupperpreop C)
      (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))))
      p0000
  have p0002 := @gImageswapfn
  have p0003 := @gWppreachupperex C
  have p0004 := @gFnconstg (synCvv) (synCima (synClec) (synCsn C)) (synCvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i (synWfn (synCimage (synCswap)) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))) (synCvv))
      p0002 p0005
  have p0007 :=
    @gFntxp (synCvv) (synCvv) (synCimage (synCswap))
      (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gInidm (synCvv)
  have p0010 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCimage (synCswap))
        (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
      p0009
  have p0011 :=
    @gMpbi
      (synWfn (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))) (synCvv))
      p0008 p0010
  have p0012 :=
    @gPm32i
      (synWfn (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))) (synCvv))
      (.classMem R (synCvv)) p0011 hyp_wppupperpreopfv_1
  have p0013 :=
    @gFvco2 (synCvv) R (synClnimageop)
      (synCtxp (synCimage (synCswap))
        (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
  have p0014 := Nominal.mp p0012 p0013
  have p0019 :=
    @gFvtxpvv R (synCimage (synCswap))
      (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))) p0002 p0005
      hyp_wppupperpreopfv_1
  have p0020 := @gWppimageswapfv R hyp_wppupperpreopfv_1
  have p0022 := @gFvconst2 (synCvv) (synCima (synClec) (synCsn C)) R p0003
  have p0023 := Nominal.mp hyp_wppupperpreopfv_1 p0022
  have p0024 :=
    @gOpeq12i (synCfv (synCimage (synCswap)) R) (synCcnv R)
      (synCfv (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))) R)
      (synCima (synClec) (synCsn C)) p0020 p0023
  have p0025 :=
    @gEqtri
      (synCfv (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))) R)
      (synCop (synCfv (synCimage (synCswap)) R)
        (synCfv (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))) R))
      (synCop (synCcnv R) (synCima (synClec) (synCsn C))) p0019 p0024
  have p0026 :=
    @gFveq2i
      (synCfv (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))) R)
      (synCop (synCcnv R) (synCima (synClec) (synCsn C))) (synClnimageop) p0025
  have p0027 :=
    @gEqtri
      (synCfv (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
            (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))) R)
      (synCfv (synClnimageop) (synCfv (synCtxp (synCimage (synCswap))
            (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))) R))
      (synCfv (synClnimageop) (synCop (synCcnv R) (synCima (synClec) (synCsn C))))
      p0014 p0026
  have p0028 := @gCnvex R hyp_wppupperpreopfv_1
  have p0030 := @gLnimageopval (synCima (synClec) (synCsn C)) (synCcnv R) p0028 p0003
  have p0031 :=
    @gEqtri
      (synCfv (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
            (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))) R)
      (synCfv (synClnimageop) (synCop (synCcnv R) (synCima (synClec) (synCsn C))))
      (synCima (synCcnv R) (synCima (synClec) (synCsn C))) p0027 p0030
  have p0032 :=
    @gEqtri (synCfv (synCwppupperpreop C) R)
      (synCfv (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
            (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))) R)
      (synCima (synCcnv R) (synCima (synClec) (synCsn C))) p0001 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerseqfun`. -/
@[expose]
noncomputable def gWpppowlayerseqfun (C : Class) (F : Class)
    (hyp_wpppowlayerseqfun_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfun (synCwpppowlayerseq F C)) :=
  by
  have p0000 := @gWppupperpreopfn C
  have p0001 := @gFnfun (synCvv) (synCwppupperpreop C)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gWpppostcompfn F hyp_wpppowlayerseqfun_1
  have p0004 := @gFnfun (synCvv) (synCwpppostcomp F)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gWpppostcompex F hyp_wpppowlayerseqfun_1
  have p0007 := @gElfuns (synCwpppostcomp F) p0006
  have p0008 :=
    @gMpbir (.classMem (synCwpppostcomp F) (synCfuns)) (synWfun (synCwpppostcomp F))
      p0005 p0007
  have p0009 := @gIdex
  have p0011 := @gFndm (synCvv) (synCwpppostcomp F)
  have p0012 := Nominal.mp p0003 p0011
  have p0013 := @gEleqtrri (synCid) (synCvv) (synCdm (synCwpppostcomp F)) p0009 p0012
  have p0014 := @gSsv (synCrn (synCwpppostcomp F))
  have p0018 :=
    @gSseqtr4i (synCrn (synCwpppostcomp F)) (synCvv) (synCdm (synCwpppostcomp F))
      p0014 p0012
  have p0019 :=
    @gN3pm32i (.classMem (synCwpppostcomp F) (synCfuns))
      (.classMem (synCid) (synCdm (synCwpppostcomp F)))
      (synWss (synCrn (synCwpppostcomp F)) (synCdm (synCwpppostcomp F))) p0008 p0013
      p0018
  have p0020 := @gWpporbitfnndv (synCwpppostcomp F) (synCid)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gFnfun (synCnnc) (synCfrec (synCwpppostcomp F) (synCid))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @gFntcfn
  have p0025 := @gFnfun (synC1c) (synCtcfn)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gPm32i (synWfun (synCfrec (synCwpppostcomp F) (synCid))) (synWfun (synCtcfn))
      p0023 p0026
  have p0028 := @gFunco (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @gPm32i (synWfun (synCwppupperpreop C))
      (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) p0002
      p0029
  have p0031 :=
    @gFunco (synCwppupperpreop C)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := (Nominal.classEqRefl (synCwpppowlayerseq F C))
  have p0034 :=
    @gFuneqi (synCwpppowlayerseq F C)
      (synCcom (synCwppupperpreop C)
        (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      p0033
  have p0035 :=
    @gMpbir (synWfun (synCwpppowlayerseq F C))
      (synWfun (synCcom (synCwppupperpreop C)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      p0032 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_wpphitfamfv`. -/
@[expose]
noncomputable def gWpphitfamfv (C : Class) (D : Class) (F : Class)
    (hyp_wpphitfamfv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpphitfam F C) (synCsn (synCsn D)))
        (synCima (synCcnv (synCwpppowlayerseq F C))
          (synCima (synCsset) (synCsn (synCsn D))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphitfam F C))
  have p0001 :=
    @gFveq1i (synCsn (synCsn D)) (synCwpphitfam F C)
      (synCcom (synCimage (synCcnv (synCwpppowlayerseq F C))) (synCimage (synCsset)))
      p0000
  have p0002 := @gWppimagefun (synCsset)
  have p0003 := @gEqid (synCima (synCsset) (synCsn (synCsn D)))
  have p0004 := @gSnex (synCsn D)
  have p0005 := @gSsetex
  have p0007 := @gImaex (synCsset) (synCsn (synCsn D)) p0005 p0004
  have p0008 :=
    @gBrimage (synCsn (synCsn D)) (synCima (synCsset) (synCsn (synCsn D)))
      (synCsset) p0004 p0007
  have p0009 :=
    @gMpbir
      (synWbr (synCsn (synCsn D)) (synCimage (synCsset))
        (synCima (synCsset) (synCsn (synCsn D))))
      (.classEq (synCima (synCsset) (synCsn (synCsn D)))
        (synCima (synCsset) (synCsn (synCsn D))))
      p0003 p0008
  have p0010 :=
    @gBreldm (synCsn (synCsn D)) (synCima (synCsset) (synCsn (synCsn D)))
      (synCimage (synCsset))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gPm32i (synWfun (synCimage (synCsset)))
      (.classMem (synCsn (synCsn D)) (synCdm (synCimage (synCsset)))) p0002 p0011
  have p0013 :=
    @gFvco (synCsn (synCsn D)) (synCimage (synCcnv (synCwpppowlayerseq F C)))
      (synCimage (synCsset))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gEqtri (synCfv (synCwpphitfam F C) (synCsn (synCsn D)))
      (synCfv (synCcom (synCimage (synCcnv (synCwpppowlayerseq F C)))
          (synCimage (synCsset))) (synCsn (synCsn D)))
      (synCfv (synCimage (synCcnv (synCwpppowlayerseq F C)))
        (synCfv (synCimage (synCsset)) (synCsn (synCsn D))))
      p0001 p0014
  have p0018 := @gWppimagefv (synCsn (synCsn D)) (synCsset) p0005 p0004
  have p0019 :=
    @gFveq2i (synCfv (synCimage (synCsset)) (synCsn (synCsn D)))
      (synCima (synCsset) (synCsn (synCsn D)))
      (synCimage (synCcnv (synCwpppowlayerseq F C))) p0018
  have p0020 :=
    @gEqtri (synCfv (synCwpphitfam F C) (synCsn (synCsn D)))
      (synCfv (synCimage (synCcnv (synCwpppowlayerseq F C)))
        (synCfv (synCimage (synCsset)) (synCsn (synCsn D))))
      (synCfv (synCimage (synCcnv (synCwpppowlayerseq F C)))
        (synCima (synCsset) (synCsn (synCsn D))))
      p0015 p0019
  have p0021 := @gWpppowlayerseqex C F hyp_wpphitfamfv_1
  have p0022 := @gCnvex (synCwpppowlayerseq F C) p0021
  have p0026 :=
    @gWppimagefv (synCima (synCsset) (synCsn (synCsn D)))
      (synCcnv (synCwpppowlayerseq F C)) p0022 p0007
  have p0027 :=
    @gEqtri (synCfv (synCwpphitfam F C) (synCsn (synCsn D)))
      (synCfv (synCimage (synCcnv (synCwpppowlayerseq F C)))
        (synCima (synCsset) (synCsn (synCsn D))))
      (synCima (synCcnv (synCwpppowlayerseq F C))
        (synCima (synCsset) (synCsn (synCsn D))))
      p0020 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_elwpphitfam`. -/
@[expose]
noncomputable def gElwpphitfam (C : Class) (D : Class) (F : Class) (q : Var)
    (hyp_elwpphitfam_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_elwpphitfam_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv q)) (synCfv (synCwpphitfam F C) (synCsn (synCsn D))))
        (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ ({ q } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_q : y ≠ q := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem D (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCima (synCsset) (synCsn (synCsn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_z_not_D, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cab y (.classMem D (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_ne_y, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, fresh_y_not_C, fresh_y_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((Wff.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_q, fresh_y_not_C, fresh_y_not_F,
          or_false, not_false_eq_true])
  have p0000 := @gWpphitfamfv C D F hyp_elwpphitfam_1
  have p0001 :=
    @gEleq2i (synCfv (synCwpphitfam F C) (synCsn (synCsn D)))
      (synCima (synCcnv (synCwpppowlayerseq F C))
        (synCima (synCsset) (synCsn (synCsn D))))
      (synCsn (.cv q)) p0000
  have p0002 := @gElimasn (synCsset) (synCsn D) (.cv z)
  have p0003 := (Nominal.biimpRefl (synWbr (synCsn D) (synCsset) (.cv z)))
  have p0004 :=
    @gBicomi (synWbr (synCsn D) (synCsset) (.cv z))
      (.classMem (synCop (synCsn D) (.cv z)) (synCsset)) p0003
  have p0005 :=
    @gBitri (.classMem (.cv z) (synCima (synCsset) (synCsn (synCsn D))))
      (.classMem (synCop (synCsn D) (.cv z)) (synCsset))
      (synWbr (synCsn D) (synCsset) (.cv z)) p0002 p0004
  have p0006 := @gVex z
  have p0007 := @gBrssetsn D (.cv z) hyp_elwpphitfam_2 p0006
  have p0008 :=
    @gBitri (.classMem (.cv z) (synCima (synCsset) (synCsn (synCsn D))))
      (synWbr (synCsn D) (synCsset) (.cv z)) (.classMem D (.cv z)) p0005 p0007
  have p0010 := @gId (.classEq (.cv y) (.cv z))
  have p0011 := @gEleq2d (.classEq (.cv y) (.cv z)) (.cv y) (.cv z) D p0010
  have p0012 :=
    @gElab (.classMem D (.cv y)) (.classMem D (.cv z)) y (.cv z) dv_cache_0001
      dv_cache_0002 p0006 p0011
  have p0013 :=
    @gBitr4i (.classMem (.cv z) (synCima (synCsset) (synCsn (synCsn D))))
      (.classMem D (.cv z)) (.classMem (.cv z) (.cab y (.classMem D (.cv y)))) p0008 p0012
  have p0014 :=
    @gEqriv z (synCima (synCsset) (synCsn (synCsn D))) (.cab y (.classMem D (.cv y)))
      dv_cache_0003 dv_cache_0004 p0013
  have p0015 :=
    @gImaeq2i (synCima (synCsset) (synCsn (synCsn D))) (.cab y (.classMem D (.cv y)))
      (synCcnv (synCwpppowlayerseq F C)) p0014
  have p0016 :=
    @gEleq2i
      (synCima (synCcnv (synCwpppowlayerseq F C))
        (synCima (synCsset) (synCsn (synCsn D))))
      (synCima (synCcnv (synCwpppowlayerseq F C)) (.cab y (.classMem D (.cv y))))
      (synCsn (.cv q)) p0015
  have p0017 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCfv (synCwpphitfam F C) (synCsn (synCsn D))))
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCwpppowlayerseq F C))
          (synCima (synCsset) (synCsn (synCsn D)))))
      (.classMem (synCsn (.cv q))
        (synCima (synCcnv (synCwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      p0001 p0016
  have p0018 := @gWpppowlayerseqfun C F hyp_elwpphitfam_1
  have p0019 := @gFunfn (synCwpppowlayerseq F C)
  have p0020 :=
    @gMpbi (synWfun (synCwpppowlayerseq F C))
      (synWfn (synCwpppowlayerseq F C) (synCdm (synCwpppowlayerseq F C))) p0018 p0019
  have p0021 :=
    @gElpreima (synCdm (synCwpppowlayerseq F C)) (synCsn (.cv q))
      (.cab y (.classMem D (.cv y))) (synCwpppowlayerseq F C)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @gFvex (synCsn (.cv q)) (synCwpppowlayerseq F C)
  have p0024 :=
    @gId (.classEq (.cv y) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))))
  have p0025 :=
    @gEleq2d (.classEq (.cv y) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))))
      (.cv y) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))) D p0024
  have p0026 :=
    @gElab (.classMem D (.cv y))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))) y
      (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))) dv_cache_0005 dv_cache_0006
      p0023 p0025
  have p0027 := @gElfvdm D (synCsn (.cv q)) (synCwpppowlayerseq F C)
  have p0028 :=
    @gSylbi
      (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q))))
      (.classMem (synCsn (.cv q)) (synCdm (synCwpppowlayerseq F C))) p0026 p0027
  have p0029 :=
    @gPm471ri
      (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (.classMem (synCsn (.cv q)) (synCdm (synCwpppowlayerseq F C))) p0028
  have p0030 :=
    @gBicomi
      (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (synWa (.classMem (synCsn (.cv q)) (synCdm (synCwpppowlayerseq F C)))
        (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
          (.cab y (.classMem D (.cv y)))))
      p0029
  have p0031 :=
    @gBitri
      (.classMem (synCsn (.cv q))
        (synCima (synCcnv (synCwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      (synWa (.classMem (synCsn (.cv q)) (synCdm (synCwpppowlayerseq F C)))
        (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
          (.cab y (.classMem D (.cv y)))))
      (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      p0022 p0030
  have p0036 :=
    @gBitri
      (.classMem (synCsn (.cv q))
        (synCima (synCcnv (synCwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      (.classMem (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))) p0031 p0026
  have p0037 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCfv (synCwpphitfam F C) (synCsn (synCsn D))))
      (.classMem (synCsn (.cv q))
        (synCima (synCcnv (synCwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv q)))) p0017 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_wpppredmemrelex`. -/
@[expose]
noncomputable def gWpppredmemrelex (C : Class) (F : Class)
    (hyp_wpppredmemrelex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpppredmemrel F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppredmemrel F C))
  have p0001 := @gSsetex
  have p0002 := @gCnvex (synCsset) p0001
  have p0003 := @gWpppredfamex C F hyp_wpppredmemrelex_1
  have p0004 := @gCoex (synCcnv (synCsset)) (synCwpppredfam F C) p0002 p0003
  have p0005 :=
    @gEqeltri (synCwpppredmemrel F C)
      (synCcom (synCcnv (synCsset)) (synCwpppredfam F C)) (synCvv) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wpphitmemrelex`. -/
@[expose]
noncomputable def gWpphitmemrelex (C : Class) (F : Class)
    (hyp_wpppredmemrelex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpphitmemrel F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphitmemrel F C))
  have p0001 := @gSsetex
  have p0002 := @gCnvex (synCsset) p0001
  have p0003 := @gWpphitfamex C F hyp_wpppredmemrelex_1
  have p0004 := @gCoex (synCcnv (synCsset)) (synCwpphitfam F C) p0002 p0003
  have p0005 :=
    @gEqeltri (synCwpphitmemrel F C)
      (synCcom (synCcnv (synCsset)) (synCwpphitfam F C)) (synCvv) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppreachincbex`. -/
@[expose]
noncomputable def gWppreachincbex (C : Class) (F : Class)
    (hyp_wppreachincbex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwppreachincb F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppreachincb F C))
  have p0001 := @gNncex
  have p0002 := @gPw1ex (synCnnc) p0001
  have p0003 := @gPw1ex (synCpw1 (synCnnc)) p0002
  have p0004 := @gWpppredmemrelex C F hyp_wppreachincbex_1
  have p0005 := @gWpphitmemrelex C F hyp_wppreachincbex_1
  have p0006 := @gSymdifex (synCwpppredmemrel F C) (synCwpphitmemrel F C) p0004 p0005
  have p0007 := @gDmex F hyp_wppreachincbex_1
  have p0008 := @gPw1ex (synCdm F) p0007
  have p0009 := @gPw1ex (synCpw1 (synCdm F)) p0008
  have p0010 :=
    @gResex (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
      (synCpw1 (synCpw1 (synCdm F))) p0006 p0009
  have p0011 :=
    @gRnex
      (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
        (synCpw1 (synCpw1 (synCdm F))))
      p0010
  have p0012 :=
    @gDifex (synCpw1 (synCpw1 (synCnnc)))
      (synCrn (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
          (synCpw1 (synCpw1 (synCdm F)))))
      p0003 p0011
  have p0013 :=
    @gUni1ex
      (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))
      p0012
  have p0014 :=
    @gUni1ex
      (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0013
  have p0015 :=
    @gEqeltri (synCwppreachincb F C)
      (synCuni1 (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      (synCvv) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_elwppreachincb`. -/
@[expose]
noncomputable def gElwppreachincb (C : Class) (F : Class) (N : Class)
    (_dv_C_F : Disjoint C.fv F.fv) (_dv_C_N : Disjoint C.fv N.fv)
    (_dv_F_N : Disjoint F.fv N.fv) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (synWb (.classMem N (synCwppreachincb F C)) (.neg
            (.classMem (synCsn (synCsn N)) (synCrn
                (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                  (synCpw1 (synCpw1 (synCdm F))))))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppreachincb F C))
  have p0001 :=
    @gEleq2i (synCwppreachincb F C)
      (synCuni1 (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      N p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem N (synCwppreachincb F C)) (.classMem N (synCuni1 (synCuni1
              (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
                  (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                    (synCpw1 (synCpw1 (synCdm F))))))))))
      (.classMem N (synCnnc)) p0001
  have p0003 :=
    @gEluni1g N
      (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (synCnnc)
  have p0004 := @gId (.classMem N (synCnnc))
  have p0005 := @gSnelpw1 N (synCnnc)
  have p0006 :=
    @gSylibr (.classMem N (synCnnc)) (.classMem N (synCnnc))
      (.classMem (synCsn N) (synCpw1 (synCnnc))) p0004 p0005
  have p0007 :=
    @gEluni1g (synCsn N)
      (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))
      (synCpw1 (synCnnc))
  have p0008 :=
    @gSyl (.classMem N (synCnnc)) (.classMem (synCsn N) (synCpw1 (synCnnc)))
      (synWb (.classMem (synCsn N) (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc)))
              (synCrn (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                  (synCpw1 (synCpw1 (synCdm F)))))))) (.classMem (synCsn (synCsn N))
          (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      p0006 p0007
  have p0009 :=
    @gBitrd (.classMem N (synCnnc))
      (.classMem N (synCuni1 (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
                (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                  (synCpw1 (synCpw1 (synCdm F)))))))))
      (.classMem (synCsn N) (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      (.classMem (synCsn (synCsn N)) (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0003 p0008
  have p0010 :=
    @gEldif (synCsn (synCsn N)) (synCpw1 (synCpw1 (synCnnc)))
      (synCrn (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
          (synCpw1 (synCpw1 (synCdm F)))))
  have p0011 := @gSnelpw1 (synCsn N) (synCpw1 (synCnnc))
  have p0013 :=
    @gBitri (.classMem (synCsn (synCsn N)) (synCpw1 (synCpw1 (synCnnc))))
      (.classMem (synCsn N) (synCpw1 (synCnnc))) (.classMem N (synCnnc)) p0011 p0005
  have p0014 :=
    @gAnbi1i (.classMem (synCsn (synCsn N)) (synCpw1 (synCpw1 (synCnnc))))
      (.classMem N (synCnnc))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0013
  have p0015 :=
    @gBitri
      (.classMem (synCsn (synCsn N)) (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (synWa (.classMem (synCsn (synCsn N)) (synCpw1 (synCpw1 (synCnnc)))) (.neg
          (.classMem (synCsn (synCsn N)) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      (synWa (.classMem N (synCnnc)) (.neg (.classMem (synCsn (synCsn N)) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      p0010 p0014
  have p0016 :=
    @gA1i
      (synWb (.classMem (synCsn (synCsn N)) (synCdif (synCpw1 (synCpw1 (synCnnc)))
            (synCrn (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))) (synWa (.classMem N (synCnnc)) (.neg
            (.classMem (synCsn (synCsn N)) (synCrn
                (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                  (synCpw1 (synCpw1 (synCdm F)))))))))
      (.classMem N (synCnnc)) p0015
  have p0018 :=
    @gBiantrurd (.classMem N (synCnnc)) (.classMem N (synCnnc))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0004
  have p0019 :=
    @gBicomd (.classMem N (synCnnc))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (synWa (.classMem N (synCnnc)) (.neg (.classMem (synCsn (synCsn N)) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      p0018
  have p0020 :=
    @gBitrd (.classMem N (synCnnc))
      (.classMem (synCsn (synCsn N)) (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (synWa (.classMem N (synCnnc)) (.neg (.classMem (synCsn (synCsn N)) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0016 p0019
  have p0021 :=
    @gBitrd (.classMem N (synCnnc))
      (.classMem N (synCuni1 (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
                (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                  (synCpw1 (synCpw1 (synCdm F)))))))))
      (.classMem (synCsn (synCsn N)) (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0009 p0020
  have p0022 :=
    @gBitrd (.classMem N (synCnnc)) (.classMem N (synCwppreachincb F C))
      (.classMem N (synCuni1 (synCuni1 (synCdif (synCpw1 (synCpw1 (synCnnc))) (synCrn
                (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                  (synCpw1 (synCpw1 (synCdm F)))))))))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      p0002 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_wppbrcofnv`. -/
@[expose]
noncomputable def gWppbrcofnv (A : Class) (B : Class) (R : Class) (H : Class)
    (_dv_A_R : Disjoint A.fv R.fv) (hyp_wppbrcofnv_1 : Nominal.NPrf (synWfn H (synCvv)))
    (hyp_wppbrcofnv_2 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (synWbr A (synCcom R H) B) (synWbr (synCfv H A) R B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ H.fv
  let x : Var := freshVar proofSupport 0
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_H : x ∉ H.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0004 : x ∉ (H).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_H, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCfv H A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_H, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synWbr (synCfv H A) R B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_H, fresh_x_not_B, fresh_x_not_R, or_false,
          not_false_eq_true])
  have p0000 := @gBrco x A B R H dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 := @gFnbrfvb (synCvv) A (.cv x) H
  have p0002 :=
    @gMp2an (synWfn H (synCvv)) (.classMem A (synCvv))
      (synWb (.classEq (synCfv H A) (.cv x)) (synWbr A H (.cv x))) hyp_wppbrcofnv_1
      hyp_wppbrcofnv_2 p0001
  have p0003 := @gBicomi (.classEq (synCfv H A) (.cv x)) (synWbr A H (.cv x)) p0002
  have p0004 :=
    @gAnbi1i (synWbr A H (.cv x)) (.classEq (synCfv H A) (.cv x)) (synWbr (.cv x) R B)
      p0003
  have p0005 := @gEqcom (synCfv H A) (.cv x)
  have p0006 :=
    @gAnbi1i (.classEq (synCfv H A) (.cv x)) (.classEq (.cv x) (synCfv H A))
      (synWbr (.cv x) R B) p0005
  have p0007 :=
    @gBitri (synWa (synWbr A H (.cv x)) (synWbr (.cv x) R B))
      (synWa (.classEq (synCfv H A) (.cv x)) (synWbr (.cv x) R B))
      (synWa (.classEq (.cv x) (synCfv H A)) (synWbr (.cv x) R B)) p0004 p0006
  have p0008 :=
    @gExbii (synWa (synWbr A H (.cv x)) (synWbr (.cv x) R B))
      (synWa (.classEq (.cv x) (synCfv H A)) (synWbr (.cv x) R B)) x p0007
  have p0009 := @gFvex A H
  have p0010 := @gBreq1 (.cv x) (synCfv H A) B R
  have p0011 :=
    @gCeqsexv (synWbr (.cv x) R B) (synWbr (synCfv H A) R B) x (synCfv H A)
      dv_cache_0005 dv_cache_0006 p0009 p0010
  have p0012 :=
    @gBitri (synWex x (synWa (synWbr A H (.cv x)) (synWbr (.cv x) R B)))
      (synWex x (synWa (.classEq (.cv x) (synCfv H A)) (synWbr (.cv x) R B)))
      (synWbr (synCfv H A) R B) p0008 p0011
  have p0013 :=
    @gBitri (synWbr A (synCcom R H) B)
      (synWex x (synWa (synWbr A H (.cv x)) (synWbr (.cv x) R B)))
      (synWbr (synCfv H A) R B) p0000 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wpppredfamfn`. -/
@[expose]
noncomputable def gWpppredfamfn (C : Class) (F : Class)
    (hyp_wpppredfamfn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfn (synCwpppredfam F C) (synCvv)) :=
  by
  have p0000 :=
    @gEqid (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0001 := @gCnvex F hyp_wpppredfamfn_1
  have p0002 := @gImageex (synCcnv F) p0001
  have p0003 :=
    @gFrecex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)) p0000 p0002
  have p0004 := @gTcfnex
  have p0005 :=
    @gCoex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCtcfn) p0003 p0004
  have p0006 :=
    @gCnvex
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
      p0005
  have p0007 :=
    @gWppimagefn
      (synCcnv
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))
      p0006
  have p0008 := @gSsetex
  have p0009 := @gWppimagefn (synCsset) p0008
  have p0010 :=
    @gFncovv
      (synCimage (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      (synCimage (synCsset)) p0007 p0009
  have p0011 := (Nominal.classEqRefl (synCwpppredfam F C))
  have p0012 :=
    @gFneq1i (synCvv) (synCwpppredfam F C)
      (synCcom (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCimage (synCsset)))
      p0011
  have p0013 :=
    @gMpbir (synWfn (synCwpppredfam F C) (synCvv))
      (synWfn (synCcom (synCimage (synCcnv (synCcom
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtcfn)))) (synCimage (synCsset))) (synCvv))
      p0010 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wpphitfamfn`. -/
@[expose]
noncomputable def gWpphitfamfn (C : Class) (F : Class)
    (hyp_wpppredfamfn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfn (synCwpphitfam F C) (synCvv)) :=
  by
  have p0000 := @gWpppowlayerseqex C F hyp_wpppredfamfn_1
  have p0001 := @gCnvex (synCwpppowlayerseq F C) p0000
  have p0002 := @gWppimagefn (synCcnv (synCwpppowlayerseq F C)) p0001
  have p0003 := @gSsetex
  have p0004 := @gWppimagefn (synCsset) p0003
  have p0005 :=
    @gFncovv (synCimage (synCcnv (synCwpppowlayerseq F C))) (synCimage (synCsset))
      p0002 p0004
  have p0006 := (Nominal.classEqRefl (synCwpphitfam F C))
  have p0007 :=
    @gFneq1i (synCvv) (synCwpphitfam F C)
      (synCcom (synCimage (synCcnv (synCwpppowlayerseq F C))) (synCimage (synCsset)))
      p0006
  have p0008 :=
    @gMpbir (synWfn (synCwpphitfam F C) (synCvv))
      (synWfn (synCcom (synCimage (synCcnv (synCwpppowlayerseq F C)))
          (synCimage (synCsset))) (synCvv))
      p0005 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part033`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppreachincbrng`. -/
@[expose]
noncomputable def gWppreachincbrng (C : Class) (F : Class) (N : Class) (d : Var)
    (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv)
    (hyp_wppreachincbrng_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (synWb (.neg (.classMem (synCsn (synCsn N)) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))) (synWral d (synCdm F) (synWb
            (.classMem (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
            (.classMem (synCsn N)
              (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))) :=
  by
  have dv_cache_0001 : d ∉ ((synCsn (synCsn N))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_N_d,
          not_false_eq_true])
  have dv_cache_0002 :
    d ∉ ((synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredmemrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitmemrel,
          Finset.mem_union, dv_C_d, dv_F_d, or_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((synCdm F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, dv_F_d,
          not_false_eq_true])
  have dv_cache_0004 :
    Disjoint ((synCsn (synCsn (.cv d)))).fv ((synCcnv (synCsset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((synCsn (synCsn (.cv d)))).fv ((synCcnv (synCsset))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
          exact
            (show Disjoint (((synCsn (.cv d))).fv) (((synCsset)).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint (((Class.cv d)).fv) (((synCsset)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ d } : Finset Var)) (((synCsset)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset];
                            exact
                              (show Disjoint (({ d } : Finset Var)) ((∅ : Finset Var))
                                from (by simp))))))))))
  have p0000 :=
    @gDfima3 (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
      (synCpw1 (synCpw1 (synCdm F)))
  have p0001 :=
    @gEleq2i
      (synCima (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
        (synCpw1 (synCpw1 (synCdm F))))
      (synCrn (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
          (synCpw1 (synCpw1 (synCdm F)))))
      (synCsn (synCsn N)) p0000
  have p0002 :=
    @gBicomi
      (.classMem (synCsn (synCsn N))
        (synCima (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
          (synCpw1 (synCpw1 (synCdm F)))))
      (.classMem (synCsn (synCsn N)) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))
      p0001
  have p0003 :=
    @gElimapw12 d (synCsn (synCsn N))
      (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C)) (synCdm F)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gBitri
      (.classMem (synCsn (synCsn N)) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))
      (.classMem (synCsn (synCsn N))
        (synCima (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
          (synCpw1 (synCpw1 (synCdm F)))))
      (synWrex d (synCdm F)
        (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
          (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))))
      p0002 p0003
  have p0005 :=
    @gElsymdif (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
      (synCwpppredmemrel F C) (synCwpphitmemrel F C)
  have p0006 :=
    (Nominal.biimpRefl (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C)
        (synCsn (synCsn N))))
  have p0007 :=
    (Nominal.biimpRefl
      (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C) (synCsn (synCsn N))))
  have p0008 :=
    @gBibi12i
      (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C) (synCsn (synCsn N)))
      (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
        (synCwpppredmemrel F C))
      (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C) (synCsn (synCsn N)))
      (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
        (synCwpphitmemrel F C))
      p0006 p0007
  have p0009 :=
    @gNotbii
      (synWb (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C)
          (synCsn (synCsn N))) (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C)
          (synCsn (synCsn N))))
      (synWb (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
          (synCwpppredmemrel F C))
        (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
          (synCwpphitmemrel F C)))
      p0008
  have p0010 :=
    @gBicomi
      (.neg (synWb (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C)
            (synCsn (synCsn N))) (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C)
            (synCsn (synCsn N)))))
      (.neg (synWb (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
            (synCwpppredmemrel F C))
          (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
            (synCwpphitmemrel F C))))
      p0009
  have p0011 :=
    @gBitri
      (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
        (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C)))
      (.neg (synWb (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
            (synCwpppredmemrel F C))
          (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
            (synCwpphitmemrel F C))))
      (.neg (synWb (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C)
            (synCsn (synCsn N))) (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C)
            (synCsn (synCsn N)))))
      p0005 p0010
  have p0012 := (Nominal.classEqRefl (synCwpppredmemrel F C))
  have p0013 :=
    @gBreqi (synCsn (synCsn (.cv d))) (synCsn (synCsn N)) (synCwpppredmemrel F C)
      (synCcom (synCcnv (synCsset)) (synCwpppredfam F C)) p0012
  have p0014 := @gWpppredfamfn C F hyp_wppreachincbrng_1
  have p0015 := @gSnex (synCsn (.cv d))
  have p0016 :=
    @gWppbrcofnv (synCsn (synCsn (.cv d))) (synCsn (synCsn N)) (synCcnv (synCsset))
      (synCwpppredfam F C) dv_cache_0004 p0014 p0015
  have p0017 :=
    @gBrcnv (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))
      (synCsn (synCsn N)) (synCsset)
  have p0018 := @gSnex N
  have p0019 := @gFvex (synCsn (synCsn (.cv d))) (synCwpppredfam F C)
  have p0020 :=
    @gBrssetsn (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))
      p0018 p0019
  have p0021 :=
    @gBitri
      (synWbr (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))
        (synCcnv (synCsset)) (synCsn (synCsn N)))
      (synWbr (synCsn (synCsn N)) (synCsset)
        (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
      (.classMem (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
      p0017 p0020
  have p0022 :=
    @gBitri
      (synWbr (synCsn (synCsn (.cv d)))
        (synCcom (synCcnv (synCsset)) (synCwpppredfam F C)) (synCsn (synCsn N)))
      (synWbr (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))
        (synCcnv (synCsset)) (synCsn (synCsn N)))
      (.classMem (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
      p0016 p0021
  have p0023 :=
    @gBitri
      (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C) (synCsn (synCsn N)))
      (synWbr (synCsn (synCsn (.cv d)))
        (synCcom (synCcnv (synCsset)) (synCwpppredfam F C)) (synCsn (synCsn N)))
      (.classMem (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
      p0013 p0022
  have p0024 := (Nominal.classEqRefl (synCwpphitmemrel F C))
  have p0025 :=
    @gBreqi (synCsn (synCsn (.cv d))) (synCsn (synCsn N)) (synCwpphitmemrel F C)
      (synCcom (synCcnv (synCsset)) (synCwpphitfam F C)) p0024
  have p0026 := @gWpphitfamfn C F hyp_wppreachincbrng_1
  have p0028 :=
    @gWppbrcofnv (synCsn (synCsn (.cv d))) (synCsn (synCsn N)) (synCcnv (synCsset))
      (synCwpphitfam F C) dv_cache_0004 p0026 p0015
  have p0029 :=
    @gBrcnv (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))
      (synCsn (synCsn N)) (synCsset)
  have p0031 := @gFvex (synCsn (synCsn (.cv d))) (synCwpphitfam F C)
  have p0032 :=
    @gBrssetsn (synCsn N) (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))
      p0018 p0031
  have p0033 :=
    @gBitri
      (synWbr (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))
        (synCcnv (synCsset)) (synCsn (synCsn N)))
      (synWbr (synCsn (synCsn N)) (synCsset)
        (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))
      (.classMem (synCsn N) (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))
      p0029 p0032
  have p0034 :=
    @gBitri
      (synWbr (synCsn (synCsn (.cv d)))
        (synCcom (synCcnv (synCsset)) (synCwpphitfam F C)) (synCsn (synCsn N)))
      (synWbr (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))
        (synCcnv (synCsset)) (synCsn (synCsn N)))
      (.classMem (synCsn N) (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))
      p0028 p0033
  have p0035 :=
    @gBitri
      (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C) (synCsn (synCsn N)))
      (synWbr (synCsn (synCsn (.cv d)))
        (synCcom (synCcnv (synCsset)) (synCwpphitfam F C)) (synCsn (synCsn N)))
      (.classMem (synCsn N) (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))
      p0025 p0034
  have p0036 :=
    @gBibi12i
      (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C) (synCsn (synCsn N)))
      (.classMem (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
      (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C) (synCsn (synCsn N)))
      (.classMem (synCsn N) (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))
      p0023 p0035
  have p0037 :=
    @gNotbii
      (synWb (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C)
          (synCsn (synCsn N))) (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C)
          (synCsn (synCsn N))))
      (synWb (.classMem (synCsn N)
          (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
          (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))
      p0036
  have p0038 :=
    @gBitri
      (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
        (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C)))
      (.neg (synWb (synWbr (synCsn (synCsn (.cv d))) (synCwpppredmemrel F C)
            (synCsn (synCsn N))) (synWbr (synCsn (synCsn (.cv d))) (synCwpphitmemrel F C)
            (synCsn (synCsn N)))))
      (.neg (synWb (.classMem (synCsn N)
            (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
            (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
      p0011 p0037
  have p0039 :=
    @gRexbii
      (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
        (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C)))
      (.neg (synWb (.classMem (synCsn N)
            (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
            (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
      d (synCdm F) p0038
  have p0040 :=
    @gBitri
      (.classMem (synCsn (synCsn N)) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))
      (synWrex d (synCdm F)
        (.classMem (synCop (synCsn (synCsn (.cv d))) (synCsn (synCsn N)))
          (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))))
      (synWrex d (synCdm F) (.neg (synWb (.classMem (synCsn N)
              (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
            (.classMem (synCsn N)
              (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))))
      p0004 p0039
  have p0041 :=
    @gNotbii
      (.classMem (synCsn (synCsn N)) (synCrn
          (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
            (synCpw1 (synCpw1 (synCdm F))))))
      (synWrex d (synCdm F) (.neg (synWb (.classMem (synCsn N)
              (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
            (.classMem (synCsn N)
              (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))))
      p0040
  have p0042 :=
    @gDfral2
      (synWb (.classMem (synCsn N)
          (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
          (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))
      d (synCdm F)
  have p0043 :=
    @gBicomi
      (synWral d (synCdm F) (synWb (.classMem (synCsn N)
            (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
            (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
      (.neg (synWrex d (synCdm F) (.neg (synWb (.classMem (synCsn N)
                (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
              (.classMem (synCsn N)
                (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))))
      p0042
  have p0044 :=
    @gBitri
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (.neg (synWrex d (synCdm F) (.neg (synWb (.classMem (synCsn N)
                (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
              (.classMem (synCsn N)
                (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))))
      (synWral d (synCdm F) (synWb (.classMem (synCsn N)
            (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
            (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
      p0041 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_elwppreachincball`. -/
@[expose]
noncomputable def gElwppreachincball (C : Class) (F : Class) (N : Class) (d : Var)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv) (dv_C_d : d ∉ C.fv)
    (dv_F_N : Disjoint F.fv N.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv)
    (hyp_elwppreachincball_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (synWb (.classMem N (synCwppreachincb F C))
          (synWral d (synCdm F) (synWb (.classMem (synCsn N)
                (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
              (.classMem (synCsn N)
                (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : Disjoint (C).fv (N).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv (N).fv from (show Disjoint (C).fv (N).fv from (by exact dv_C_N)))
  have dv_cache_0003 : Disjoint (F).fv (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (F).fv (N).fv from (show Disjoint (F).fv (N).fv from (by exact dv_F_N)))
  have dv_cache_0004 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_d, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_d, not_false_eq_true])
  have dv_cache_0006 : d ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_d, not_false_eq_true])
  have p0000 := @gElwppreachincb C F N dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gWppreachincbrng C F N d dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_elwppreachincball_1
  have p0002 :=
    @gA1i
      (synWb (.neg (.classMem (synCsn (synCsn N)) (synCrn
              (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
                (synCpw1 (synCpw1 (synCdm F))))))) (synWral d (synCdm F) (synWb
            (.classMem (synCsn N) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
            (.classMem (synCsn N)
              (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))))
      (.classMem N (synCnnc)) p0001
  have p0003 :=
    @gBitrd (.classMem N (synCnnc)) (.classMem N (synCwppreachincb F C))
      (.neg (.classMem (synCsn (synCsn N)) (synCrn
            (synCres (synCsymdif (synCwpppredmemrel F C) (synCwpphitmemrel F C))
              (synCpw1 (synCpw1 (synCdm F)))))))
      (synWral d (synCdm F) (synWb (.classMem (synCsn N)
            (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d))))) (.classMem (synCsn N)
            (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_wppreachincblayers`. -/
@[expose]
noncomputable def gWppreachincblayers (C : Class) (n : Var) (F : Class) (d : Var)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_C_n : n ∉ C.fv)
    (dv_F_d : d ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_d_n : d ≠ n)
    (hyp_wppreachincblayers_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwppreachincb F C))
          (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                  (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                  (synCtc (.cv n)))) (.classMem (.cv d)
                (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))))))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv n)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv ((Class.cv n)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ n } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show n ∉ (C).fv from (by exact dv_C_n))))))
  have dv_cache_0003 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_d, not_false_eq_true])
  have dv_cache_0004 : Disjoint (F).fv ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (F).fv ((Class.cv n)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((F).fv) (({ n } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show n ∉ (F).fv from (by exact dv_F_n))))))
  have dv_cache_0005 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_d, not_false_eq_true])
  have dv_cache_0006 : d ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_n,
          not_false_eq_true])
  have p0000 :=
    @gElwppreachincball C F (.cv n) d dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wppreachincblayers_1
  have p0001 := @gVex d
  have p0002 := @gElwpppredfam C (.cv d) F n hyp_wppreachincblayers_1 p0001
  have p0004 := @gElwpphitfam C (.cv d) F n hyp_wppreachincblayers_1 p0001
  have p0005 :=
    @gBibi12i
      (.classMem (synCsn (.cv n)) (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv n))))
      (.classMem (synCsn (.cv n)) (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))
      (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))) p0002
      p0004
  have p0006 :=
    @gRalbii
      (synWb (.classMem (synCsn (.cv n))
          (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
        (.classMem (synCsn (.cv n))
          (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d))))))
      (synWb (.classMem (.cv d)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv n))))
        (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))))
      d (synCdm F) p0005
  have p0007 :=
    @gA1i
      (synWb (synWral d (synCdm F) (synWb (.classMem (synCsn (.cv n))
              (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
            (.classMem (synCsn (.cv n))
              (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
        (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc (.cv n))))
            (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))))))
      (.classMem (.cv n) (synCnnc)) p0006
  have p0008 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwppreachincb F C))
      (synWral d (synCdm F) (synWb (.classMem (synCsn (.cv n))
            (synCfv (synCwpppredfam F C) (synCsn (synCsn (.cv d)))))
          (.classMem (synCsn (.cv n))
            (synCfv (synCwpphitfam F C) (synCsn (synCsn (.cv d)))))))
      (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv n))))
          (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))))
      p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wpppowcorefn`. -/
@[expose]
noncomputable def gWpppowcorefn (F : Class)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc)) :=
  by
  have p0000 := @gWpppostcompfn F hyp_wpppowcorefn_1
  have p0001 := @gFnfun (synCvv) (synCwpppostcomp F)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gWpppostcompex F hyp_wpppowcorefn_1
  have p0004 := @gElfuns (synCwpppostcomp F) p0003
  have p0005 :=
    @gMpbir (.classMem (synCwpppostcomp F) (synCfuns)) (synWfun (synCwpppostcomp F))
      p0002 p0004
  have p0006 := @gIdex
  have p0008 := @gFndm (synCvv) (synCwpppostcomp F)
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @gEleqtrri (synCid) (synCvv) (synCdm (synCwpppostcomp F)) p0006 p0009
  have p0011 := @gSsv (synCrn (synCwpppostcomp F))
  have p0015 :=
    @gSseqtr4i (synCrn (synCwpppostcomp F)) (synCvv) (synCdm (synCwpppostcomp F))
      p0011 p0009
  have p0016 :=
    @gN3pm32i (.classMem (synCwpppostcomp F) (synCfuns))
      (.classMem (synCid) (synCdm (synCwpppostcomp F)))
      (synWss (synCrn (synCwpppostcomp F)) (synCdm (synCwpppostcomp F))) p0005 p0010
      p0015
  have p0017 := @gWpporbitfnndv (synCwpppostcomp F) (synCid)
  have p0018 := Nominal.mp p0016 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_wpppowcore0`. -/
@[expose]
noncomputable def gWpppowcore0 (F : Class)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) (synCid)) :=
  by
  have p0000 := @gWpppostcompfn F hyp_wpppowcorefn_1
  have p0001 := @gFnfun (synCvv) (synCwpppostcomp F)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gWpppostcompex F hyp_wpppowcorefn_1
  have p0004 := @gElfuns (synCwpppostcomp F) p0003
  have p0005 :=
    @gMpbir (.classMem (synCwpppostcomp F) (synCfuns)) (synWfun (synCwpppostcomp F))
      p0002 p0004
  have p0006 := @gIdex
  have p0008 := @gFndm (synCvv) (synCwpppostcomp F)
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @gEleqtrri (synCid) (synCvv) (synCdm (synCwpppostcomp F)) p0006 p0009
  have p0011 := @gSsv (synCrn (synCwpppostcomp F))
  have p0015 :=
    @gSseqtr4i (synCrn (synCwpppostcomp F)) (synCvv) (synCdm (synCwpppostcomp F))
      p0011 p0009
  have p0016 :=
    @gN3pm32i (.classMem (synCwpppostcomp F) (synCfuns))
      (.classMem (synCid) (synCdm (synCwpppostcomp F)))
      (synWss (synCrn (synCwpppostcomp F)) (synCdm (synCwpppostcomp F))) p0005 p0010
      p0015
  have p0017 := @gWpporbit0ndv (synCwpppostcomp F) (synCid)
  have p0018 := Nominal.mp p0016 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_wpppowcoresuc`. -/
@[expose]
noncomputable def gWpppowcoresuc (n : Var) (F : Class) (_dv_F_n : n ∉ F.fv)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (.classEq
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv n) (synC1c)))
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))) :=
  by
  have p0000 := @gWpppostcompfn F hyp_wpppowcorefn_1
  have p0001 := @gFnfun (synCvv) (synCwpppostcomp F)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gWpppostcompex F hyp_wpppowcorefn_1
  have p0004 := @gElfuns (synCwpppostcomp F) p0003
  have p0005 :=
    @gMpbir (.classMem (synCwpppostcomp F) (synCfuns)) (synWfun (synCwpppostcomp F))
      p0002 p0004
  have p0006 := @gIdex
  have p0008 := @gFndm (synCvv) (synCwpppostcomp F)
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @gEleqtrri (synCid) (synCvv) (synCdm (synCwpppostcomp F)) p0006 p0009
  have p0011 := @gSsv (synCrn (synCwpppostcomp F))
  have p0015 :=
    @gSseqtr4i (synCrn (synCwpppostcomp F)) (synCvv) (synCdm (synCwpppostcomp F))
      p0011 p0009
  have p0016 :=
    @gN3pm32i (.classMem (synCwpppostcomp F) (synCfuns))
      (.classMem (synCid) (synCdm (synCwpppostcomp F)))
      (synWss (synCrn (synCwpppostcomp F)) (synCdm (synCwpppostcomp F))) p0005 p0010
      p0015
  have p0017 := @gWpporbitsucndv (synCwpppostcomp F) (synCid) (.cv n)
  have p0018 :=
    @gMpan
      (synW3a (.classMem (synCwpppostcomp F) (synCfuns))
        (.classMem (synCid) (synCdm (synCwpppostcomp F)))
        (synWss (synCrn (synCwpppostcomp F)) (synCdm (synCwpppostcomp F))))
      (.classMem (.cv n) (synCnnc))
      (.classEq
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv n) (synC1c)))
        (synCfv (synCwpppostcomp F)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      p0016 p0017
  have p0019 := @gFvex (.cv n) (synCfrec (synCwpppostcomp F) (synCid))
  have p0020 :=
    @gWpppostcompfv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F
      hyp_wpppowcorefn_1 p0019
  have p0021 :=
    @gA1i
      (.classEq (synCfv (synCwpppostcomp F)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0020
  have p0022 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv n) (synC1c)))
      (synCfv (synCwpppostcomp F)
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))) p0018
      p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerseqfv`. -/
@[expose]
noncomputable def gWpppowlayerseqfv (C : Class) (n : Var) (F : Class)
    (_dv_C_F : Disjoint C.fv F.fv) (_dv_C_n : n ∉ C.fv) (_dv_F_n : n ∉ F.fv)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc))
        (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))) (synCima (synCcnv
              (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
            (synCima (synClec) (synCsn C))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowlayerseq F C))
  have p0001 :=
    @gFveq1i (synCsn (.cv n)) (synCwpppowlayerseq F C)
      (synCcom (synCwppupperpreop C)
        (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))) (synCfv
          (synCcom (synCwppupperpreop C)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
          (synCsn (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0001
  have p0003 := @gWpppostcompfn F hyp_wpppowcorefn_1
  have p0004 := @gFnfun (synCvv) (synCwpppostcomp F)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gWpppostcompex F hyp_wpppowcorefn_1
  have p0007 := @gElfuns (synCwpppostcomp F) p0006
  have p0008 :=
    @gMpbir (.classMem (synCwpppostcomp F) (synCfuns)) (synWfun (synCwpppostcomp F))
      p0005 p0007
  have p0009 := @gIdex
  have p0011 := @gFndm (synCvv) (synCwpppostcomp F)
  have p0012 := Nominal.mp p0003 p0011
  have p0013 := @gEleqtrri (synCid) (synCvv) (synCdm (synCwpppostcomp F)) p0009 p0012
  have p0014 := @gSsv (synCrn (synCwpppostcomp F))
  have p0018 :=
    @gSseqtr4i (synCrn (synCwpppostcomp F)) (synCvv) (synCdm (synCwpppostcomp F))
      p0014 p0012
  have p0019 :=
    @gN3pm32i (.classMem (synCwpppostcomp F) (synCfuns))
      (.classMem (synCid) (synCdm (synCwpppostcomp F)))
      (synWss (synCrn (synCwpppostcomp F)) (synCdm (synCwpppostcomp F))) p0008 p0013
      p0018
  have p0020 := @gWpporbitfnndv (synCwpppostcomp F) (synCid)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gFnfun (synCnnc) (synCfrec (synCwpppostcomp F) (synCid))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @gFntcfn
  have p0025 := @gFnfun (synC1c) (synCtcfn)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gPm32i (synWfun (synCfrec (synCwpppostcomp F) (synCid))) (synWfun (synCtcfn))
      p0023 p0026
  have p0028 := @gFunco (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @gA1i (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (.classMem (.cv n) (synCnnc)) p0029
  have p0031 := @gNntccl (.cv n)
  have p0032 := @gVex n
  have p0033 := @gTcfnfv (.cv n) p0032
  have p0034 :=
    @gA1i (.classEq (synCfv (synCtcfn) (synCsn (.cv n))) (synCtc (.cv n)))
      (.classMem (.cv n) (synCnnc)) p0033
  have p0035 :=
    @gEleq1d (.classMem (.cv n) (synCnnc)) (synCfv (synCtcfn) (synCsn (.cv n)))
      (synCtc (.cv n)) (synCnnc) p0034
  have p0036 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCnnc))
      (.classMem (synCtc (.cv n)) (synCnnc)) p0031 p0035
  have p0056 := @gFndm (synCnnc) (synCfrec (synCwpppostcomp F) (synCid))
  have p0057 := Nominal.mp p0021 p0056
  have p0058 :=
    @gEleq2i (synCdm (synCfrec (synCwpppostcomp F) (synCid))) (synCnnc)
      (synCfv (synCtcfn) (synCsn (.cv n))) p0057
  have p0059 :=
    @gA1i
      (synWb (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
          (synCdm (synCfrec (synCwpppostcomp F) (synCid))))
        (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0058
  have p0060 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
        (synCdm (synCfrec (synCwpppostcomp F) (synCid))))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCnnc)) p0036 p0059
  have p0065 := @gSnel1c (.cv n) p0032
  have p0067 := @gFndm (synC1c) (synCtcfn)
  have p0068 := Nominal.mp p0024 p0067
  have p0069 := @gEleqtrri (synCsn (.cv n)) (synC1c) (synCdm (synCtcfn)) p0065 p0068
  have p0070 :=
    @gPm32i (synWfun (synCtcfn)) (.classMem (synCsn (.cv n)) (synCdm (synCtcfn)))
      p0026 p0069
  have p0071 :=
    @gDmfco (synCsn (.cv n)) (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)
  have p0072 := Nominal.mp p0070 p0071
  have p0073 :=
    @gA1i
      (synWb (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
        (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
          (synCdm (synCfrec (synCwpppostcomp F) (synCid)))))
      (.classMem (.cv n) (synCnnc)) p0072
  have p0074 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n))
        (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
        (synCdm (synCfrec (synCwpppostcomp F) (synCid))))
      p0060 p0073
  have p0075 :=
    @gJca (.classMem (.cv n) (synCnnc))
      (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (.classMem (synCsn (.cv n))
        (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      p0030 p0074
  have p0076 :=
    @gFvco (synCsn (.cv n)) (synCwppupperpreop C)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
  have p0077 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
        (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
      (.classEq (synCfv (synCcom (synCwppupperpreop C)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
          (synCsn (.cv n))) (synCfv (synCwppupperpreop C)
          (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
            (synCsn (.cv n)))))
      p0075 p0076
  have p0081 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (.classMem (synCsn (.cv n)) (synC1c))
      p0024 p0065
  have p0082 :=
    @gFvco2 (synC1c) (synCsn (.cv n)) (synCfrec (synCwpppostcomp F) (synCid))
      (synCtcfn)
  have p0083 := Nominal.mp p0081 p0082
  have p0086 :=
    @gFveq2i (synCfv (synCtcfn) (synCsn (.cv n))) (synCtc (.cv n))
      (synCfrec (synCwpppostcomp F) (synCid)) p0033
  have p0087 :=
    @gEqtri
      (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
        (synCsn (.cv n)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCfv (synCtcfn) (synCsn (.cv n))))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) p0083 p0086
  have p0088 :=
    @gA1i
      (.classEq (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
          (synCsn (.cv n)))
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0087
  have p0089 :=
    @gFveq2d (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
        (synCsn (.cv n)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
      (synCwppupperpreop C) p0088
  have p0090 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppupperpreop C)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) (synCsn (.cv n)))
      (synCfv (synCwppupperpreop C)
        (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
          (synCsn (.cv n))))
      (synCfv (synCwppupperpreop C)
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      p0077 p0089
  have p0091 := @gFvex (synCtc (.cv n)) (synCfrec (synCwpppostcomp F) (synCid))
  have p0092 :=
    @gWppupperpreopfv C
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) p0091
  have p0093 :=
    @gA1i
      (.classEq (synCfv (synCwppupperpreop C)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))) (synCima
          (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
          (synCima (synClec) (synCsn C))))
      (.classMem (.cv n) (synCnnc)) p0092
  have p0094 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppupperpreop C)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) (synCsn (.cv n)))
      (synCfv (synCwppupperpreop C)
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      (synCima
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synClec) (synCsn C)))
      p0090 p0093
  have p0095 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))
      (synCfv (synCcom (synCwppupperpreop C)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) (synCsn (.cv n)))
      (synCima
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synClec) (synCsn C)))
      p0002 p0094
  exact p0095

/-- Checked nominal proof certificate identified upstream as `g_wppimageatex`. -/
@[expose]
noncomputable def gWppimageatex (D : Class)
    (_hyp_wppimageatex_1 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf (.classMem (synCwppimageat D) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppimageat D))
  have p0001 := @gLnimageopex
  have p0002 := @gIdex
  have p0003 := @gVvex
  have p0004 := @gSnex (synCsn D)
  have p0005 := @gXpex (synCvv) (synCsn (synCsn D)) p0003 p0004
  have p0006 := @gTxpex (synCid) (synCxp (synCvv) (synCsn (synCsn D))) p0002 p0005
  have p0007 :=
    @gCoex (synClnimageop)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) p0001 p0006
  have p0008 :=
    @gEqeltri (synCwppimageat D)
      (synCcom (synClnimageop) (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))))
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wppimageatfn`. -/
@[expose]
noncomputable def gWppimageatfn (D : Class)
    (_hyp_wppimageatfn_1 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf (synWfn (synCwppimageat D) (synCvv)) :=
  by
  have p0000 := @gLnimageopfn
  have p0001 := @gF1ovi
  have p0002 := @gF1ofn (synCvv) (synCvv) (synCid)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gSnex D
  have p0005 := @gFnconstg (synCvv) (synCsn D) (synCvv)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gPm32i (synWfn (synCid) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCsn D))) (synCvv)) p0003 p0006
  have p0008 :=
    @gFntxp (synCvv) (synCvv) (synCid) (synCxp (synCvv) (synCsn (synCsn D)))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gInidm (synCvv)
  have p0011 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) p0010
  have p0012 :=
    @gMpbi
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) (synCvv))
      p0009 p0011
  have p0013 :=
    @gFncovv (synClnimageop)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) p0000 p0012
  have p0014 := (Nominal.classEqRefl (synCwppimageat D))
  have p0015 :=
    @gFneq1i (synCvv) (synCwppimageat D)
      (synCcom (synClnimageop) (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))))
      p0014
  have p0016 :=
    @gMpbir (synWfn (synCwppimageat D) (synCvv))
      (synWfn (synCcom (synClnimageop)
          (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))) (synCvv))
      p0013 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_wppimageatfv`. -/
@[expose]
noncomputable def gWppimageatfv (D : Class) (R : Class)
    (_hyp_wppimageatfv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_wppimageatfv_2 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCwppimageat D) R) (synCima R (synCsn D))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppimageat D))
  have p0001 :=
    @gFveq1i R (synCwppimageat D)
      (synCcom (synClnimageop) (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))))
      p0000
  have p0002 := @gF1ovi
  have p0003 := @gF1ofn (synCvv) (synCvv) (synCid)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gSnex D
  have p0006 := @gFnconstg (synCvv) (synCsn D) (synCvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i (synWfn (synCid) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCsn D))) (synCvv)) p0004 p0007
  have p0009 :=
    @gFntxp (synCvv) (synCvv) (synCid) (synCxp (synCvv) (synCsn (synCsn D)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gInidm (synCvv)
  have p0012 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) p0011
  have p0013 :=
    @gMpbi
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) (synCvv))
      p0010 p0012
  have p0014 :=
    @gPm32i
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) (synCvv))
      (.classMem R (synCvv)) p0013 hyp_wppimageatfv_2
  have p0015 :=
    @gFvco2 (synCvv) R (synClnimageop)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))
  have p0016 := Nominal.mp p0014 p0015
  have p0023 :=
    @gFvtxpvv R (synCid) (synCxp (synCvv) (synCsn (synCsn D))) p0004 p0007
      hyp_wppimageatfv_2
  have p0024 := @gFvi R (synCvv)
  have p0025 := Nominal.mp hyp_wppimageatfv_2 p0024
  have p0027 := @gFvconst2 (synCvv) (synCsn D) R p0005
  have p0028 := Nominal.mp hyp_wppimageatfv_2 p0027
  have p0029 :=
    @gOpeq12i (synCfv (synCid) R) R
      (synCfv (synCxp (synCvv) (synCsn (synCsn D))) R) (synCsn D) p0025 p0028
  have p0030 :=
    @gEqtri (synCfv (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) R)
      (synCop (synCfv (synCid) R) (synCfv (synCxp (synCvv) (synCsn (synCsn D))) R))
      (synCop R (synCsn D)) p0023 p0029
  have p0031 :=
    @gFveq2i (synCfv (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) R)
      (synCop R (synCsn D)) (synClnimageop) p0030
  have p0032 :=
    @gEqtri
      (synCfv (synCcom (synClnimageop)
          (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))) R)
      (synCfv (synClnimageop)
        (synCfv (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D)))) R))
      (synCfv (synClnimageop) (synCop R (synCsn D))) p0016 p0031
  have p0034 := @gLnimageopval (synCsn D) R hyp_wppimageatfv_2 p0005
  have p0035 :=
    @gEqtri
      (synCfv (synCcom (synClnimageop)
          (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))) R)
      (synCfv (synClnimageop) (synCop R (synCsn D))) (synCima R (synCsn D)) p0032
      p0034
  have p0036 :=
    @gEqtri (synCfv (synCwppimageat D) R)
      (synCfv (synCcom (synClnimageop)
          (synCtxp (synCid) (synCxp (synCvv) (synCsn (synCsn D))))) R)
      (synCima R (synCsn D)) p0001 p0035
  exact p0036

/-- Checked nominal proof certificate identified upstream as `g_wpppowateqex`. -/
@[expose]
noncomputable def gWpppowateqex (D : Class) (F : Class)
    (hyp_wpppowateqex_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wpppowateqex_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf (.classMem (synCwpppowateq F D) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowateq F D))
  have p0001 := @gWppimageatex D hyp_wpppowateqex_2
  have p0002 := @gWpppostcompex F hyp_wpppowateqex_1
  have p0003 := @gEqid (synCfrec (synCwpppostcomp F) (synCid))
  have p0004 :=
    @gFrecexg (synCfrec (synCwpppostcomp F) (synCid)) (synCwpppostcomp F) (synCid)
      (synCvv) p0003
  have p0005 := Nominal.mp p0002 p0004
  have p0006 := @gTcfnex
  have p0007 :=
    @gPm32i (.classMem (synCfrec (synCwpppostcomp F) (synCid)) (synCvv))
      (.classMem (synCtcfn) (synCvv)) p0005 p0006
  have p0008 :=
    @gCoexg (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn) (synCvv) (synCvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gPm32i (.classMem (synCwppimageat D) (synCvv))
      (.classMem (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)) (synCvv))
      p0001 p0009
  have p0011 :=
    @gCoexg (synCwppimageat D)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)) (synCvv)
      (synCvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gCnvexg
      (synCcom (synCwppimageat D)
        (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (synCvv)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @gEqid (synCfrec F D)
  have p0016 := @gFrecexg (synCfrec F D) F D (synCvv) p0015
  have p0017 := Nominal.mp hyp_wpppowateqex_1 p0016
  have p0018 := @gSiexg (synCfrec F D) (synCvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gPm32i
      (.classMem (synCcnv (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))) (synCvv))
      (.classMem (synCsi (synCfrec F D)) (synCvv)) p0014 p0019
  have p0021 :=
    @gCoexg
      (synCcnv (synCcom (synCwppimageat D)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      (synCsi (synCfrec F D)) (synCvv) (synCvv)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gFixexg
      (synCcom (synCcnv (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
        (synCsi (synCfrec F D)))
      (synCvv)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gUni1exg
      (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
              (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
          (synCsi (synCfrec F D))))
      (synCvv)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gEqeltri (synCwpppowateq F D)
      (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
                (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
            (synCsi (synCfrec F D)))))
      (synCvv) p0000 p0026
  exact p0027


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wpppowateqval`. -/
@[expose]
noncomputable def gWpppowateqval (D : Class) (n : Var) (F : Class)
    (hyp_wpppowateqval_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpppowateqval_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wpppowateqval_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwpppowateq F D))
          (.classEq (synCima
              (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
              (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv n)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowateq F D))
  have p0001 :=
    @gEleq2i (synCwpppowateq F D)
      (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
                (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
            (synCsi (synCfrec F D)))))
      (.cv n) p0000
  have p0002 := @gVex n
  have p0003 :=
    @gEluni1 (.cv n)
      (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
              (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
          (synCsi (synCfrec F D))))
      p0002
  have p0004 :=
    @gBitri (.classMem (.cv n) (synCwpppowateq F D))
      (.classMem (.cv n) (synCuni1 (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
                  (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
              (synCsi (synCfrec F D))))))
      (.classMem (synCsn (.cv n)) (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
                (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
            (synCsi (synCfrec F D)))))
      p0001 p0003
  have p0005 :=
    @gA1i
      (synWb (.classMem (.cv n) (synCwpppowateq F D)) (.classMem (synCsn (.cv n)) (synCfix
            (synCcom (synCcnv (synCcom (synCwppimageat D)
                  (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
              (synCsi (synCfrec F D))))))
      (.classMem (.cv n) (synCnnc)) p0004
  have p0006 := @gElex D (synCdm F)
  have p0007 := Nominal.mp hyp_wpppowateqval_2 p0006
  have p0008 := @gWppimageatfn D p0007
  have p0009 := @gFnfun (synCvv) (synCwppimageat D)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gElex F (synCfuns)
  have p0012 := Nominal.mp hyp_wpppowateqval_1 p0011
  have p0013 := @gWpppowcorefn F p0012
  have p0014 := @gFnfun (synCnnc) (synCfrec (synCwpppostcomp F) (synCid))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gFntcfn
  have p0017 := @gFnfun (synC1c) (synCtcfn)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gPm32i (synWfun (synCfrec (synCwpppostcomp F) (synCid))) (synWfun (synCtcfn))
      p0015 p0018
  have p0020 := @gFunco (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @gPm32i (synWfun (synCwppimageat D))
      (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) p0010
      p0021
  have p0023 :=
    @gFunco (synCwppimageat D)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gA1i
      (synWfun (synCcom (synCwppimageat D)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      (.classMem (.cv n) (synCnnc)) p0024
  have p0026 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem D (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wpppowateqval_1 hyp_wpppowateqval_2
      hyp_wpppowateqval_3
  have p0027 := @gWpporbitfnndv F D
  have p0028 := Nominal.mp p0026 p0027
  have p0029 := @gFnfun (synCnnc) (synCfrec F D)
  have p0030 := Nominal.mp p0028 p0029
  have p0031 := @gFunsi (synCfrec F D)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @gA1i (synWfun (synCsi (synCfrec F D))) (.classMem (.cv n) (synCnnc)) p0032
  have p0034 :=
    @gFvex (synCsn (.cv n))
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
  have p0038 := @gFndm (synCvv) (synCwppimageat D)
  have p0039 := Nominal.mp p0008 p0038
  have p0040 :=
    @gEleqtrri
      (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
        (synCsn (.cv n)))
      (synCvv) (synCdm (synCwppimageat D)) p0034 p0039
  have p0041 :=
    @gA1i
      (.classMem (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
          (synCsn (.cv n))) (synCdm (synCwppimageat D)))
      (.classMem (.cv n) (synCnnc)) p0040
  have p0053 :=
    @gA1i (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (.classMem (.cv n) (synCnnc)) p0021
  have p0054 := @gNntccl (.cv n)
  have p0056 := @gTcfnfv (.cv n) p0002
  have p0057 :=
    @gA1i (.classEq (synCfv (synCtcfn) (synCsn (.cv n))) (synCtc (.cv n)))
      (.classMem (.cv n) (synCnnc)) p0056
  have p0058 :=
    @gEleq1d (.classMem (.cv n) (synCnnc)) (synCfv (synCtcfn) (synCsn (.cv n)))
      (synCtc (.cv n)) (synCnnc) p0057
  have p0059 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCnnc))
      (.classMem (synCtc (.cv n)) (synCnnc)) p0054 p0058
  have p0063 := @gFndm (synCnnc) (synCfrec (synCwpppostcomp F) (synCid))
  have p0064 := Nominal.mp p0013 p0063
  have p0065 :=
    @gEleq2i (synCdm (synCfrec (synCwpppostcomp F) (synCid))) (synCnnc)
      (synCfv (synCtcfn) (synCsn (.cv n))) p0064
  have p0066 :=
    @gA1i
      (synWb (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
          (synCdm (synCfrec (synCwpppostcomp F) (synCid))))
        (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0065
  have p0067 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
        (synCdm (synCfrec (synCwpppostcomp F) (synCid))))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n))) (synCnnc)) p0059 p0066
  have p0072 := @gSnel1c (.cv n) p0002
  have p0074 := @gFndm (synC1c) (synCtcfn)
  have p0075 := Nominal.mp p0016 p0074
  have p0076 := @gEleqtrri (synCsn (.cv n)) (synC1c) (synCdm (synCtcfn)) p0072 p0075
  have p0077 :=
    @gPm32i (synWfun (synCtcfn)) (.classMem (synCsn (.cv n)) (synCdm (synCtcfn)))
      p0018 p0076
  have p0078 :=
    @gDmfco (synCsn (.cv n)) (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)
  have p0079 := Nominal.mp p0077 p0078
  have p0080 :=
    @gA1i
      (synWb (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
        (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
          (synCdm (synCfrec (synCwpppostcomp F) (synCid)))))
      (.classMem (.cv n) (synCnnc)) p0079
  have p0081 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n))
        (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      (.classMem (synCfv (synCtcfn) (synCsn (.cv n)))
        (synCdm (synCfrec (synCwpppostcomp F) (synCid))))
      p0067 p0080
  have p0082 :=
    @gJca (.classMem (.cv n) (synCnnc))
      (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (.classMem (synCsn (.cv n))
        (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      p0053 p0081
  have p0083 :=
    @gDmfco (synCsn (.cv n)) (synCwppimageat D)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
  have p0084 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
        (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
      (synWb (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCwppimageat D)
              (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))) (.classMem
          (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
            (synCsn (.cv n))) (synCdm (synCwppimageat D))))
      p0082 p0083
  have p0085 :=
    @gMpbird (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
      (.classMem (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
          (synCsn (.cv n))) (synCdm (synCwppimageat D)))
      p0041 p0084
  have p0086 := @gSnelpw1 (.cv n) (synCnnc)
  have p0087 :=
    @gBiimpri (.classMem (synCsn (.cv n)) (synCpw1 (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0086
  have p0088 := @gDmsi (synCfrec F D)
  have p0092 := @gFndm (synCnnc) (synCfrec F D)
  have p0093 := Nominal.mp p0028 p0092
  have p0094 := @gPw1eq (synCdm (synCfrec F D)) (synCnnc)
  have p0095 := Nominal.mp p0093 p0094
  have p0096 :=
    @gEqtri (synCdm (synCsi (synCfrec F D))) (synCpw1 (synCdm (synCfrec F D)))
      (synCpw1 (synCnnc)) p0088 p0095
  have p0097 :=
    @gA1i (.classEq (synCdm (synCsi (synCfrec F D))) (synCpw1 (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0096
  have p0098 :=
    @gEleqtrrd (.classMem (.cv n) (synCnnc)) (synCsn (.cv n)) (synCpw1 (synCnnc))
      (synCdm (synCsi (synCfrec F D))) p0087 p0097
  have p0099 :=
    @gJca (.classMem (.cv n) (synCnnc))
      (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
      (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F D)))) p0085 p0098
  have p0100 :=
    @gN3jca (.classMem (.cv n) (synCnnc))
      (synWfun (synCcom (synCwppimageat D)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
      (synWfun (synCsi (synCfrec F D)))
      (synWa (.classMem (synCsn (.cv n)) (synCdm (synCcom (synCwppimageat D)
              (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
        (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F D)))))
      p0025 p0033 p0099
  have p0101 :=
    @gFuneqfix (synCsn (.cv n))
      (synCcom (synCwppimageat D)
        (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (synCsi (synCfrec F D))
  have p0102 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synW3a (synWfun (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
        (synWfun (synCsi (synCfrec F D))) (synWa (.classMem (synCsn (.cv n)) (synCdm
              (synCcom (synCwppimageat D)
                (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
          (.classMem (synCsn (.cv n)) (synCdm (synCsi (synCfrec F D))))))
      (synWb (.classMem (synCsn (.cv n)) (synCfix (synCcom (synCcnv
                (synCcom (synCwppimageat D)
                  (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
              (synCsi (synCfrec F D))))) (.classEq (synCfv (synCcom (synCwppimageat D)
              (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
            (synCsn (.cv n))) (synCfv (synCsi (synCfrec F D)) (synCsn (.cv n)))))
      p0100 p0101
  have p0103 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpppowateq F D))
      (.classMem (synCsn (.cv n)) (synCfix (synCcom (synCcnv (synCcom (synCwppimageat D)
                (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))))
            (synCsi (synCfrec F D)))))
      (.classEq (synCfv (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
          (synCsn (.cv n))) (synCfv (synCsi (synCfrec F D)) (synCsn (.cv n))))
      p0005 p0102
  have p0145 :=
    @gFvco (synCsn (.cv n)) (synCwppimageat D)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
  have p0146 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfun (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
        (.classMem (synCsn (.cv n))
          (synCdm (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))))
      (.classEq (synCfv (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
          (synCsn (.cv n))) (synCfv (synCwppimageat D)
          (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
            (synCsn (.cv n)))))
      p0082 p0145
  have p0150 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (.classMem (synCsn (.cv n)) (synC1c))
      p0016 p0072
  have p0151 :=
    @gFvco2 (synC1c) (synCsn (.cv n)) (synCfrec (synCwpppostcomp F) (synCid))
      (synCtcfn)
  have p0152 := Nominal.mp p0150 p0151
  have p0155 :=
    @gFveq2i (synCfv (synCtcfn) (synCsn (.cv n))) (synCtc (.cv n))
      (synCfrec (synCwpppostcomp F) (synCid)) p0056
  have p0156 :=
    @gEqtri
      (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
        (synCsn (.cv n)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCfv (synCtcfn) (synCsn (.cv n))))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) p0152 p0155
  have p0157 :=
    @gA1i
      (.classEq (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
          (synCsn (.cv n)))
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0156
  have p0158 :=
    @gFveq2d (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
        (synCsn (.cv n)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
      (synCwppimageat D) p0157
  have p0159 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppimageat D)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) (synCsn (.cv n)))
      (synCfv (synCwppimageat D)
        (synCfv (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))
          (synCsn (.cv n))))
      (synCfv (synCwppimageat D)
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      p0146 p0158
  have p0162 := @gFvex (synCtc (.cv n)) (synCfrec (synCwpppostcomp F) (synCid))
  have p0163 :=
    @gWppimageatfv D
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) p0007 p0162
  have p0164 :=
    @gA1i
      (.classEq (synCfv (synCwppimageat D)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
          (synCsn D)))
      (.classMem (.cv n) (synCnnc)) p0163
  have p0165 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppimageat D)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) (synCsn (.cv n)))
      (synCfv (synCwppimageat D)
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
        (synCsn D))
      p0159 p0164
  have p0169 := @gSifnvalv n (synCnnc) (synCfrec F D)
  have p0170 :=
    @gMpan (synWfn (synCfrec F D) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.classEq (synCfv (synCsi (synCfrec F D)) (synCsn (.cv n)))
        (synCsn (synCfv (synCfrec F D) (.cv n))))
      p0028 p0169
  have p0171 :=
    @gEqeq12d (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppimageat D)
          (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn))) (synCsn (.cv n)))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
        (synCsn D))
      (synCfv (synCsi (synCfrec F D)) (synCsn (.cv n)))
      (synCsn (synCfv (synCfrec F D) (.cv n))) p0165 p0170
  have p0172 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpppowateq F D))
      (.classEq (synCfv (synCcom (synCwppimageat D)
            (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
          (synCsn (.cv n))) (synCfv (synCsi (synCfrec F D)) (synCsn (.cv n))))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv n))))
      p0103 p0171
  exact p0172

/-- Checked nominal proof certificate identified upstream as `g_wpppowateqvalcl`. -/
@[expose]
noncomputable def gWpppowateqvalcl (B : Class) (D : Class) (F : Class)
    (hyp_wpppowateqvalcl_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpppowateqvalcl_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wpppowateqvalcl_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwpppowateq F D)) (.classEq
            (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B))
              (synCsn D)) (synCsn (synCfv (synCfrec F D) B))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
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
  have dv_cache_0002 :
    n ∉
      ((Wff.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwpppowateq F D)) (.classEq
              (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B))
                (synCsn D)) (synCsn (synCfv (synCfrec F D) B)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCwpppowateq F D) p0001
  have p0006 := @gTceq (.cv n) B
  have p0007 :=
    @gSyl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (synCtc (.cv n)) (synCtc B)) p0001 p0006
  have p0008 :=
    @gFveq2d (.classEq (.cv n) B) (synCtc (.cv n)) (synCtc B)
      (synCfrec (synCwpppostcomp F) (synCid)) p0007
  have p0009 :=
    @gImaeq1d (.classEq (.cv n) B)
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)) (synCsn D) p0008
  have p0011 := @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec F D) p0001
  have p0012 :=
    @gSneqd (.classEq (.cv n) B) (synCfv (synCfrec F D) (.cv n))
      (synCfv (synCfrec F D) B) p0011
  have p0013 :=
    @gEqeq12d (.classEq (.cv n) B)
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
        (synCsn D))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)) (synCsn D))
      (synCsn (synCfv (synCfrec F D) (.cv n))) (synCsn (synCfv (synCfrec F D) B))
      p0009 p0012
  have p0014 :=
    @gBibi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCwpppowateq F D))
      (.classMem B (synCwpppowateq F D))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv n))))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) B)))
      p0004 p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (synWb (.classMem (.cv n) (synCwpppowateq F D)) (.classEq
          (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
            (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv n)))))
      (synWb (.classMem B (synCwpppowateq F D)) (.classEq
          (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B))
            (synCsn D)) (synCsn (synCfv (synCfrec F D) B))))
      p0002 p0014
  have p0016 :=
    @gWpppowateqval D n F hyp_wpppowateqvalcl_1 hyp_wpppowateqvalcl_2
      hyp_wpppowateqvalcl_3
  have p0017 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwpppowateq F D))
          (.classEq (synCima
              (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
              (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv n))))))
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwpppowateq F D)) (.classEq
            (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B))
              (synCsn D)) (synCsn (synCfv (synCfrec F D) B)))))
      n B (synCnnc) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem B (synCwpppowateq F D)) (.classEq
          (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B))
            (synCsn D)) (synCsn (synCfv (synCfrec F D) B))))
      p0000 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_wpppowcoresuccl`. -/
@[expose]
noncomputable def gWpppowcoresuccl (B : Class) (F : Class)
    (hyp_wpppowcoresuccl_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (.classEq
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_F, not_false_eq_true])
  have dv_cache_0002 : n ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0003 :
    n ∉
      ((Wff.imp (.classMem B (synCnnc)) (.classEq
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
            (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gAddceq1d (.classEq (.cv n) B) (.cv n) B (synC1c) p0001
  have p0005 :=
    @gFveq2d (.classEq (.cv n) B) (synCplc (.cv n) (synC1c)) (synCplc B (synC1c))
      (synCfrec (synCwpppostcomp F) (synCid)) p0004
  have p0007 :=
    @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec (synCwpppostcomp F) (synCid))
      p0001
  have p0008 :=
    @gCoeq2d (.classEq (.cv n) B)
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F p0007
  have p0009 :=
    @gEqeq12d (.classEq (.cv n) B)
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv n) (synC1c)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)) p0005 p0008
  have p0010 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (.classEq
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv n) (synC1c)))
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      (.classEq (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))
      p0002 p0009
  have p0011 := @gWpppowcoresuc n F dv_cache_0001 hyp_wpppowcoresuccl_1
  have p0012 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc)) (.classEq
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv n) (synC1c)))
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))))
      (.imp (.classMem B (synCnnc)) (.classEq
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B))))
      n B (synCnnc) dv_cache_0002 dv_cache_0003 p0010 p0011
  have p0013 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (.classEq (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))
      p0000 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wpppowateqall`. -/
@[expose]
noncomputable def gWpppowateqall (D : Class) (F : Class) (N : Class)
    (hyp_wpppowateqall_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpppowateqall_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wpppowateqall_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classMem N (synCwpppowateq F D))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ F.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_D : m ∉ D.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have dv_cache_0001 : n ∉ ((synCwpppowateq F D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          Finset.mem_union, fresh_n_not_D, fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.classMem (.cv m) (synCwpppowateq F D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          Finset.mem_union, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_D,
          fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ ((Wff.classMem (.cv n) (synCwpppowateq F D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          Finset.mem_union, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_D,
          fresh_m_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classMem (synC0c) (synCwpppowateq F D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          Finset.mem_union, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((Wff.classMem N (synCwpppowateq F D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          Finset.mem_union, fresh_n_not_N, fresh_n_not_D, fresh_n_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    n ∉ ((Wff.classMem (synCplc (.cv m) (synC1c)) (synCwpppowateq F D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq,
          Finset.mem_union, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_D,
          fresh_n_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : n ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wpppowateqall_1 p0000
  have p0002 := @gElex D (synCdm F)
  have p0003 := Nominal.mp hyp_wpppowateqall_2 p0002
  have p0004 := @gWpppowateqex D F p0001 p0003
  have p0005 := @gAbid2 n (synCwpppowateq F D) dv_cache_0001
  have p0006 :=
    @gEleq1i (.cab n (.classMem (.cv n) (synCwpppowateq F D))) (synCwpppowateq F D)
      (synCvv) p0005
  have p0007 :=
    @gMpbir (.classMem (.cab n (.classMem (.cv n) (synCwpppowateq F D))) (synCvv))
      (.classMem (synCwpppowateq F D) (synCvv)) p0004 p0006
  have p0008 := @gId (.classEq (.cv n) (synC0c))
  have p0009 :=
    @gEleq1d (.classEq (.cv n) (synC0c)) (.cv n) (synC0c) (synCwpppowateq F D) p0008
  have p0010 := @gId (.classEq (.cv n) (.cv m))
  have p0011 :=
    @gEleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (synCwpppowateq F D) p0010
  have p0012 := @gId (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
  have p0013 :=
    @gEleq1d (.classEq (.cv n) (synCplc (.cv m) (synC1c))) (.cv n)
      (synCplc (.cv m) (synC1c)) (synCwpppowateq F D) p0012
  have p0014 := @gId (.classEq (.cv n) N)
  have p0015 := @gEleq1d (.classEq (.cv n) N) (.cv n) N (synCwpppowateq F D) p0014
  have p0016 := @gTc0c
  have p0017 :=
    @gFveq2i (synCtc (synC0c)) (synC0c) (synCfrec (synCwpppostcomp F) (synCid))
      p0016
  have p0020 := @gWpppowcore0 F p0001
  have p0021 :=
    @gEqtri (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) (synCid) p0017 p0020
  have p0022 :=
    @gImaeq1i (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
      (synCid) (synCsn D) p0021
  have p0023 := @gImai (synCsn D)
  have p0024 :=
    @gEqtri
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
        (synCsn D))
      (synCima (synCid) (synCsn D)) (synCsn D) p0022 p0023
  have p0025 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem D (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wpppowateqall_1 hyp_wpppowateqall_2
      hyp_wpppowateqall_3
  have p0026 := @gWpporbit0ndv F D
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @gSneqi (synCfv (synCfrec F D) (synC0c)) D p0027
  have p0029 := @gEqcomi (synCsn (synCfv (synCfrec F D) (synC0c))) (synCsn D) p0028
  have p0030 :=
    @gEqtri
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
        (synCsn D))
      (synCsn D) (synCsn (synCfv (synCfrec F D) (synC0c))) p0024 p0029
  have p0031 := @gPeano1
  have p0032 :=
    @gWpppowateqvalcl (synC0c) D F hyp_wpppowateqall_1 hyp_wpppowateqall_2
      hyp_wpppowateqall_3
  have p0033 := Nominal.mp p0031 p0032
  have p0034 :=
    @gMpbir (.classMem (synC0c) (synCwpppowateq F D))
      (.classEq
        (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (synC0c)))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) (synC0c))))
      p0030 p0033
  have p0035 :=
    @gSimpl (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D))
  have p0036 := @gNntcsuc (.cv m)
  have p0037 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCnnc))
      (.classEq (synCtc (synCplc (.cv m) (synC1c))) (synCplc (synCtc (.cv m)) (synC1c)))
      p0035 p0036
  have p0038 :=
    @gFveq2d
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCtc (synCplc (.cv m) (synC1c))) (synCplc (synCtc (.cv m)) (synC1c))
      (synCfrec (synCwpppostcomp F) (synCid)) p0037
  have p0040 := @gNntccl (.cv m)
  have p0041 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCtc (.cv m)) (synCnnc)) p0035 p0040
  have p0044 := @gWpppowcoresuccl (synCtc (.cv m)) F p0001
  have p0045 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (synCtc (.cv m)) (synCnnc))
      (.classEq (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCplc (synCtc (.cv m)) (synC1c))) (synCcom F
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))))
      p0041 p0044
  have p0046 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCtc (synCplc (.cv m) (synC1c))))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCplc (synCtc (.cv m)) (synC1c)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m))))
      p0038 p0045
  have p0047 :=
    @gImaeq1d
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCtc (synCplc (.cv m) (synC1c))))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m))))
      (synCsn D) p0046
  have p0048 :=
    @gImaco F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
      (synCsn D)
  have p0049 :=
    @gA1i
      (.classEq (synCima (synCcom F
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))) (synCsn D))
        (synCima F
          (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
            (synCsn D))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      p0048
  have p0050 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCtc (synCplc (.cv m) (synC1c)))) (synCsn D))
      (synCima (synCcom F
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))) (synCsn D))
      (synCima F
        (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
          (synCsn D)))
      p0047 p0049
  have p0051 :=
    @gSimpr (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D))
  have p0053 :=
    @gWpppowateqval D m F hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0054 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCnnc))
      (synWb (.classMem (.cv m) (synCwpppowateq F D)) (.classEq
          (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
            (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv m)))))
      p0035 p0053
  have p0055 :=
    @gBiimpd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCwpppowateq F D))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv m))))
      p0054
  have p0056 :=
    @gMpd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCwpppowateq F D))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) (.cv m))))
      p0051 p0055
  have p0057 :=
    @gImaeq2d
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
        (synCsn D))
      (synCsn (synCfv (synCfrec F D) (.cv m))) F p0056
  have p0058 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCtc (synCplc (.cv m) (synC1c)))) (synCsn D))
      (synCima F
        (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv m)))
          (synCsn D)))
      (synCima F (synCsn (synCfv (synCfrec F D) (.cv m)))) p0050 p0057
  have p0059 := @gElfunsi F
  have p0060 := Nominal.mp hyp_wpppowateqall_1 p0059
  have p0061 := @gFunfn F
  have p0062 := @gBiimpi (synWfun F) (synWfn F (synCdm F)) p0061
  have p0063 := Nominal.mp p0060 p0062
  have p0064 :=
    @gA1i (synWfn F (synCdm F))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      p0063
  have p0067 := @gFrecdomfv F D (.cv m)
  have p0068 :=
    @gMpan
      (synW3a (.classMem F (synCfuns)) (.classMem D (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv m) (synCnnc))
      (.classMem (synCfv (synCfrec F D) (.cv m)) (synCdm F)) p0025 p0067
  have p0069 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCnnc))
      (.classMem (synCfv (synCfrec F D) (.cv m)) (synCdm F)) p0035 p0068
  have p0070 :=
    @gJca
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synWfn F (synCdm F)) (.classMem (synCfv (synCfrec F D) (.cv m)) (synCdm F))
      p0064 p0069
  have p0071 := @gFnsnfv (synCdm F) (synCfv (synCfrec F D) (.cv m)) F
  have p0072 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synWa (synWfn F (synCdm F)) (.classMem (synCfv (synCfrec F D) (.cv m)) (synCdm F)))
      (.classEq (synCsn (synCfv F (synCfv (synCfrec F D) (.cv m))))
        (synCima F (synCsn (synCfv (synCfrec F D) (.cv m)))))
      p0070 p0071
  have p0073 :=
    @gEqcomd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCsn (synCfv F (synCfv (synCfrec F D) (.cv m))))
      (synCima F (synCsn (synCfv (synCfrec F D) (.cv m)))) p0072
  have p0074 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCtc (synCplc (.cv m) (synC1c)))) (synCsn D))
      (synCima F (synCsn (synCfv (synCfrec F D) (.cv m))))
      (synCsn (synCfv F (synCfv (synCfrec F D) (.cv m)))) p0058 p0073
  have p0077 := @gWpporbitsucndv F D (.cv m)
  have p0078 :=
    @gMpan
      (synW3a (.classMem F (synCfuns)) (.classMem D (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv m) (synCnnc))
      (.classEq (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c)))
        (synCfv F (synCfv (synCfrec F D) (.cv m))))
      p0025 p0077
  have p0079 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCnnc))
      (.classEq (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c)))
        (synCfv F (synCfv (synCfrec F D) (.cv m))))
      p0035 p0078
  have p0080 :=
    @gSneqd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c)))
      (synCfv F (synCfv (synCfrec F D) (.cv m))) p0079
  have p0081 :=
    @gEqcomd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCsn (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c))))
      (synCsn (synCfv F (synCfv (synCfrec F D) (.cv m)))) p0080
  have p0082 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCtc (synCplc (.cv m) (synC1c)))) (synCsn D))
      (synCsn (synCfv F (synCfv (synCfrec F D) (.cv m))))
      (synCsn (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c)))) p0074 p0081
  have p0084 := @gPeano2 (.cv m)
  have p0085 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      p0035 p0084
  have p0086 :=
    @gWpppowateqvalcl (synCplc (.cv m) (synC1c)) D F hyp_wpppowateqall_1
      hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0087 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (synWb (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowateq F D)) (.classEq (synCima
            (synCfv (synCfrec (synCwpppostcomp F) (synCid))
              (synCtc (synCplc (.cv m) (synC1c)))) (synCsn D))
          (synCsn (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c))))))
      p0085 p0086
  have p0088 :=
    @gMpbird
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowateq F D))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid))
            (synCtc (synCplc (.cv m) (synC1c)))) (synCsn D))
        (synCsn (synCfv (synCfrec F D) (synCplc (.cv m) (synC1c)))))
      p0082 p0087
  have p0089 :=
    @gEx (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowateq F D))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowateq F D)) p0088
  have p0090_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (.classMem (.cv n) (synCwpppowateq F D))
          (.classMem (.cv m) (synCwpppowateq F D)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpppowateq synCuni1 synCuni synWex synWa synCin synCcompl
          synCnin synWnan synC1c synCfix synCrn synCima synWrex synWbr synCop
          synCun synCvv synCcom synCopab synCcnv synCsi synCfrec synCclos1
          synCint synCsn synCpprod synCtxp synCmpt synCplc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0090 :=
    @gFinds (.classMem (.cv n) (synCwpppowateq F D))
      (.classMem (synC0c) (synCwpppowateq F D))
      (.classMem (.cv m) (synCwpppowateq F D))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowateq F D))
      (.classMem N (synCwpppowateq F D)) n m N dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0007 p0009
      p0090_e02_recanon p0013 p0015 p0034 p0089
  exact p0090

/-- Checked nominal proof certificate identified upstream as `g_wpppowatact`. -/
@[expose]
noncomputable def gWpppowatact (D : Class) (F : Class) (N : Class)
    (hyp_wpppowatact_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpppowatact_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wpppowatact_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (.classEq
          (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc N))
            (synCsn D)) (synCsn (synCfv (synCfrec F D) N)))) :=
  by
  have p0000 :=
    @gWpppowateqall D F N hyp_wpppowatact_1 hyp_wpppowatact_2 hyp_wpppowatact_3
  have p0001 :=
    @gWpppowateqvalcl N D F hyp_wpppowatact_1 hyp_wpppowatact_2 hyp_wpppowatact_3
  have p0002 :=
    @gMpbid (.classMem N (synCnnc)) (.classMem N (synCwpppowateq F D))
      (.classEq (synCima (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc N))
          (synCsn D)) (synCsn (synCfv (synCfrec F D) N)))
      p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wpppreimaactsnd`. -/
@[expose]
noncomputable def gWpppreimaactsnd (ph : Wff) (D : Class) (R : Class) (U : Class)
    (O : Class) (_hyp_wpppreimaactsnd_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_wpppreimaactsnd_2 : Nominal.NPrf (.classMem O (synCvv)))
    (hyp_wpppreimaactsnd_3 :
      Nominal.NPrf (.imp ph (.classEq (synCima R (synCsn D)) (synCsn O)))) :
    Nominal.NPrf
      (.imp ph (synWb (.classMem D (synCima (synCcnv R) U)) (.classMem O U))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ D.fv ∪ R.fv ∪ U.fv ∪ O.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_U : x ∉ U.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_O : x ∉ O.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCcnv R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (U).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_U, not_false_eq_true])
  have dv_cache_0004 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0005 : x ∉ (O).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_O, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem O U)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          fresh_x_not_O, fresh_x_not_U, or_false, not_false_eq_true])
  have p0000 := @gElima x D (synCcnv R) U dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gA1i
      (synWb (.classMem D (synCima (synCcnv R) U))
        (synWrex x U (synWbr (.cv x) (synCcnv R) D)))
      ph p0000
  have p0002 := @gBrcnv (.cv x) D R
  have p0003 := (Nominal.biimpRefl (synWbr D R (.cv x)))
  have p0004 :=
    @gBitri (synWbr (.cv x) (synCcnv R) D) (synWbr D R (.cv x))
      (.classMem (synCop D (.cv x)) R) p0002 p0003
  have p0005 := @gElimasn R D (.cv x)
  have p0006 :=
    @gBicomi (.classMem (.cv x) (synCima R (synCsn D)))
      (.classMem (synCop D (.cv x)) R) p0005
  have p0007 :=
    @gBitri (synWbr (.cv x) (synCcnv R) D) (.classMem (synCop D (.cv x)) R)
      (.classMem (.cv x) (synCima R (synCsn D))) p0004 p0006
  have p0008 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCcnv R) D) (.classMem (.cv x) (synCima R (synCsn D))))
      ph p0007
  have p0009 :=
    @gEleq2d ph (synCima R (synCsn D)) (synCsn O) (.cv x) hyp_wpppreimaactsnd_3
  have p0010 :=
    @gBitrd ph (synWbr (.cv x) (synCcnv R) D)
      (.classMem (.cv x) (synCima R (synCsn D))) (.classMem (.cv x) (synCsn O)) p0008
      p0009
  have p0011 :=
    @gRexbidv ph (synWbr (.cv x) (synCcnv R) D) (.classMem (.cv x) (synCsn O)) x U
      dv_cache_0004 p0010
  have p0012 :=
    @gBitrd ph (.classMem D (synCima (synCcnv R) U))
      (synWrex x U (synWbr (.cv x) (synCcnv R) D))
      (synWrex x U (.classMem (.cv x) (synCsn O))) p0001 p0011
  have p0013 := (Nominal.biimpRefl (synWrex x U (.classMem (.cv x) (synCsn O))))
  have p0014 := @gAncom (.classMem (.cv x) U) (.classMem (.cv x) (synCsn O))
  have p0015 :=
    @gExbii (synWa (.classMem (.cv x) U) (.classMem (.cv x) (synCsn O)))
      (synWa (.classMem (.cv x) (synCsn O)) (.classMem (.cv x) U)) x p0014
  have p0016 :=
    @gBitri (synWrex x U (.classMem (.cv x) (synCsn O)))
      (synWex x (synWa (.classMem (.cv x) U) (.classMem (.cv x) (synCsn O))))
      (synWex x (synWa (.classMem (.cv x) (synCsn O)) (.classMem (.cv x) U))) p0013
      p0015
  have p0017 := (Nominal.biimpRefl (synWrex x (synCsn O) (.classMem (.cv x) U)))
  have p0018 :=
    @gBicomi (synWrex x (synCsn O) (.classMem (.cv x) U))
      (synWex x (synWa (.classMem (.cv x) (synCsn O)) (.classMem (.cv x) U))) p0017
  have p0019 :=
    @gBitri (synWrex x U (.classMem (.cv x) (synCsn O)))
      (synWex x (synWa (.classMem (.cv x) (synCsn O)) (.classMem (.cv x) U)))
      (synWrex x (synCsn O) (.classMem (.cv x) U)) p0016 p0018
  have p0020 := @gId (.classEq (.cv x) O)
  have p0021 := @gEleq1d (.classEq (.cv x) O) (.cv x) O U p0020
  have p0022 :=
    @gRexsn (.classMem (.cv x) U) (.classMem O U) x O dv_cache_0005 dv_cache_0006
      hyp_wpppreimaactsnd_2 p0021
  have p0023 :=
    @gBitri (synWrex x U (.classMem (.cv x) (synCsn O)))
      (synWrex x (synCsn O) (.classMem (.cv x) U)) (.classMem O U) p0019 p0022
  have p0024 :=
    @gA1i (synWb (synWrex x U (.classMem (.cv x) (synCsn O))) (.classMem O U)) ph
      p0023
  have p0025 :=
    @gBitrd ph (.classMem D (synCima (synCcnv R) U))
      (synWrex x U (.classMem (.cv x) (synCsn O))) (.classMem O U) p0012 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerorb`. -/
@[expose]
noncomputable def gWpppowlayerorb (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_n : n ∉ C.fv) (dv_F_n : n ∉ F.fv)
    (hyp_wpppowlayerorb_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpppowlayerorb_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wpppowlayerorb_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc))
        (synWb (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
          (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : n ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wpppowlayerorb_1 p0000
  have p0002 := @gWpppowlayerseqfv C n F dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @gEleq2d (.classMem (.cv n) (synCnnc))
      (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))
      (synCima
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synClec) (synCsn C)))
      D p0002
  have p0004 := @gElex D (synCdm F)
  have p0005 := Nominal.mp hyp_wpppowlayerorb_2 p0004
  have p0006 := @gFvex (.cv n) (synCfrec F D)
  have p0007 :=
    @gWpppowatact D F (.cv n) hyp_wpppowlayerorb_1 hyp_wpppowlayerorb_2
      hyp_wpppowlayerorb_3
  have p0008 :=
    @gWpppreimaactsnd (.classMem (.cv n) (synCnnc)) D
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
      (synCima (synClec) (synCsn C)) (synCfv (synCfrec F D) (.cv n)) p0005 p0006
      p0007
  have p0009 :=
    @gBitrd (.classMem (.cv n) (synCnnc))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
      (.classMem D (synCima (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
          (synCima (synClec) (synCsn C))))
      (.classMem (synCfv (synCfrec F D) (.cv n)) (synCima (synClec) (synCsn C)))
      p0003 p0008
  have p0010 := @gElimasn (synClec) C (synCfv (synCfrec F D) (.cv n))
  have p0011 :=
    (Nominal.biimpRefl (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))
  have p0012 :=
    @gBicomi (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))
      (.classMem (synCop C (synCfv (synCfrec F D) (.cv n))) (synClec)) p0011
  have p0013 :=
    @gBitri
      (.classMem (synCfv (synCfrec F D) (.cv n)) (synCima (synClec) (synCsn C)))
      (.classMem (synCop C (synCfv (synCfrec F D) (.cv n))) (synClec))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))) p0010 p0012
  have p0014 :=
    @gA1i
      (synWb (.classMem (synCfv (synCfrec F D) (.cv n)) (synCima (synClec) (synCsn C)))
        (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0013
  have p0015 :=
    @gBitrd (.classMem (.cv n) (synCnnc))
      (.classMem D (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
      (.classMem (synCfv (synCfrec F D) (.cv n)) (synCima (synClec) (synCsn C)))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))) p0009 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wppprecompex`. -/
@[expose]
noncomputable def gWppprecompex (F : Class)
    (_hyp_wppprecompex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwppprecomp F) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppprecomp F))
  have p0001 := @gComposeex
  have p0002 := @gIdex
  have p0003 := @gVvex
  have p0004 := @gSnex F
  have p0005 := @gXpex (synCvv) (synCsn F) p0003 p0004
  have p0006 := @gTxpex (synCid) (synCxp (synCvv) (synCsn F)) p0002 p0005
  have p0007 :=
    @gCoex (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) p0001
      p0006
  have p0008 :=
    @gEqeltri (synCwppprecomp F)
      (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F))))
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wppprecompfn`. -/
@[expose]
noncomputable def gWppprecompfn (F : Class)
    (hyp_wppprecompfn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfn (synCwppprecomp F) (synCvv)) :=
  by
  have p0000 := @gComposefn
  have p0001 := @gF1ovi
  have p0002 := @gF1ofn (synCvv) (synCvv) (synCid)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gFnconstg (synCvv) F (synCvv)
  have p0005 := Nominal.mp hyp_wppprecompfn_1 p0004
  have p0006 :=
    @gPm32i (synWfn (synCid) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn F)) (synCvv)) p0003 p0005
  have p0007 := @gFntxp (synCvv) (synCvv) (synCid) (synCxp (synCvv) (synCsn F))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gInidm (synCvv)
  have p0010 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) p0009
  have p0011 :=
    @gMpbi
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) (synCvv)) p0008 p0010
  have p0012 :=
    @gFncovv (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) p0000
      p0011
  have p0013 := (Nominal.classEqRefl (synCwppprecomp F))
  have p0014 :=
    @gFneq1i (synCvv) (synCwppprecomp F)
      (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))) p0013
  have p0015 :=
    @gMpbir (synWfn (synCwppprecomp F) (synCvv))
      (synWfn (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F))))
        (synCvv))
      p0012 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wppprecompfv`. -/
@[expose]
noncomputable def gWppprecompfv (R : Class) (F : Class)
    (hyp_wppprecompfv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppprecompfv_2 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCwppprecomp F) R) (synCcom R F)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppprecomp F))
  have p0001 :=
    @gFveq1i R (synCwppprecomp F)
      (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))) p0000
  have p0002 := @gF1ovi
  have p0003 := @gF1ofn (synCvv) (synCvv) (synCid)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gFnconstg (synCvv) F (synCvv)
  have p0006 := Nominal.mp hyp_wppprecompfv_1 p0005
  have p0007 :=
    @gPm32i (synWfn (synCid) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn F)) (synCvv)) p0004 p0006
  have p0008 := @gFntxp (synCvv) (synCvv) (synCid) (synCxp (synCvv) (synCsn F))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gInidm (synCvv)
  have p0011 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) p0010
  have p0012 :=
    @gMpbi
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) (synCvv)) p0009 p0011
  have p0013 :=
    @gPm32i (synWfn (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) (synCvv))
      (.classMem R (synCvv)) p0012 hyp_wppprecompfv_2
  have p0014 :=
    @gFvco2 (synCvv) R (synCcompose)
      (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))
  have p0015 := Nominal.mp p0013 p0014
  have p0021 :=
    @gFvtxpvv R (synCid) (synCxp (synCvv) (synCsn F)) p0004 p0006 hyp_wppprecompfv_2
  have p0022 := @gFvi R (synCvv)
  have p0023 := Nominal.mp hyp_wppprecompfv_2 p0022
  have p0024 := @gFvconst2 (synCvv) F R hyp_wppprecompfv_1
  have p0025 := Nominal.mp hyp_wppprecompfv_2 p0024
  have p0026 :=
    @gOpeq12i (synCfv (synCid) R) R (synCfv (synCxp (synCvv) (synCsn F)) R) F p0023
      p0025
  have p0027 :=
    @gEqtri (synCfv (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) R)
      (synCop (synCfv (synCid) R) (synCfv (synCxp (synCvv) (synCsn F)) R))
      (synCop R F) p0021 p0026
  have p0028 :=
    @gFveq2i (synCfv (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) R)
      (synCop R F) (synCcompose) p0027
  have p0029 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))) R)
      (synCfv (synCcompose) (synCfv (synCtxp (synCid) (synCxp (synCvv) (synCsn F))) R))
      (synCfv (synCcompose) (synCop R F)) p0015 p0028
  have p0030 := (Nominal.classEqRefl (synCo R (synCcompose) F))
  have p0031 :=
    @gEqcomi (synCo R (synCcompose) F) (synCfv (synCcompose) (synCop R F)) p0030
  have p0032 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))) R)
      (synCfv (synCcompose) (synCop R F)) (synCo R (synCcompose) F) p0029 p0031
  have p0033 :=
    @gPm32i (.classMem R (synCvv)) (.classMem F (synCvv)) hyp_wppprecompfv_2
      hyp_wppprecompfv_1
  have p0034 := @gComposevalg R F (synCvv) (synCvv)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @gEqtri
      (synCfv (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))) R)
      (synCo R (synCcompose) F) (synCcom R F) p0032 p0035
  have p0037 :=
    @gEqtri (synCfv (synCwppprecomp F) R)
      (synCfv (synCcom (synCcompose) (synCtxp (synCid) (synCxp (synCvv) (synCsn F)))) R)
      (synCcom R F) p0001 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_wpppowcommeqex`. -/
@[expose]
noncomputable def gWpppowcommeqex (F : Class)
    (hyp_wpppowcommeqex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpppowcommeq F) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowcommeq F))
  have p0001 := @gWppprecompex F hyp_wpppowcommeqex_1
  have p0002 := @gEqid (synCfrec (synCwpppostcomp F) (synCid))
  have p0003 := @gWpppostcompex F hyp_wpppowcommeqex_1
  have p0004 :=
    @gFrecex (synCfrec (synCwpppostcomp F) (synCid)) (synCwpppostcomp F) (synCid)
      p0002 p0003
  have p0005 :=
    @gCoex (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)) p0001 p0004
  have p0006 :=
    @gCnvex (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
      p0005
  have p0011 :=
    @gCoex (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)) p0003 p0004
  have p0012 :=
    @gCoex
      (synCcnv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))) p0006
      p0011
  have p0013 :=
    @gFixex
      (synCcom (synCcnv
          (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
        (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      p0012
  have p0014 :=
    @gEqeltri (synCwpppowcommeq F)
      (synCfix (synCcom (synCcnv
            (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))))
      (synCvv) p0000 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_wpppowcommeqval`. -/
@[expose]
noncomputable def gWpppowcommeqval (n : Var) (F : Class)
    (hyp_wpppowcommeqval_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwpppowcommeq F))
          (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
            (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowcommeq F))
  have p0001 :=
    @gEleq2i (synCwpppowcommeq F)
      (synCfix (synCcom (synCcnv
            (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))))
      (.cv n) p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (.cv n) (synCwpppowcommeq F)) (.classMem (.cv n) (synCfix (synCcom
              (synCcnv
                (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
              (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))))))
      (.classMem (.cv n) (synCnnc)) p0001
  have p0003 := @gWppprecompfn F hyp_wpppowcommeqval_1
  have p0004 := @gWpppowcorefn F hyp_wpppowcommeqval_1
  have p0005 := @gSsv (synCrn (synCfrec (synCwpppostcomp F) (synCid)))
  have p0006 :=
    @gN3pm32i (synWfn (synCwppprecomp F) (synCvv))
      (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc))
      (synWss (synCrn (synCfrec (synCwpppostcomp F) (synCid))) (synCvv)) p0003 p0004
      p0005
  have p0007 :=
    @gFnco (synCvv) (synCnnc) (synCwppprecomp F)
      (synCfrec (synCwpppostcomp F) (synCid))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gFnfun (synCnnc)
      (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gA1i
      (synWfun (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      (.classMem (.cv n) (synCnnc)) p0010
  have p0012 := @gWpppostcompfn F hyp_wpppowcommeqval_1
  have p0015 :=
    @gN3pm32i (synWfn (synCwpppostcomp F) (synCvv))
      (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc))
      (synWss (synCrn (synCfrec (synCwpppostcomp F) (synCid))) (synCvv)) p0012 p0004
      p0005
  have p0016 :=
    @gFnco (synCvv) (synCnnc) (synCwpppostcomp F)
      (synCfrec (synCwpppostcomp F) (synCid))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gFnfun (synCnnc)
      (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gA1i
      (synWfun (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      (.classMem (.cv n) (synCnnc)) p0019
  have p0021 := @gId (.classMem (.cv n) (synCnnc))
  have p0028 :=
    @gFndm (synCnnc)
      (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
  have p0029 := Nominal.mp p0008 p0028
  have p0030 :=
    @gA1i
      (.classEq (synCdm
          (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))) (synCnnc))
      (.classMem (.cv n) (synCnnc)) p0029
  have p0031 :=
    @gEleqtrrd (.classMem (.cv n) (synCnnc)) (.cv n) (synCnnc)
      (synCdm (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      p0021 p0030
  have p0039 :=
    @gFndm (synCnnc)
      (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))
  have p0040 := Nominal.mp p0017 p0039
  have p0041 :=
    @gA1i
      (.classEq (synCdm
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))
        (synCnnc))
      (.classMem (.cv n) (synCnnc)) p0040
  have p0042 :=
    @gEleqtrrd (.classMem (.cv n) (synCnnc)) (.cv n) (synCnnc)
      (synCdm (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      p0021 p0041
  have p0043 :=
    @gJca (.classMem (.cv n) (synCnnc))
      (.classMem (.cv n) (synCdm
          (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))))
      (.classMem (.cv n) (synCdm
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))))
      p0031 p0042
  have p0044 :=
    @gN3jca (.classMem (.cv n) (synCnnc))
      (synWfun (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      (synWfun (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))
      (synWa (.classMem (.cv n) (synCdm
            (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))))
        (.classMem (.cv n) (synCdm
            (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))))
      p0011 p0020 p0043
  have p0045 :=
    @gFuneqfix (.cv n)
      (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
      (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))
  have p0046 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synW3a (synWfun
          (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))) (synWfun
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))) (synWa
          (.classMem (.cv n) (synCdm
              (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))))
          (.classMem (.cv n) (synCdm (synCcom (synCwpppostcomp F)
                (synCfrec (synCwpppostcomp F) (synCid)))))))
      (synWb (.classMem (.cv n) (synCfix (synCcom (synCcnv
                (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
              (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))))
        (.classEq (synCfv
            (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))) (.cv n))
          (synCfv (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))
            (.cv n))))
      p0044 p0045
  have p0047 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpppowcommeq F))
      (.classMem (.cv n) (synCfix (synCcom (synCcnv
              (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid))))
            (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))))))
      (.classEq
        (synCfv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
          (.cv n)) (synCfv
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))) (.cv n)))
      p0002 p0046
  have p0049 :=
    @gA1i (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc))
      (.classMem (.cv n) (synCnnc)) p0004
  have p0051 :=
    @gJca (.classMem (.cv n) (synCnnc))
      (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc))
      (.classMem (.cv n) (synCnnc)) p0049 p0021
  have p0052 :=
    @gFvco2 (synCnnc) (.cv n) (synCwppprecomp F)
      (synCfrec (synCwpppostcomp F) (synCid))
  have p0053 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc))
        (.classMem (.cv n) (synCnnc)))
      (.classEq
        (synCfv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
          (.cv n)) (synCfv (synCwppprecomp F)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      p0051 p0052
  have p0054 := @gFvex (.cv n) (synCfrec (synCwpppostcomp F) (synCid))
  have p0055 :=
    @gWppprecompfv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F
      hyp_wpppowcommeqval_1 p0054
  have p0056 :=
    @gA1i
      (.classEq (synCfv (synCwppprecomp F)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
        (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F))
      (.classMem (.cv n) (synCnnc)) p0055
  have p0057 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
        (.cv n))
      (synCfv (synCwppprecomp F) (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F) p0053
      p0056
  have p0062 :=
    @gFvco2 (synCnnc) (.cv n) (synCwpppostcomp F)
      (synCfrec (synCwpppostcomp F) (synCid))
  have p0063 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (synWfn (synCfrec (synCwpppostcomp F) (synCid)) (synCnnc))
        (.classMem (.cv n) (synCnnc)))
      (.classEq (synCfv
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))) (.cv n))
        (synCfv (synCwpppostcomp F)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      p0051 p0062
  have p0065 :=
    @gWpppostcompfv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F
      hyp_wpppowcommeqval_1 p0054
  have p0066 :=
    @gA1i
      (.classEq (synCfv (synCwpppostcomp F)
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0065
  have p0067 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))
        (.cv n))
      (synCfv (synCwpppostcomp F)
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))) p0063
      p0066
  have p0068 :=
    @gEqeq12d (.classMem (.cv n) (synCnnc))
      (synCfv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
        (.cv n))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
      (synCfv (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid)))
        (.cv n))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))) p0057
      p0067
  have p0069 :=
    @gBitrd (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpppowcommeq F))
      (.classEq
        (synCfv (synCcom (synCwppprecomp F) (synCfrec (synCwpppostcomp F) (synCid)))
          (.cv n)) (synCfv
          (synCcom (synCwpppostcomp F) (synCfrec (synCwpppostcomp F) (synCid))) (.cv n)))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      p0047 p0068
  exact p0069

/-- Checked nominal proof certificate identified upstream as `g_wpppowcommeqvalcl`. -/
@[expose]
noncomputable def gWpppowcommeqvalcl (B : Class) (F : Class)
    (hyp_wpppowcommeqvalcl_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwpppowcommeq F))
          (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
            (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_F : n ∉ F.fv := by
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
  have dv_cache_0002 :
    n ∉
      ((Wff.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwpppowcommeq F))
            (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
              (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCwpppowcommeq F) p0001
  have p0006 :=
    @gFveq2d (.classEq (.cv n) B) (.cv n) B (synCfrec (synCwpppostcomp F) (synCid))
      p0001
  have p0007 :=
    @gCoeq1d (.classEq (.cv n) B)
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F p0006
  have p0010 :=
    @gCoeq2d (.classEq (.cv n) B)
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F p0006
  have p0011 :=
    @gEqeq12d (.classEq (.cv n) B)
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)) p0007 p0010
  have p0012 :=
    @gBibi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCwpppowcommeq F))
      (.classMem B (synCwpppowcommeq F))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))
      p0004 p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (synWb (.classMem (.cv n) (synCwpppowcommeq F)) (.classEq
          (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)))))
      (synWb (.classMem B (synCwpppowcommeq F))
        (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B))))
      p0002 p0012
  have p0014 := @gWpppowcommeqval n F hyp_wpppowcommeqvalcl_1
  have p0015 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwpppowcommeq F))
          (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n)) F)
            (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv n))))))
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwpppowcommeq F))
          (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
            (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))))
      n B (synCnnc) dv_cache_0001 dv_cache_0002 p0013 p0014
  have p0016 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem B (synCwpppowcommeq F))
        (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_wpppowcommall`. -/
@[expose]
noncomputable def gWpppowcommall (F : Class) (N : Class)
    (hyp_wpppowcommall_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classMem N (synCwpppowcommeq F))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (h))
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have dv_cache_0001 : n ∉ ((synCwpppowcommeq F)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          fresh_n_not_F, not_false_eq_true])
  have dv_cache_0002 : m ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_F, not_false_eq_true])
  have dv_cache_0003 : n ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Wff.classMem (.cv m) (synCwpppowcommeq F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          Finset.mem_union, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0005 : m ∉ ((Wff.classMem (.cv n) (synCwpppowcommeq F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          Finset.mem_union, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0006 : n ∉ ((Wff.classMem (synC0c) (synCwpppowcommeq F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          Finset.mem_union, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem N (synCwpppowcommeq F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          Finset.mem_union, fresh_n_not_N, fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0008 :
    n ∉ ((Wff.classMem (synCplc (.cv m) (synC1c)) (synCwpppowcommeq F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowcommeq,
          Finset.mem_union, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : n ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 := @gWpppowcommeqex F hyp_wpppowcommall_1
  have p0001 := @gAbid2 n (synCwpppowcommeq F) dv_cache_0001
  have p0002 :=
    @gEleq1i (.cab n (.classMem (.cv n) (synCwpppowcommeq F))) (synCwpppowcommeq F)
      (synCvv) p0001
  have p0003 :=
    @gMpbir (.classMem (.cab n (.classMem (.cv n) (synCwpppowcommeq F))) (synCvv))
      (.classMem (synCwpppowcommeq F) (synCvv)) p0000 p0002
  have p0004 := @gId (.classEq (.cv n) (synC0c))
  have p0005 :=
    @gEleq1d (.classEq (.cv n) (synC0c)) (.cv n) (synC0c) (synCwpppowcommeq F) p0004
  have p0006 := @gId (.classEq (.cv n) (.cv m))
  have p0007 :=
    @gEleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (synCwpppowcommeq F) p0006
  have p0008 := @gId (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
  have p0009 :=
    @gEleq1d (.classEq (.cv n) (synCplc (.cv m) (synC1c))) (.cv n)
      (synCplc (.cv m) (synC1c)) (synCwpppowcommeq F) p0008
  have p0010 := @gId (.classEq (.cv n) N)
  have p0011 := @gEleq1d (.classEq (.cv n) N) (.cv n) N (synCwpppowcommeq F) p0010
  have p0012 := @gWpppowcore0 F hyp_wpppowcommall_1
  have p0013 :=
    @gCoeq1i (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) (synCid) F
      p0012
  have p0014 := @gCoi2 F
  have p0015 :=
    @gEqtri (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) F)
      (synCcom (synCid) F) F p0013 p0014
  have p0017 :=
    @gCoeq2i (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) (synCid) F
      p0012
  have p0018 := @gCoi1 F
  have p0019 :=
    @gEqtri (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)))
      (synCcom F (synCid)) F p0017 p0018
  have p0020 :=
    @gEqcomi (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)))
      F p0019
  have p0021 :=
    @gEqtri (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) F) F
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c))) p0015
      p0020
  have p0022 := @gPeano1
  have p0023 := @gWpppowcommeqvalcl (synC0c) F hyp_wpppowcommall_1
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gMpbir (.classMem (synC0c) (synCwpppowcommeq F))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c)) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synC0c))))
      p0021 p0024
  have p0026 :=
    @gSimpl (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F))
  have p0027 := @gWpppowcoresuc m F dv_cache_0002 hyp_wpppowcommall_1
  have p0028 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (.cv m) (synCnnc))
      (.classEq
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c)))
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))))
      p0026 p0027
  have p0029 :=
    @gCoeq1d
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))) F p0028
  have p0030 := @gCoass F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F
  have p0031 :=
    @gA1i
      (.classEq (synCcom
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))) F)
        (synCcom F (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F)))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      p0030
  have p0032 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCcom
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c))) F)
      (synCcom (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))) F)
      (synCcom F (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F))
      p0029 p0031
  have p0033 :=
    @gSimpr (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F))
  have p0035 := @gWpppowcommeqval m F hyp_wpppowcommall_1
  have p0036 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (.cv m) (synCnnc))
      (synWb (.classMem (.cv m) (synCwpppowcommeq F)) (.classEq
          (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F)
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)))))
      p0026 p0035
  have p0037 :=
    @gBiimpd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (.cv m) (synCwpppowcommeq F))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))))
      p0036
  have p0038 :=
    @gMpd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (.cv m) (synCwpppowcommeq F))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))))
      p0033 p0037
  have p0039 :=
    @gCoeq2d
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F)
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))) F p0038
  have p0040 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCcom
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c))) F)
      (synCcom F (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)) F))
      (synCcom F (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))))
      p0032 p0039
  have p0044 :=
    @gEqcomd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))) p0028
  have p0045 :=
    @gCoeq2d
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c))) F
      p0044
  have p0046 :=
    @gEqtrd
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (synCcom
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c))) F)
      (synCcom F (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (.cv m))))
      (synCcom F
        (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c))))
      p0040 p0045
  have p0048 := @gPeano2 (.cv m)
  have p0049 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      p0026 p0048
  have p0050 := @gWpppowcommeqvalcl (synCplc (.cv m) (synC1c)) F hyp_wpppowcommall_1
  have p0051 :=
    @gSyl
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (synWb (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowcommeq F)) (.classEq (synCcom
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c))) F)
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid))
              (synCplc (.cv m) (synC1c))))))
      p0049 p0050
  have p0052 :=
    @gMpbird
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowcommeq F))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid))
            (synCplc (.cv m) (synC1c))) F) (synCcom F
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc (.cv m) (synC1c)))))
      p0046 p0051
  have p0053 :=
    @gEx (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCwpppowcommeq F))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowcommeq F)) p0052
  have p0054_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (.classMem (.cv n) (synCwpppowcommeq F))
          (.classMem (.cv m) (synCwpppowcommeq F)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpppowcommeq synCfix synCrn synCima synWrex synWex synWa
          synWbr synCop synCun synCnin synWnan synCcompl synCvv synCin synCid
          synCopab synCcom synCcnv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0054 :=
    @gFinds (.classMem (.cv n) (synCwpppowcommeq F))
      (.classMem (synC0c) (synCwpppowcommeq F))
      (.classMem (.cv m) (synCwpppowcommeq F))
      (.classMem (synCplc (.cv m) (synC1c)) (synCwpppowcommeq F))
      (.classMem N (synCwpppowcommeq F)) n m N dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0003 p0005
      p0054_e02_recanon p0009 p0011 p0025 p0053
  exact p0054

/-- Checked nominal proof certificate identified upstream as `g_wpppowcomm`. -/
@[expose]
noncomputable def gWpppowcomm (B : Class) (F : Class)
    (hyp_wpppowcomm_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc))
        (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
          (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))) :=
  by
  have p0000 := @gWpppowcommall F B hyp_wpppowcomm_1
  have p0001 := @gWpppowcommeqvalcl B F hyp_wpppowcomm_1
  have p0002 :=
    @gMpbid (.classMem B (synCnnc)) (.classMem B (synCwpppowcommeq F))
      (.classEq (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
        (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wpppowcorersuccl`. -/
@[expose]
noncomputable def gWpppowcorersuccl (B : Class) (F : Class)
    (hyp_wpppowcorersuccl_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (.classEq
          (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
          (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F))) :=
  by
  have p0000 := @gWpppowcoresuccl B F hyp_wpppowcorersuccl_1
  have p0001 := @gWpppowcomm B F hyp_wpppowcorersuccl_1
  have p0002 :=
    @gEqcomd (.classMem B (synCnnc))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F)
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B)) p0001
  have p0003 :=
    @gEqtrd (.classMem B (synCnnc))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCplc B (synC1c)))
      (synCcom F (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) B) F) p0000 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerseqfvcl`. -/
@[expose]
noncomputable def gWpppowlayerseqfvcl (B : Class) (C : Class) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wpppowlayerseqfvcl_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn B))
          (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
            (synCima (synClec) (synCsn C))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0002 : n ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_C, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_F, not_false_eq_true])
  have dv_cache_0004 : n ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0005 :
    n ∉
      ((Wff.imp (.classMem B (synCnnc))
          (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn B)) (synCima
              (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
              (synCima (synClec) (synCsn C)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_n_not_B, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gSneqd (.classEq (.cv n) B) (.cv n) B p0001
  have p0005 :=
    @gFveq2d (.classEq (.cv n) B) (synCsn (.cv n)) (synCsn B) (synCwpppowlayerseq F C)
      p0004
  have p0007 := @gTceq (.cv n) B
  have p0008 :=
    @gSyl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (synCtc (.cv n)) (synCtc B)) p0001 p0007
  have p0009 :=
    @gFveq2d (.classEq (.cv n) B) (synCtc (.cv n)) (synCtc B)
      (synCfrec (synCwpppostcomp F) (synCid)) p0008
  have p0010 :=
    @gCnveqd (.classEq (.cv n) B)
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)) p0009
  have p0011 :=
    @gImaeq1d (.classEq (.cv n) B)
      (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
      (synCima (synClec) (synCsn C)) p0010
  have p0012 :=
    @gEqeq12d (.classEq (.cv n) B) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))
      (synCfv (synCwpppowlayerseq F C) (synCsn B))
      (synCima
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synClec) (synCsn C)))
      (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
        (synCima (synClec) (synCsn C)))
      p0005 p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))) (synCima (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
          (synCima (synClec) (synCsn C))))
      (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn B)) (synCima
          (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
          (synCima (synClec) (synCsn C))))
      p0002 p0012
  have p0014 :=
    @gWpppowlayerseqfv C n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wpppowlayerseqfvcl_1
  have p0015 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc))
        (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))) (synCima (synCcnv
              (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
            (synCima (synClec) (synCsn C)))))
      (.imp (.classMem B (synCnnc)) (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn B))
          (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
            (synCima (synClec) (synCsn C)))))
      n B (synCnnc) dv_cache_0004 dv_cache_0005 p0013 p0014
  have p0016 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn B)) (synCima
          (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc B)))
          (synCima (synClec) (synCsn C))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerseqsuc`. -/
@[expose]
noncomputable def gWpppowlayerseqsuc (C : Class) (n : Var) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wpppowlayerseqsuc_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (synCnnc)) (.classEq
          (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv n) (synC1c))))
          (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have p0000 := @gId (.classMem (.cv n) (synCnnc))
  have p0001 := @gPeano2 (.cv n)
  have p0002 :=
    @gSyl (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc)) p0000 p0001
  have p0003 :=
    @gWpppowlayerseqfvcl (synCplc (.cv n) (synC1c)) C F dv_cache_0001
      hyp_wpppowlayerseqsuc_1
  have p0004 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classEq (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv n) (synC1c))))
        (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid))
              (synCtc (synCplc (.cv n) (synC1c))))) (synCima (synClec) (synCsn C))))
      p0002 p0003
  have p0005 := @gNntcsuc (.cv n)
  have p0006 :=
    @gFveq2d (.classMem (.cv n) (synCnnc)) (synCtc (synCplc (.cv n) (synC1c)))
      (synCplc (synCtc (.cv n)) (synC1c)) (synCfrec (synCwpppostcomp F) (synCid))
      p0005
  have p0007 := @gNntccl (.cv n)
  have p0008 := @gWpppowcorersuccl (synCtc (.cv n)) F hyp_wpppowlayerseqsuc_1
  have p0009 :=
    @gSyl (.classMem (.cv n) (synCnnc)) (.classMem (synCtc (.cv n)) (synCnnc))
      (.classEq (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCplc (synCtc (.cv n)) (synC1c)))
        (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) F))
      p0007 p0008
  have p0010 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCtc (synCplc (.cv n) (synC1c))))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCplc (synCtc (.cv n)) (synC1c)))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) F)
      p0006 p0009
  have p0011 :=
    @gCnveqd (.classMem (.cv n) (synCnnc))
      (synCfv (synCfrec (synCwpppostcomp F) (synCid))
        (synCtc (synCplc (.cv n) (synC1c))))
      (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) F)
      p0010
  have p0012 :=
    @gImaeq1d (.classMem (.cv n) (synCnnc))
      (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid))
          (synCtc (synCplc (.cv n) (synC1c)))))
      (synCcnv (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
          F))
      (synCima (synClec) (synCsn C)) p0011
  have p0013 :=
    @gCnvco (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) F
  have p0014 :=
    @gA1i
      (.classEq (synCcnv
          (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) F))
        (synCcom (synCcnv F) (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))))
      (.classMem (.cv n) (synCnnc)) p0013
  have p0015 :=
    @gImaeq1d (.classMem (.cv n) (synCnnc))
      (synCcnv (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))
          F))
      (synCcom (synCcnv F)
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))))
      (synCima (synClec) (synCsn C)) p0014
  have p0016 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid))
            (synCtc (synCplc (.cv n) (synC1c))))) (synCima (synClec) (synCsn C)))
      (synCima (synCcnv
          (synCcom (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))) F))
        (synCima (synClec) (synCsn C)))
      (synCima (synCcom (synCcnv F) (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))))
        (synCima (synClec) (synCsn C)))
      p0012 p0015
  have p0017 :=
    @gImaco (synCcnv F)
      (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
      (synCima (synClec) (synCsn C))
  have p0018 :=
    @gA1i
      (.classEq (synCima (synCcom (synCcnv F) (synCcnv
              (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))))
          (synCima (synClec) (synCsn C))) (synCima (synCcnv F) (synCima (synCcnv
              (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
            (synCima (synClec) (synCsn C)))))
      (.classMem (.cv n) (synCnnc)) p0017
  have p0019 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid))
            (synCtc (synCplc (.cv n) (synC1c))))) (synCima (synClec) (synCsn C)))
      (synCima (synCcom (synCcnv F) (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n)))))
        (synCima (synClec) (synCsn C)))
      (synCima (synCcnv F) (synCima (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
          (synCima (synClec) (synCsn C))))
      p0016 p0018
  have p0020 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv n) (synC1c))))
      (synCima (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid))
            (synCtc (synCplc (.cv n) (synC1c))))) (synCima (synClec) (synCsn C)))
      (synCima (synCcnv F) (synCima (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
          (synCima (synClec) (synCsn C))))
      p0004 p0019
  have p0021 := @gWpppowlayerseqfvcl (.cv n) C F dv_cache_0001 hyp_wpppowlayerseqsuc_1
  have p0022 :=
    @gEqcomd (.classMem (.cv n) (synCnnc))
      (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))
      (synCima
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synClec) (synCsn C)))
      p0021
  have p0023 :=
    @gImaeq2d (.classMem (.cv n) (synCnnc))
      (synCima
        (synCcnv (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
        (synCima (synClec) (synCsn C)))
      (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))) (synCcnv F) p0022
  have p0024 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCfv (synCwpppowlayerseq F C) (synCsn (synCplc (.cv n) (synC1c))))
      (synCima (synCcnv F) (synCima (synCcnv
            (synCfv (synCfrec (synCwpppostcomp F) (synCid)) (synCtc (.cv n))))
          (synCima (synClec) (synCsn C))))
      (synCima (synCcnv F) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))) p0020
      p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_wppreachincblayerscl`. -/
@[expose]
noncomputable def gWppreachincblayerscl (B : Class) (C : Class) (F : Class) (d : Var)
    (dv_B_d : d ∉ B.fv) (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv)
    (dv_F_d : d ∉ F.fv)
    (hyp_wppreachincblayerscl_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwppreachincb F C))
          (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                  (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                  (synCtc B)))
              (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B))))))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ F.fv ∪ ({ d } : Finset Var)
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
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_d : n ≠ d := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_n : d ≠ n := Ne.symm fresh_n_ne_d
  have dv_cache_0001 : d ∉ ((Wff.classEq (.cv n) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_n, dv_B_d, or_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (C).fv (F).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have dv_cache_0003 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_d, not_false_eq_true])
  have dv_cache_0004 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_C, not_false_eq_true])
  have dv_cache_0005 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_d, not_false_eq_true])
  have dv_cache_0006 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_F, not_false_eq_true])
  have dv_cache_0007 : d ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show d ≠ n from (by exact fresh_d_ne_n))
  have dv_cache_0008 : n ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0009 :
    n ∉
      ((Wff.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwppreachincb F C))
            (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                    (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                    (synCtc B))) (.classMem (.cv d)
                  (synCfv (synCwpppowlayerseq F C) (synCsn B)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreachincb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_n_not_B,
          fresh_n_not_C, fresh_n_not_F, fresh_n_ne_d, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gId (.classEq (.cv n) B)
  have p0002 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCnnc) p0001
  have p0004 := @gEleq1d (.classEq (.cv n) B) (.cv n) B (synCwppreachincb F C) p0001
  have p0006 := @gTceq (.cv n) B
  have p0007 :=
    @gSyl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (synCtc (.cv n)) (synCtc B)) p0001 p0006
  have p0008 :=
    @gFveq2d (.classEq (.cv n) B) (synCtc (.cv n)) (synCtc B)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) p0007
  have p0009 :=
    @gEleq2d (.classEq (.cv n) B)
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (.cv n)))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc B))
      (.cv d) p0008
  have p0011 := @gSneqd (.classEq (.cv n) B) (.cv n) B p0001
  have p0012 :=
    @gFveq2d (.classEq (.cv n) B) (synCsn (.cv n)) (synCsn B) (synCwpppowlayerseq F C)
      p0011
  have p0013 :=
    @gEleq2d (.classEq (.cv n) B) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))
      (synCfv (synCwpppowlayerseq F C) (synCsn B)) (.cv d) p0012
  have p0014 :=
    @gBibi12d (.classEq (.cv n) B)
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv n))))
      (.classMem (.cv d)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc B)))
      (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))
      (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B))) p0009 p0013
  have p0015 :=
    @gRalbidv (.classEq (.cv n) B)
      (synWb (.classMem (.cv d)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv n))))
        (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))))
      (synWb (.classMem (.cv d)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc B))) (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B))))
      d (synCdm F) dv_cache_0001 p0014
  have p0016 :=
    @gBibi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCwppreachincb F C))
      (.classMem B (synCwppreachincb F C))
      (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv n))))
          (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))))
      (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc B)))
          (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B)))))
      p0004 p0015
  have p0017 :=
    @gImbi12d (.classEq (.cv n) B) (.classMem (.cv n) (synCnnc))
      (.classMem B (synCnnc))
      (synWb (.classMem (.cv n) (synCwppreachincb F C)) (synWral d (synCdm F) (synWb
            (.classMem (.cv d) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc (.cv n))))
            (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n)))))))
      (synWb (.classMem B (synCwppreachincb F C)) (synWral d (synCdm F) (synWb
            (.classMem (.cv d) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc B)))
            (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B))))))
      p0002 p0016
  have p0018 :=
    @gWppreachincblayers C n F d dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 hyp_wppreachincblayerscl_1
  have p0019 :=
    @gVtoclg
      (.imp (.classMem (.cv n) (synCnnc)) (synWb (.classMem (.cv n) (synCwppreachincb F C))
          (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                  (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                  (synCtc (.cv n)))) (.classMem (.cv d)
                (synCfv (synCwpppowlayerseq F C) (synCsn (.cv n))))))))
      (.imp (.classMem B (synCnnc)) (synWb (.classMem B (synCwppreachincb F C))
          (synWral d (synCdm F) (synWb (.classMem (.cv d) (synCfv
                  (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                  (synCtc B)))
              (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B)))))))
      n B (synCnnc) dv_cache_0008 dv_cache_0009 p0017 p0018
  have p0020 :=
    @gMpd (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem B (synCwppreachincb F C)) (synWral d (synCdm F) (synWb
            (.classMem (.cv d) (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc B)))
            (.classMem (.cv d) (synCfv (synCwpppowlayerseq F C) (synCsn B))))))
      p0000 p0019
  exact p0020


end NFChoice.DirectNominalPrf.WPPReplay

end
