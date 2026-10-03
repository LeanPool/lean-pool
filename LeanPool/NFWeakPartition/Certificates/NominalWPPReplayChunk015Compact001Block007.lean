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

@[expose]
noncomputable def g_wpppostcompfv (R : Class) (F : Class)
    (hyp_wpppostcompfv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wpppostcompfv_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpppostcomp F) R) (syn_ccom F R)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppostcomp F))
  have p0001 :=
    @g_fveq1i R (syn_cwpppostcomp F)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) p0000
  have p0002 := @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0003 := Nominal.mp hyp_wpppostcompfv_1 p0002
  have p0004 := @g_f1ovi
  have p0005 := @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0003 p0006
  have p0008 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_inidm (syn_cvv)
  have p0011 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0010
  have p0012 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cvv))
      (.classMem R (syn_cvv)) p0012 hyp_wpppostcompfv_2
  have p0014 :=
    @g_fvco2 (syn_cvv) R (syn_ccompose)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))
  have p0015 := Nominal.mp p0013 p0014
  have p0021 :=
    @g_fvtxpvv R (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid) p0003 p0006 hyp_wpppostcompfv_2
  have p0022 := @g_fvconst2 (syn_cvv) F R hyp_wpppostcompfv_1
  have p0023 := Nominal.mp hyp_wpppostcompfv_2 p0022
  have p0024 := @g_fvi R (syn_cvv)
  have p0025 := Nominal.mp hyp_wpppostcompfv_2 p0024
  have p0026 :=
    @g_opeq12i (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R) F (syn_cfv (syn_cid) R) R p0023
      p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) R)
      (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R) (syn_cfv (syn_cid) R))
      (syn_cop F R) p0021 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) R)
      (syn_cop F R) (syn_ccompose) p0027
  have p0029 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R)
      (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) R))
      (syn_cfv (syn_ccompose) (syn_cop F R)) p0015 p0028
  have p0030 := (Nominal.classEqRefl (syn_co F (syn_ccompose) R))
  have p0031 :=
    @g_eqcomi (syn_co F (syn_ccompose) R) (syn_cfv (syn_ccompose) (syn_cop F R)) p0030
  have p0032 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R)
      (syn_cfv (syn_ccompose) (syn_cop F R)) (syn_co F (syn_ccompose) R) p0029 p0031
  have p0033 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem R (syn_cvv)) hyp_wpppostcompfv_1
      hyp_wpppostcompfv_2
  have p0034 := @g_composevalg F R (syn_cvv) (syn_cvv)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R)
      (syn_co F (syn_ccompose) R) (syn_ccom F R) p0032 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_cwpppostcomp F) R)
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) R)
      (syn_ccom F R) p0001 p0036
  exact p0037

@[expose]
noncomputable def g_wppupperpreopfn (C : Class) :
    Nominal.NPrf (syn_wfn (syn_cwppupperpreop C) (syn_cvv)) :=
  by
  have p0000 := @g_lnimageopfn
  have p0001 := @g_imageswapfn
  have p0002 := @g_wppreachupperex C
  have p0003 := @g_fnconstg (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) (syn_cvv))
      p0001 p0004
  have p0006 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap))
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_inidm (syn_cvv)
  have p0009 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cimage (syn_cswap))
        (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
      p0008
  have p0010 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv))
      p0007 p0009
  have p0011 :=
    @g_fncovv (syn_clnimageop)
      (syn_ctxp (syn_cimage (syn_cswap))
        (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
      p0000 p0010
  have p0012 := (Nominal.classEqRefl (syn_cwppupperpreop C))
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_cwppupperpreop C)
      (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))))
      p0012
  have p0014 :=
    @g_mpbir (syn_wfn (syn_cwppupperpreop C) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
            (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) (syn_cvv))
      p0011 p0013
  exact p0014

@[expose]
noncomputable def g_wppimageswapfv (R : Class)
    (hyp_wppimageswapfv_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R)) :=
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
    x ∉ ((Wff.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R))).fv :=
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
  have p0000 := @g_id (.classEq (.cv x) R)
  have p0001 := @g_fveq2d (.classEq (.cv x) R) (.cv x) R (syn_cimage (syn_cswap)) p0000
  have p0003 := @g_cnveqd (.classEq (.cv x) R) (.cv x) R p0000
  have p0004 :=
    @g_eqeq12d (.classEq (.cv x) R) (syn_cfv (syn_cimage (syn_cswap)) (.cv x))
      (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv (.cv x)) (syn_ccnv R) p0001 p0003
  have p0005 := @g_imageswapval x
  have p0006 :=
    @g_vtoclg (.classEq (syn_cfv (syn_cimage (syn_cswap)) (.cv x)) (syn_ccnv (.cv x)))
      (.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R)) x R (syn_cvv)
      dv_cache_0001 dv_cache_0002 p0004 p0005
  have p0007 := Nominal.mp hyp_wppimageswapfv_1 p0006
  exact p0007

@[expose]
noncomputable def g_wppupperpreopfv (C : Class) (R : Class)
    (hyp_wppupperpreopfv_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppupperpreop C) R)
        (syn_cima (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppupperpreop C))
  have p0001 :=
    @g_fveq1i R (syn_cwppupperpreop C)
      (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))))
      p0000
  have p0002 := @g_imageswapfn
  have p0003 := @g_wppreachupperex C
  have p0004 := @g_fnconstg (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) (syn_cvv))
      p0002 p0005
  have p0007 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap))
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cimage (syn_cswap))
        (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
      p0009
  have p0011 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv))
      p0008 p0010
  have p0012 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) (syn_cvv))
      (.classMem R (syn_cvv)) p0011 hyp_wppupperpreopfv_1
  have p0013 :=
    @g_fvco2 (syn_cvv) R (syn_clnimageop)
      (syn_ctxp (syn_cimage (syn_cswap))
        (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
  have p0014 := Nominal.mp p0012 p0013
  have p0019 :=
    @g_fvtxpvv R (syn_cimage (syn_cswap))
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) p0002 p0005
      hyp_wppupperpreopfv_1
  have p0020 := @g_wppimageswapfv R hyp_wppupperpreopfv_1
  have p0022 := @g_fvconst2 (syn_cvv) (syn_cima (syn_clec) (syn_csn C)) R p0003
  have p0023 := Nominal.mp hyp_wppupperpreopfv_1 p0022
  have p0024 :=
    @g_opeq12i (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R)
      (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) R)
      (syn_cima (syn_clec) (syn_csn C)) p0020 p0023
  have p0025 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) R)
      (syn_cop (syn_cfv (syn_cimage (syn_cswap)) R)
        (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) R))
      (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) p0019 p0024
  have p0026 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) R)
      (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) (syn_clnimageop) p0025
  have p0027 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
            (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) R)
      (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_cimage (syn_cswap))
            (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) R))
      (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))))
      p0014 p0026
  have p0028 := @g_cnvex R hyp_wppupperpreopfv_1
  have p0030 := @g_lnimageopval (syn_cima (syn_clec) (syn_csn C)) (syn_ccnv R) p0028 p0003
  have p0031 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
            (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) R)
      (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))))
      (syn_cima (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) p0027 p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_cwppupperpreop C) R)
      (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
            (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) R)
      (syn_cima (syn_ccnv R) (syn_cima (syn_clec) (syn_csn C))) p0001 p0031
  exact p0032

@[expose]
noncomputable def g_wpppowlayerseqfun (C : Class) (F : Class)
    (hyp_wpppowlayerseqfun_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfun (syn_cwpppowlayerseq F C)) :=
  by
  have p0000 := @g_wppupperpreopfn C
  have p0001 := @g_fnfun (syn_cvv) (syn_cwppupperpreop C)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_wpppostcompfn F hyp_wpppowlayerseqfun_1
  have p0004 := @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_wpppostcompex F hyp_wpppowlayerseqfun_1
  have p0007 := @g_elfuns (syn_cwpppostcomp F) p0006
  have p0008 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F))
      p0005 p0007
  have p0009 := @g_idex
  have p0011 := @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0012 := Nominal.mp p0003 p0011
  have p0013 := @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0009 p0012
  have p0014 := @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0018 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F))
      p0014 p0012
  have p0019 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns))
      (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F)))
      (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0008 p0013
      p0018
  have p0020 := @g_wpporbitfnndv (syn_cwpppostcomp F) (syn_cid)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @g_fntcfn
  have p0025 := @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn))
      p0023 p0026
  have p0028 := @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @g_pm3_2i (syn_wfun (syn_cwppupperpreop C))
      (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) p0002
      p0029
  have p0031 :=
    @g_funco (syn_cwppupperpreop C)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := (Nominal.classEqRefl (syn_cwpppowlayerseq F C))
  have p0034 :=
    @g_funeqi (syn_cwpppowlayerseq F C)
      (syn_ccom (syn_cwppupperpreop C)
        (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      p0033
  have p0035 :=
    @g_mpbir (syn_wfun (syn_cwpppowlayerseq F C))
      (syn_wfun (syn_ccom (syn_cwppupperpreop C)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      p0032 p0034
  exact p0035

@[expose]
noncomputable def g_wpphitfamfv (C : Class) (D : Class) (F : Class)
    (hyp_wpphitfamfv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))
        (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C))
          (syn_cima (syn_csset) (syn_csn (syn_csn D))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphitfam F C))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn D)) (syn_cwpphitfam F C)
      (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset)))
      p0000
  have p0002 := @g_wppimagefun (syn_csset)
  have p0003 := @g_eqid (syn_cima (syn_csset) (syn_csn (syn_csn D)))
  have p0004 := @g_snex (syn_csn D)
  have p0005 := @g_ssetex
  have p0007 := @g_imaex (syn_csset) (syn_csn (syn_csn D)) p0005 p0004
  have p0008 :=
    @g_brimage (syn_csn (syn_csn D)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))
      (syn_csset) p0004 p0007
  have p0009 :=
    @g_mpbir
      (syn_wbr (syn_csn (syn_csn D)) (syn_cimage (syn_csset))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (.classEq (syn_cima (syn_csset) (syn_csn (syn_csn D)))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      p0003 p0008
  have p0010 :=
    @g_breldm (syn_csn (syn_csn D)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))
      (syn_cimage (syn_csset))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfun (syn_cimage (syn_csset)))
      (.classMem (syn_csn (syn_csn D)) (syn_cdm (syn_cimage (syn_csset)))) p0002 p0011
  have p0013 :=
    @g_fvco (syn_csn (syn_csn D)) (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
      (syn_cimage (syn_csset))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))
      (syn_cfv (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
          (syn_cimage (syn_csset))) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
        (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D))))
      p0001 p0014
  have p0018 := @g_wppimagefv (syn_csn (syn_csn D)) (syn_csset) p0005 p0004
  have p0019 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D)))
      (syn_cima (syn_csset) (syn_csn (syn_csn D)))
      (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) p0018
  have p0020 :=
    @g_eqtri (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
        (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D))))
      (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      p0015 p0019
  have p0021 := @g_wpppowlayerseqex C F hyp_wpphitfamfv_1
  have p0022 := @g_cnvex (syn_cwpppowlayerseq F C) p0021
  have p0026 :=
    @g_wppimagefv (syn_cima (syn_csset) (syn_csn (syn_csn D)))
      (syn_ccnv (syn_cwpppowlayerseq F C)) p0022 p0007
  have p0027 :=
    @g_eqtri (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      p0020 p0026
  exact p0027

@[expose]
noncomputable def g_elwpphitfam (C : Class) (D : Class) (F : Class) (q : Var)
    (hyp_elwpphitfam_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_elwpphitfam_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))))
        (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))) :=
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
  have dv_cache_0003 : z ∉ ((syn_cima (syn_csset) (syn_csn (syn_csn D)))).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))).fv :=
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
    y ∉ ((Wff.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))).fv :=
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
  have p0000 := @g_wpphitfamfv C D F hyp_elwpphitfam_1
  have p0001 :=
    @g_eleq2i (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D)))
      (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (syn_csn (.cv q)) p0000
  have p0002 := @g_elimasn (syn_csset) (syn_csn D) (.cv z)
  have p0003 := (Nominal.biimpRefl (syn_wbr (syn_csn D) (syn_csset) (.cv z)))
  have p0004 :=
    @g_bicomi (syn_wbr (syn_csn D) (syn_csset) (.cv z))
      (.classMem (syn_cop (syn_csn D) (.cv z)) (syn_csset)) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (.classMem (syn_cop (syn_csn D) (.cv z)) (syn_csset))
      (syn_wbr (syn_csn D) (syn_csset) (.cv z)) p0002 p0004
  have p0006 := @g_vex z
  have p0007 := @g_brssetsn D (.cv z) hyp_elwpphitfam_2 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (syn_wbr (syn_csn D) (syn_csset) (.cv z)) (.classMem D (.cv z)) p0005 p0007
  have p0010 := @g_id (.classEq (.cv y) (.cv z))
  have p0011 := @g_eleq2d (.classEq (.cv y) (.cv z)) (.cv y) (.cv z) D p0010
  have p0012 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (.cv z)) y (.cv z) dv_cache_0001
      dv_cache_0002 p0006 p0011
  have p0013 :=
    @g_bitr4i (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (.classMem D (.cv z)) (.classMem (.cv z) (.cab y (.classMem D (.cv y)))) p0008 p0012
  have p0014 :=
    @g_eqriv z (syn_cima (syn_csset) (syn_csn (syn_csn D))) (.cab y (.classMem D (.cv y)))
      dv_cache_0003 dv_cache_0004 p0013
  have p0015 :=
    @g_imaeq2i (syn_cima (syn_csset) (syn_csn (syn_csn D))) (.cab y (.classMem D (.cv y)))
      (syn_ccnv (syn_cwpppowlayerseq F C)) p0014
  have p0016 :=
    @g_eleq2i
      (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C))
        (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y))))
      (syn_csn (.cv q)) p0015
  have p0017 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))))
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C))
          (syn_cima (syn_csset) (syn_csn (syn_csn D)))))
      (.classMem (syn_csn (.cv q))
        (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      p0001 p0016
  have p0018 := @g_wpppowlayerseqfun C F hyp_elwpphitfam_1
  have p0019 := @g_funfn (syn_cwpppowlayerseq F C)
  have p0020 :=
    @g_mpbi (syn_wfun (syn_cwpppowlayerseq F C))
      (syn_wfn (syn_cwpppowlayerseq F C) (syn_cdm (syn_cwpppowlayerseq F C))) p0018 p0019
  have p0021 :=
    @g_elpreima (syn_cdm (syn_cwpppowlayerseq F C)) (syn_csn (.cv q))
      (.cab y (.classMem D (.cv y))) (syn_cwpppowlayerseq F C)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @g_fvex (syn_csn (.cv q)) (syn_cwpppowlayerseq F C)
  have p0024 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))
  have p0025 :=
    @g_eleq2d (.classEq (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))
      (.cv y) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) D p0024
  have p0026 :=
    @g_elab (.classMem D (.cv y))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) y
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))) dv_cache_0005 dv_cache_0006
      p0023 p0025
  have p0027 := @g_elfvdm D (syn_csn (.cv q)) (syn_cwpppowlayerseq F C)
  have p0028 :=
    @g_sylbi
      (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q))))
      (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C))) p0026 p0027
  have p0029 :=
    @g_pm4_71ri
      (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C))) p0028
  have p0030 :=
    @g_bicomi
      (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C)))
        (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
          (.cab y (.classMem D (.cv y)))))
      p0029
  have p0031 :=
    @g_bitri
      (.classMem (syn_csn (.cv q))
        (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_cwpppowlayerseq F C)))
        (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
          (.cab y (.classMem D (.cv y)))))
      (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      p0022 p0030
  have p0036 :=
    @g_bitri
      (.classMem (syn_csn (.cv q))
        (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      (.classMem (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))
        (.cab y (.classMem D (.cv y))))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) p0031 p0026
  have p0037 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn D))))
      (.classMem (syn_csn (.cv q))
        (syn_cima (syn_ccnv (syn_cwpppowlayerseq F C)) (.cab y (.classMem D (.cv y)))))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv q)))) p0017 p0036
  exact p0037

@[expose]
noncomputable def g_wpppredmemrelex (C : Class) (F : Class)
    (hyp_wpppredmemrelex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppredmemrel F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppredmemrel F C))
  have p0001 := @g_ssetex
  have p0002 := @g_cnvex (syn_csset) p0001
  have p0003 := @g_wpppredfamex C F hyp_wpppredmemrelex_1
  have p0004 := @g_coex (syn_ccnv (syn_csset)) (syn_cwpppredfam F C) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_cwpppredmemrel F C)
      (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) (syn_cvv) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wpphitmemrelex (C : Class) (F : Class)
    (hyp_wpppredmemrelex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpphitmemrel F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphitmemrel F C))
  have p0001 := @g_ssetex
  have p0002 := @g_cnvex (syn_csset) p0001
  have p0003 := @g_wpphitfamex C F hyp_wpppredmemrelex_1
  have p0004 := @g_coex (syn_ccnv (syn_csset)) (syn_cwpphitfam F C) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_cwpphitmemrel F C)
      (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) (syn_cvv) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wppreachincbex (C : Class) (F : Class)
    (hyp_wppreachincbex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppreachincb F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppreachincb F C))
  have p0001 := @g_nncex
  have p0002 := @g_pw1ex (syn_cnnc) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cnnc)) p0002
  have p0004 := @g_wpppredmemrelex C F hyp_wppreachincbex_1
  have p0005 := @g_wpphitmemrelex C F hyp_wppreachincbex_1
  have p0006 := @g_symdifex (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C) p0004 p0005
  have p0007 := @g_dmex F hyp_wppreachincbex_1
  have p0008 := @g_pw1ex (syn_cdm F) p0007
  have p0009 := @g_pw1ex (syn_cpw1 (syn_cdm F)) p0008
  have p0010 :=
    @g_resex (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
      (syn_cpw1 (syn_cpw1 (syn_cdm F))) p0006 p0009
  have p0011 :=
    @g_rnex
      (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
        (syn_cpw1 (syn_cpw1 (syn_cdm F))))
      p0010
  have p0012 :=
    @g_difex (syn_cpw1 (syn_cpw1 (syn_cnnc)))
      (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
          (syn_cpw1 (syn_cpw1 (syn_cdm F)))))
      p0003 p0011
  have p0013 :=
    @g_uni1ex
      (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))
      p0012
  have p0014 :=
    @g_uni1ex
      (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0013
  have p0015 :=
    @g_eqeltri (syn_cwppreachincb F C)
      (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      (syn_cvv) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_elwppreachincb (C : Class) (F : Class) (N : Class)
    (_dv_C_F : Disjoint C.fv F.fv) (_dv_C_N : Disjoint C.fv N.fv)
    (_dv_F_N : Disjoint F.fv N.fv) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem N (syn_cwppreachincb F C)) (.neg
            (.classMem (syn_csn (syn_csn N)) (syn_crn
                (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                  (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppreachincb F C))
  have p0001 :=
    @g_eleq2i (syn_cwppreachincb F C)
      (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      N p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem N (syn_cwppreachincb F C)) (.classMem N (syn_cuni1 (syn_cuni1
              (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
                  (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                    (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))))
      (.classMem N (syn_cnnc)) p0001
  have p0003 :=
    @g_eluni1g N
      (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (syn_cnnc)
  have p0004 := @g_id (.classMem N (syn_cnnc))
  have p0005 := @g_snelpw1 N (syn_cnnc)
  have p0006 :=
    @g_sylibr (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) p0004 p0005
  have p0007 :=
    @g_eluni1g (syn_csn N)
      (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))
      (syn_cpw1 (syn_cnnc))
  have p0008 :=
    @g_syl (.classMem N (syn_cnnc)) (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc)))
      (syn_wb (.classMem (syn_csn N) (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc)))
              (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                  (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))) (.classMem (syn_csn (syn_csn N))
          (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      p0006 p0007
  have p0009 :=
    @g_bitrd (.classMem N (syn_cnnc))
      (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
                (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                  (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))))
      (.classMem (syn_csn N) (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0003 p0008
  have p0010 :=
    @g_eldif (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc)))
      (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
          (syn_cpw1 (syn_cpw1 (syn_cdm F)))))
  have p0011 := @g_snelpw1 (syn_csn N) (syn_cpw1 (syn_cnnc))
  have p0013 :=
    @g_bitri (.classMem (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc))))
      (.classMem (syn_csn N) (syn_cpw1 (syn_cnnc))) (.classMem N (syn_cnnc)) p0011 p0005
  have p0014 :=
    @g_anbi1i (.classMem (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc))))
      (.classMem N (syn_cnnc))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0013
  have p0015 :=
    @g_bitri
      (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (syn_wa (.classMem (syn_csn (syn_csn N)) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.neg
          (.classMem (syn_csn (syn_csn N)) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      p0010 p0014
  have p0016 :=
    @g_a1i
      (syn_wb (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc)))
            (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wa (.classMem N (syn_cnnc)) (.neg
            (.classMem (syn_csn (syn_csn N)) (syn_crn
                (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                  (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))))
      (.classMem N (syn_cnnc)) p0015
  have p0018 :=
    @g_biantrurd (.classMem N (syn_cnnc)) (.classMem N (syn_cnnc))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0004
  have p0019 :=
    @g_bicomd (.classMem N (syn_cnnc))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      p0018
  have p0020 :=
    @g_bitrd (.classMem N (syn_cnnc))
      (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (syn_wa (.classMem N (syn_cnnc)) (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0016 p0019
  have p0021 :=
    @g_bitrd (.classMem N (syn_cnnc))
      (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
                (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                  (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))))
      (.classMem (syn_csn (syn_csn N)) (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0009 p0020
  have p0022 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C))
      (.classMem N (syn_cuni1 (syn_cuni1 (syn_cdif (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_crn
                (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                  (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      p0002 p0021
  exact p0022

@[expose]
noncomputable def g_wppbrcofnv (A : Class) (B : Class) (R : Class) (H : Class)
    (_dv_A_R : Disjoint A.fv R.fv) (hyp_wppbrcofnv_1 : Nominal.NPrf (syn_wfn H (syn_cvv)))
    (hyp_wppbrcofnv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_ccom R H) B) (syn_wbr (syn_cfv H A) R B)) :=
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
  have dv_cache_0005 : x ∉ ((syn_cfv H A)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_wbr (syn_cfv H A) R B)).fv :=
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
  have p0000 := @g_brco x A B R H dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 := @g_fnbrfvb (syn_cvv) A (.cv x) H
  have p0002 :=
    @g_mp2an (syn_wfn H (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wb (.classEq (syn_cfv H A) (.cv x)) (syn_wbr A H (.cv x))) hyp_wppbrcofnv_1
      hyp_wppbrcofnv_2 p0001
  have p0003 := @g_bicomi (.classEq (syn_cfv H A) (.cv x)) (syn_wbr A H (.cv x)) p0002
  have p0004 :=
    @g_anbi1i (syn_wbr A H (.cv x)) (.classEq (syn_cfv H A) (.cv x)) (syn_wbr (.cv x) R B)
      p0003
  have p0005 := @g_eqcom (syn_cfv H A) (.cv x)
  have p0006 :=
    @g_anbi1i (.classEq (syn_cfv H A) (.cv x)) (.classEq (.cv x) (syn_cfv H A))
      (syn_wbr (.cv x) R B) p0005
  have p0007 :=
    @g_bitri (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B))
      (syn_wa (.classEq (syn_cfv H A) (.cv x)) (syn_wbr (.cv x) R B))
      (syn_wa (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B)) p0004 p0006
  have p0008 :=
    @g_exbii (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B))
      (syn_wa (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B)) x p0007
  have p0009 := @g_fvex A H
  have p0010 := @g_breq1 (.cv x) (syn_cfv H A) B R
  have p0011 :=
    @g_ceqsexv (syn_wbr (.cv x) R B) (syn_wbr (syn_cfv H A) R B) x (syn_cfv H A)
      dv_cache_0005 dv_cache_0006 p0009 p0010
  have p0012 :=
    @g_bitri (syn_wex x (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B)))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cfv H A)) (syn_wbr (.cv x) R B)))
      (syn_wbr (syn_cfv H A) R B) p0008 p0011
  have p0013 :=
    @g_bitri (syn_wbr A (syn_ccom R H) B)
      (syn_wex x (syn_wa (syn_wbr A H (.cv x)) (syn_wbr (.cv x) R B)))
      (syn_wbr (syn_cfv H A) R B) p0000 p0012
  exact p0013

@[expose]
noncomputable def g_wpppredfamfn (C : Class) (F : Class)
    (hyp_wpppredfamfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwpppredfam F C) (syn_cvv)) :=
  by
  have p0000 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0001 := @g_cnvex F hyp_wpppredfamfn_1
  have p0002 := @g_imageex (syn_ccnv F) p0001
  have p0003 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0000 p0002
  have p0004 := @g_tcfnex
  have p0005 :=
    @g_coex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_ctcfn) p0003 p0004
  have p0006 :=
    @g_cnvex
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
      p0005
  have p0007 :=
    @g_wppimagefn
      (syn_ccnv
        (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))
      p0006
  have p0008 := @g_ssetex
  have p0009 := @g_wppimagefn (syn_csset) p0008
  have p0010 :=
    @g_fncovv
      (syn_cimage (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      (syn_cimage (syn_csset)) p0007 p0009
  have p0011 := (Nominal.classEqRefl (syn_cwpppredfam F C))
  have p0012 :=
    @g_fneq1i (syn_cvv) (syn_cwpppredfam F C)
      (syn_ccom (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cimage (syn_csset)))
      p0011
  have p0013 :=
    @g_mpbir (syn_wfn (syn_cwpppredfam F C) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_ccnv (syn_ccom
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctcfn)))) (syn_cimage (syn_csset))) (syn_cvv))
      p0010 p0012
  exact p0013

@[expose]
noncomputable def g_wpphitfamfn (C : Class) (F : Class)
    (hyp_wpppredfamfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwpphitfam F C) (syn_cvv)) :=
  by
  have p0000 := @g_wpppowlayerseqex C F hyp_wpppredfamfn_1
  have p0001 := @g_cnvex (syn_cwpppowlayerseq F C) p0000
  have p0002 := @g_wppimagefn (syn_ccnv (syn_cwpppowlayerseq F C)) p0001
  have p0003 := @g_ssetex
  have p0004 := @g_wppimagefn (syn_csset) p0003
  have p0005 :=
    @g_fncovv (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))
      p0002 p0004
  have p0006 := (Nominal.classEqRefl (syn_cwpphitfam F C))
  have p0007 :=
    @g_fneq1i (syn_cvv) (syn_cwpphitfam F C)
      (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset)))
      p0006
  have p0008 :=
    @g_mpbir (syn_wfn (syn_cwpphitfam F C) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C)))
          (syn_cimage (syn_csset))) (syn_cvv))
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

@[expose]
noncomputable def g_wppreachincbrng (C : Class) (F : Class) (N : Class) (d : Var)
    (dv_C_d : d ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv)
    (hyp_wppreachincbrng_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wral d (syn_cdm F) (syn_wb
            (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
            (.classMem (syn_csn N)
              (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))) :=
  by
  have dv_cache_0001 : d ∉ ((syn_csn (syn_csn N))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_N_d,
          not_false_eq_true])
  have dv_cache_0002 :
    d ∉ ((syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))).fv :=
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
  have dv_cache_0003 : d ∉ ((syn_cdm F)).fv :=
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
    Disjoint ((syn_csn (syn_csn (.cv d)))).fv ((syn_ccnv (syn_csset))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((syn_csn (syn_csn (.cv d)))).fv ((syn_ccnv (syn_csset))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
          exact
            (show Disjoint (((syn_csn (.cv d))).fv) (((syn_csset)).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                exact
                  (show Disjoint (((Class.cv d)).fv) (((syn_csset)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ d } : Finset Var)) (((syn_csset)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset];
                            exact
                              (show Disjoint (({ d } : Finset Var)) ((∅ : Finset Var))
                                from (by simp))))))))))
  have p0000 :=
    @g_dfima3 (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
      (syn_cpw1 (syn_cpw1 (syn_cdm F)))
  have p0001 :=
    @g_eleq2i
      (syn_cima (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
        (syn_cpw1 (syn_cpw1 (syn_cdm F))))
      (syn_crn (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
          (syn_cpw1 (syn_cpw1 (syn_cdm F)))))
      (syn_csn (syn_csn N)) p0000
  have p0002 :=
    @g_bicomi
      (.classMem (syn_csn (syn_csn N))
        (syn_cima (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
          (syn_cpw1 (syn_cpw1 (syn_cdm F)))))
      (.classMem (syn_csn (syn_csn N)) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))
      p0001
  have p0003 :=
    @g_elimapw12 d (syn_csn (syn_csn N))
      (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)) (syn_cdm F)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_bitri
      (.classMem (syn_csn (syn_csn N)) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))
      (.classMem (syn_csn (syn_csn N))
        (syn_cima (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
          (syn_cpw1 (syn_cpw1 (syn_cdm F)))))
      (syn_wrex d (syn_cdm F)
        (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
          (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))))
      p0002 p0003
  have p0005 :=
    @g_elsymdif (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
      (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)
  have p0006 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C)
        (syn_csn (syn_csn N))))
  have p0007 :=
    (Nominal.biimpRefl
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N))))
  have p0008 :=
    @g_bibi12i
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
        (syn_cwpppredmemrel F C))
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
        (syn_cwpphitmemrel F C))
      p0006 p0007
  have p0009 :=
    @g_notbii
      (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C)
          (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C)
          (syn_csn (syn_csn N))))
      (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
          (syn_cwpppredmemrel F C))
        (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
          (syn_cwpphitmemrel F C)))
      p0008
  have p0010 :=
    @g_bicomi
      (.neg (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C)
            (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C)
            (syn_csn (syn_csn N)))))
      (.neg (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
            (syn_cwpppredmemrel F C))
          (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
            (syn_cwpphitmemrel F C))))
      p0009
  have p0011 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
        (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)))
      (.neg (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
            (syn_cwpppredmemrel F C))
          (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
            (syn_cwpphitmemrel F C))))
      (.neg (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C)
            (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C)
            (syn_csn (syn_csn N)))))
      p0005 p0010
  have p0012 := (Nominal.classEqRefl (syn_cwpppredmemrel F C))
  have p0013 :=
    @g_breqi (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_cwpppredmemrel F C)
      (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) p0012
  have p0014 := @g_wpppredfamfn C F hyp_wppreachincbrng_1
  have p0015 := @g_snex (syn_csn (.cv d))
  have p0016 :=
    @g_wppbrcofnv (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_ccnv (syn_csset))
      (syn_cwpppredfam F C) dv_cache_0004 p0014 p0015
  have p0017 :=
    @g_brcnv (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))
      (syn_csn (syn_csn N)) (syn_csset)
  have p0018 := @g_snex N
  have p0019 := @g_fvex (syn_csn (syn_csn (.cv d))) (syn_cwpppredfam F C)
  have p0020 :=
    @g_brssetsn (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))
      p0018 p0019
  have p0021 :=
    @g_bitri
      (syn_wbr (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))
        (syn_ccnv (syn_csset)) (syn_csn (syn_csn N)))
      (syn_wbr (syn_csn (syn_csn N)) (syn_csset)
        (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
      p0017 p0020
  have p0022 :=
    @g_bitri
      (syn_wbr (syn_csn (syn_csn (.cv d)))
        (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) (syn_csn (syn_csn N)))
      (syn_wbr (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))
        (syn_ccnv (syn_csset)) (syn_csn (syn_csn N)))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
      p0016 p0021
  have p0023 :=
    @g_bitri
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N)))
      (syn_wbr (syn_csn (syn_csn (.cv d)))
        (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpppredfam F C)) (syn_csn (syn_csn N)))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
      p0013 p0022
  have p0024 := (Nominal.classEqRefl (syn_cwpphitmemrel F C))
  have p0025 :=
    @g_breqi (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_cwpphitmemrel F C)
      (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) p0024
  have p0026 := @g_wpphitfamfn C F hyp_wppreachincbrng_1
  have p0028 :=
    @g_wppbrcofnv (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)) (syn_ccnv (syn_csset))
      (syn_cwpphitfam F C) dv_cache_0004 p0026 p0015
  have p0029 :=
    @g_brcnv (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))
      (syn_csn (syn_csn N)) (syn_csset)
  have p0031 := @g_fvex (syn_csn (syn_csn (.cv d))) (syn_cwpphitfam F C)
  have p0032 :=
    @g_brssetsn (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))
      p0018 p0031
  have p0033 :=
    @g_bitri
      (syn_wbr (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))
        (syn_ccnv (syn_csset)) (syn_csn (syn_csn N)))
      (syn_wbr (syn_csn (syn_csn N)) (syn_csset)
        (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))
      p0029 p0032
  have p0034 :=
    @g_bitri
      (syn_wbr (syn_csn (syn_csn (.cv d)))
        (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) (syn_csn (syn_csn N)))
      (syn_wbr (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))
        (syn_ccnv (syn_csset)) (syn_csn (syn_csn N)))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))
      p0028 p0033
  have p0035 :=
    @g_bitri
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N)))
      (syn_wbr (syn_csn (syn_csn (.cv d)))
        (syn_ccom (syn_ccnv (syn_csset)) (syn_cwpphitfam F C)) (syn_csn (syn_csn N)))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))
      p0025 p0034
  have p0036 :=
    @g_bibi12i
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C) (syn_csn (syn_csn N)))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
      (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C) (syn_csn (syn_csn N)))
      (.classMem (syn_csn N) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))
      p0023 p0035
  have p0037 :=
    @g_notbii
      (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C)
          (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C)
          (syn_csn (syn_csn N))))
      (syn_wb (.classMem (syn_csn N)
          (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
          (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))
      p0036
  have p0038 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
        (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)))
      (.neg (syn_wb (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpppredmemrel F C)
            (syn_csn (syn_csn N))) (syn_wbr (syn_csn (syn_csn (.cv d))) (syn_cwpphitmemrel F C)
            (syn_csn (syn_csn N)))))
      (.neg (syn_wb (.classMem (syn_csn N)
            (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
            (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
      p0011 p0037
  have p0039 :=
    @g_rexbii
      (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
        (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C)))
      (.neg (syn_wb (.classMem (syn_csn N)
            (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
            (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
      d (syn_cdm F) p0038
  have p0040 :=
    @g_bitri
      (.classMem (syn_csn (syn_csn N)) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))
      (syn_wrex d (syn_cdm F)
        (.classMem (syn_cop (syn_csn (syn_csn (.cv d))) (syn_csn (syn_csn N)))
          (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))))
      (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N)
              (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
            (.classMem (syn_csn N)
              (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))
      p0004 p0039
  have p0041 :=
    @g_notbii
      (.classMem (syn_csn (syn_csn N)) (syn_crn
          (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
            (syn_cpw1 (syn_cpw1 (syn_cdm F))))))
      (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N)
              (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
            (.classMem (syn_csn N)
              (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))
      p0040
  have p0042 :=
    @g_dfral2
      (syn_wb (.classMem (syn_csn N)
          (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
          (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))
      d (syn_cdm F)
  have p0043 :=
    @g_bicomi
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N)
            (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
            (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
      (.neg (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N)
                (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
              (.classMem (syn_csn N)
                (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))))
      p0042
  have p0044 :=
    @g_bitri
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (.neg (syn_wrex d (syn_cdm F) (.neg (syn_wb (.classMem (syn_csn N)
                (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
              (.classMem (syn_csn N)
                (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N)
            (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
            (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
      p0041 p0043
  exact p0044

@[expose]
noncomputable def g_elwppreachincball (C : Class) (F : Class) (N : Class) (d : Var)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv) (dv_C_d : d ∉ C.fv)
    (dv_F_N : Disjoint F.fv N.fv) (dv_F_d : d ∉ F.fv) (dv_N_d : d ∉ N.fv)
    (hyp_elwppreachincball_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem N (syn_cwppreachincb F C))
          (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N)
                (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
              (.classMem (syn_csn N)
                (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))) :=
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
  have p0000 := @g_elwppreachincb C F N dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_wppreachincbrng C F N d dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_elwppreachincball_1
  have p0002 :=
    @g_a1i
      (syn_wb (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
              (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
                (syn_cpw1 (syn_cpw1 (syn_cdm F))))))) (syn_wral d (syn_cdm F) (syn_wb
            (.classMem (syn_csn N) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
            (.classMem (syn_csn N)
              (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))))
      (.classMem N (syn_cnnc)) p0001
  have p0003 :=
    @g_bitrd (.classMem N (syn_cnnc)) (.classMem N (syn_cwppreachincb F C))
      (.neg (.classMem (syn_csn (syn_csn N)) (syn_crn
            (syn_cres (syn_csymdif (syn_cwpppredmemrel F C) (syn_cwpphitmemrel F C))
              (syn_cpw1 (syn_cpw1 (syn_cdm F)))))))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn N)
            (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d))))) (.classMem (syn_csn N)
            (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_wppreachincblayers (C : Class) (n : Var) (F : Class) (d : Var)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv) (dv_C_n : n ∉ C.fv)
    (dv_F_d : d ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_d_n : d ≠ n)
    (hyp_wppreachincblayers_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C))
          (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                  (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                  (syn_ctc (.cv n)))) (.classMem (.cv d)
                (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))))) :=
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
    @g_elwppreachincball C F (.cv n) d dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wppreachincblayers_1
  have p0001 := @g_vex d
  have p0002 := @g_elwpppredfam C (.cv d) F n hyp_wppreachincblayers_1 p0001
  have p0004 := @g_elwpphitfam C (.cv d) F n hyp_wppreachincblayers_1 p0001
  have p0005 :=
    @g_bibi12i
      (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv n))))
      (.classMem (syn_csn (.cv n)) (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))
      (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) p0002
      p0004
  have p0006 :=
    @g_ralbii
      (syn_wb (.classMem (syn_csn (.cv n))
          (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
        (.classMem (syn_csn (.cv n))
          (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d))))))
      (syn_wb (.classMem (.cv d)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv n))))
        (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))
      d (syn_cdm F) p0005
  have p0007 :=
    @g_a1i
      (syn_wb (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn (.cv n))
              (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
            (.classMem (syn_csn (.cv n))
              (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
        (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc (.cv n))))
            (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))))
      (.classMem (.cv n) (syn_cnnc)) p0006
  have p0008 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwppreachincb F C))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (syn_csn (.cv n))
            (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn (.cv d)))))
          (.classMem (syn_csn (.cv n))
            (syn_cfv (syn_cwpphitfam F C) (syn_csn (syn_csn (.cv d)))))))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv n))))
          (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))))
      p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wpppowcorefn (F : Class)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc)) :=
  by
  have p0000 := @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0001 := @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0004 := @g_elfuns (syn_cwpppostcomp F) p0003
  have p0005 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F))
      p0002 p0004
  have p0006 := @g_idex
  have p0008 := @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0006 p0009
  have p0011 := @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0015 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F))
      p0011 p0009
  have p0016 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns))
      (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F)))
      (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0005 p0010
      p0015
  have p0017 := @g_wpporbitfnndv (syn_cwpppostcomp F) (syn_cid)
  have p0018 := Nominal.mp p0016 p0017
  exact p0018

@[expose]
noncomputable def g_wpppowcore0 (F : Class)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid)) :=
  by
  have p0000 := @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0001 := @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0004 := @g_elfuns (syn_cwpppostcomp F) p0003
  have p0005 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F))
      p0002 p0004
  have p0006 := @g_idex
  have p0008 := @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0006 p0009
  have p0011 := @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0015 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F))
      p0011 p0009
  have p0016 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns))
      (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F)))
      (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0005 p0010
      p0015
  have p0017 := @g_wpporbit0ndv (syn_cwpppostcomp F) (syn_cid)
  have p0018 := Nominal.mp p0016 p0017
  exact p0018

@[expose]
noncomputable def g_wpppowcoresuc (n : Var) (F : Class) (_dv_F_n : n ∉ F.fv)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))) :=
  by
  have p0000 := @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0001 := @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0004 := @g_elfuns (syn_cwpppostcomp F) p0003
  have p0005 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F))
      p0002 p0004
  have p0006 := @g_idex
  have p0008 := @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0009 := Nominal.mp p0000 p0008
  have p0010 := @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0006 p0009
  have p0011 := @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0015 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F))
      p0011 p0009
  have p0016 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns))
      (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F)))
      (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0005 p0010
      p0015
  have p0017 := @g_wpporbitsucndv (syn_cwpppostcomp F) (syn_cid) (.cv n)
  have p0018 :=
    @g_mpan
      (syn_w3a (.classMem (syn_cwpppostcomp F) (syn_cfuns))
        (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F)))
        (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))))
      (.classMem (.cv n) (syn_cnnc))
      (.classEq
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cfv (syn_cwpppostcomp F)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      p0016 p0017
  have p0019 := @g_fvex (.cv n) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0020 :=
    @g_wpppostcompfv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F
      hyp_wpppowcorefn_1 p0019
  have p0021 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwpppostcomp F)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0020
  have p0022 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cfv (syn_cwpppostcomp F)
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) p0018
      p0021
  exact p0022

@[expose]
noncomputable def g_wpppowlayerseqfv (C : Class) (n : Var) (F : Class)
    (_dv_C_F : Disjoint C.fv F.fv) (_dv_C_n : n ∉ C.fv) (_dv_F_n : n ∉ F.fv)
    (hyp_wpppowcorefn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc))
        (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv
              (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
            (syn_cima (syn_clec) (syn_csn C))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowlayerseq F C))
  have p0001 :=
    @g_fveq1i (syn_csn (.cv n)) (syn_cwpppowlayerseq F C)
      (syn_ccom (syn_cwppupperpreop C)
        (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cfv
          (syn_ccom (syn_cwppupperpreop C)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
          (syn_csn (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0001
  have p0003 := @g_wpppostcompfn F hyp_wpppowcorefn_1
  have p0004 := @g_fnfun (syn_cvv) (syn_cwpppostcomp F)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_wpppostcompex F hyp_wpppowcorefn_1
  have p0007 := @g_elfuns (syn_cwpppostcomp F) p0006
  have p0008 :=
    @g_mpbir (.classMem (syn_cwpppostcomp F) (syn_cfuns)) (syn_wfun (syn_cwpppostcomp F))
      p0005 p0007
  have p0009 := @g_idex
  have p0011 := @g_fndm (syn_cvv) (syn_cwpppostcomp F)
  have p0012 := Nominal.mp p0003 p0011
  have p0013 := @g_eleqtrri (syn_cid) (syn_cvv) (syn_cdm (syn_cwpppostcomp F)) p0009 p0012
  have p0014 := @g_ssv (syn_crn (syn_cwpppostcomp F))
  have p0018 :=
    @g_sseqtr4i (syn_crn (syn_cwpppostcomp F)) (syn_cvv) (syn_cdm (syn_cwpppostcomp F))
      p0014 p0012
  have p0019 :=
    @g_n_3pm3_2i (.classMem (syn_cwpppostcomp F) (syn_cfuns))
      (.classMem (syn_cid) (syn_cdm (syn_cwpppostcomp F)))
      (syn_wss (syn_crn (syn_cwpppostcomp F)) (syn_cdm (syn_cwpppostcomp F))) p0008 p0013
      p0018
  have p0020 := @g_wpporbitfnndv (syn_cwpppostcomp F) (syn_cid)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @g_fntcfn
  have p0025 := @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn))
      p0023 p0026
  have p0028 := @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (.classMem (.cv n) (syn_cnnc)) p0029
  have p0031 := @g_nntccl (.cv n)
  have p0032 := @g_vex n
  have p0033 := @g_tcfnfv (.cv n) p0032
  have p0034 :=
    @g_a1i (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)))
      (.classMem (.cv n) (syn_cnnc)) p0033
  have p0035 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
      (syn_ctc (.cv n)) (syn_cnnc) p0034
  have p0036 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0031 p0035
  have p0056 := @g_fndm (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0057 := Nominal.mp p0021 p0056
  have p0058 :=
    @g_eleq2i (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cnnc)
      (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) p0057
  have p0059 :=
    @g_a1i
      (syn_wb (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
          (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
        (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0058
  have p0060 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
        (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) p0036 p0059
  have p0065 := @g_snel1c (.cv n) p0032
  have p0067 := @g_fndm (syn_c1c) (syn_ctcfn)
  have p0068 := Nominal.mp p0024 p0067
  have p0069 := @g_eleqtrri (syn_csn (.cv n)) (syn_c1c) (syn_cdm (syn_ctcfn)) p0065 p0068
  have p0070 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn)))
      p0026 p0069
  have p0071 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0072 := Nominal.mp p0070 p0071
  have p0073 :=
    @g_a1i
      (syn_wb (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
        (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
          (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
      (.classMem (.cv n) (syn_cnnc)) p0072
  have p0074 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n))
        (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
        (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      p0060 p0073
  have p0075 :=
    @g_jca (.classMem (.cv n) (syn_cnnc))
      (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (.classMem (syn_csn (.cv n))
        (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      p0030 p0074
  have p0076 :=
    @g_fvco (syn_csn (.cv n)) (syn_cwppupperpreop C)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0077 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
        (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
      (.classEq (syn_cfv (syn_ccom (syn_cwppupperpreop C)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
          (syn_csn (.cv n))) (syn_cfv (syn_cwppupperpreop C)
          (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
            (syn_csn (.cv n)))))
      p0075 p0076
  have p0081 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn (.cv n)) (syn_c1c))
      p0024 p0065
  have p0082 :=
    @g_fvco2 (syn_c1c) (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      (syn_ctcfn)
  have p0083 := Nominal.mp p0081 p0082
  have p0086 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0033
  have p0087 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
        (syn_csn (.cv n)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_cfv (syn_ctcfn) (syn_csn (.cv n))))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0083 p0086
  have p0088 :=
    @g_a1i
      (.classEq (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
          (syn_csn (.cv n)))
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0087
  have p0089 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
        (syn_csn (.cv n)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
      (syn_cwppupperpreop C) p0088
  have p0090 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppupperpreop C)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))
      (syn_cfv (syn_cwppupperpreop C)
        (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
          (syn_csn (.cv n))))
      (syn_cfv (syn_cwppupperpreop C)
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      p0077 p0089
  have p0091 := @g_fvex (syn_ctc (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0092 :=
    @g_wppupperpreopfv C
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0091
  have p0093 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppupperpreop C)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima
          (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
          (syn_cima (syn_clec) (syn_csn C))))
      (.classMem (.cv n) (syn_cnnc)) p0092
  have p0094 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppupperpreop C)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))
      (syn_cfv (syn_cwppupperpreop C)
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      (syn_cima
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_clec) (syn_csn C)))
      p0090 p0093
  have p0095 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))
      (syn_cfv (syn_ccom (syn_cwppupperpreop C)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))
      (syn_cima
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_clec) (syn_csn C)))
      p0002 p0094
  exact p0095

@[expose]
noncomputable def g_wppimageatex (D : Class)
    (_hyp_wppimageatex_1 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppimageat D) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppimageat D))
  have p0001 := @g_lnimageopex
  have p0002 := @g_idex
  have p0003 := @g_vvex
  have p0004 := @g_snex (syn_csn D)
  have p0005 := @g_xpex (syn_cvv) (syn_csn (syn_csn D)) p0003 p0004
  have p0006 := @g_txpex (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) p0002 p0005
  have p0007 :=
    @g_coex (syn_clnimageop)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_cwppimageat D)
      (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))))
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wppimageatfn (D : Class)
    (_hyp_wppimageatfn_1 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwppimageat D) (syn_cvv)) :=
  by
  have p0000 := @g_lnimageopfn
  have p0001 := @g_f1ovi
  have p0002 := @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_snex D
  have p0005 := @g_fnconstg (syn_cvv) (syn_csn D) (syn_cvv)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_inidm (syn_cvv)
  have p0011 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0010
  have p0012 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cvv))
      p0009 p0011
  have p0013 :=
    @g_fncovv (syn_clnimageop)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0000 p0012
  have p0014 := (Nominal.classEqRefl (syn_cwppimageat D))
  have p0015 :=
    @g_fneq1i (syn_cvv) (syn_cwppimageat D)
      (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))))
      p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_cwppimageat D) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) (syn_cvv))
      p0013 p0015
  exact p0016

@[expose]
noncomputable def g_wppimageatfv (D : Class) (R : Class)
    (_hyp_wppimageatfv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_wppimageatfv_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppimageat D) R) (syn_cima R (syn_csn D))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppimageat D))
  have p0001 :=
    @g_fveq1i R (syn_cwppimageat D)
      (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))))
      p0000
  have p0002 := @g_f1ovi
  have p0003 := @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_snex D
  have p0006 := @g_fnconstg (syn_cvv) (syn_csn D) (syn_cvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_inidm (syn_cvv)
  have p0012 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) p0011
  have p0013 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cvv))
      p0010 p0012
  have p0014 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) (syn_cvv))
      (.classMem R (syn_cvv)) p0013 hyp_wppimageatfv_2
  have p0015 :=
    @g_fvco2 (syn_cvv) R (syn_clnimageop)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))
  have p0016 := Nominal.mp p0014 p0015
  have p0023 :=
    @g_fvtxpvv R (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) p0004 p0007
      hyp_wppimageatfv_2
  have p0024 := @g_fvi R (syn_cvv)
  have p0025 := Nominal.mp hyp_wppimageatfv_2 p0024
  have p0027 := @g_fvconst2 (syn_cvv) (syn_csn D) R p0005
  have p0028 := Nominal.mp hyp_wppimageatfv_2 p0027
  have p0029 :=
    @g_opeq12i (syn_cfv (syn_cid) R) R
      (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) R) (syn_csn D) p0025 p0028
  have p0030 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) R)
      (syn_cop (syn_cfv (syn_cid) R) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_csn D))) R))
      (syn_cop R (syn_csn D)) p0023 p0029
  have p0031 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) R)
      (syn_cop R (syn_csn D)) (syn_clnimageop) p0030
  have p0032 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) R)
      (syn_cfv (syn_clnimageop)
        (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D)))) R))
      (syn_cfv (syn_clnimageop) (syn_cop R (syn_csn D))) p0016 p0031
  have p0034 := @g_lnimageopval (syn_csn D) R hyp_wppimageatfv_2 p0005
  have p0035 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) R)
      (syn_cfv (syn_clnimageop) (syn_cop R (syn_csn D))) (syn_cima R (syn_csn D)) p0032
      p0034
  have p0036 :=
    @g_eqtri (syn_cfv (syn_cwppimageat D) R)
      (syn_cfv (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn (syn_csn D))))) R)
      (syn_cima R (syn_csn D)) p0001 p0035
  exact p0036

@[expose]
noncomputable def g_wpppowateqex (D : Class) (F : Class)
    (hyp_wpppowateqex_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wpppowateqex_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppowateq F D) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowateq F D))
  have p0001 := @g_wppimageatex D hyp_wpppowateqex_2
  have p0002 := @g_wpppostcompex F hyp_wpppowateqex_1
  have p0003 := @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0004 :=
    @g_frecexg (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid)
      (syn_cvv) p0003
  have p0005 := Nominal.mp p0002 p0004
  have p0006 := @g_tcfnex
  have p0007 :=
    @g_pm3_2i (.classMem (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cvv))
      (.classMem (syn_ctcfn) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_coexg (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn) (syn_cvv) (syn_cvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_pm3_2i (.classMem (syn_cwppimageat D) (syn_cvv))
      (.classMem (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_cvv))
      p0001 p0009
  have p0011 :=
    @g_coexg (syn_cwppimageat D)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_cvv)
      (syn_cvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_cnvexg
      (syn_ccom (syn_cwppimageat D)
        (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (syn_cvv)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @g_eqid (syn_cfrec F D)
  have p0016 := @g_frecexg (syn_cfrec F D) F D (syn_cvv) p0015
  have p0017 := Nominal.mp hyp_wpppowateqex_1 p0016
  have p0018 := @g_siexg (syn_cfrec F D) (syn_cvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i
      (.classMem (syn_ccnv (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_cvv))
      (.classMem (syn_csi (syn_cfrec F D)) (syn_cvv)) p0014 p0019
  have p0021 :=
    @g_coexg
      (syn_ccnv (syn_ccom (syn_cwppimageat D)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      (syn_csi (syn_cfrec F D)) (syn_cvv) (syn_cvv)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_fixexg
      (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
        (syn_csi (syn_cfrec F D)))
      (syn_cvv)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_uni1exg
      (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
              (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
          (syn_csi (syn_cfrec F D))))
      (syn_cvv)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_eqeltri (syn_cwpppowateq F D)
      (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
                (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
            (syn_csi (syn_cfrec F D)))))
      (syn_cvv) p0000 p0026
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

@[expose]
noncomputable def g_wpppowateqval (D : Class) (n : Var) (F : Class)
    (hyp_wpppowateqval_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpppowateqval_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wpppowateqval_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D))
          (.classEq (syn_cima
              (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
              (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowateq F D))
  have p0001 :=
    @g_eleq2i (syn_cwpppowateq F D)
      (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
                (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
            (syn_csi (syn_cfrec F D)))))
      (.cv n) p0000
  have p0002 := @g_vex n
  have p0003 :=
    @g_eluni1 (.cv n)
      (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
              (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
          (syn_csi (syn_cfrec F D))))
      p0002
  have p0004 :=
    @g_bitri (.classMem (.cv n) (syn_cwpppowateq F D))
      (.classMem (.cv n) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
                  (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
              (syn_csi (syn_cfrec F D))))))
      (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
                (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
            (syn_csi (syn_cfrec F D)))))
      p0001 p0003
  have p0005 :=
    @g_a1i
      (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem (syn_csn (.cv n)) (syn_cfix
            (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
                  (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
              (syn_csi (syn_cfrec F D))))))
      (.classMem (.cv n) (syn_cnnc)) p0004
  have p0006 := @g_elex D (syn_cdm F)
  have p0007 := Nominal.mp hyp_wpppowateqval_2 p0006
  have p0008 := @g_wppimageatfn D p0007
  have p0009 := @g_fnfun (syn_cvv) (syn_cwppimageat D)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_elex F (syn_cfuns)
  have p0012 := Nominal.mp hyp_wpppowateqval_1 p0011
  have p0013 := @g_wpppowcorefn F p0012
  have p0014 := @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_fntcfn
  have p0017 := @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn))
      p0015 p0018
  have p0020 := @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 :=
    @g_pm3_2i (syn_wfun (syn_cwppimageat D))
      (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) p0010
      p0021
  have p0023 :=
    @g_funco (syn_cwppimageat D)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_a1i
      (syn_wfun (syn_ccom (syn_cwppimageat D)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      (.classMem (.cv n) (syn_cnnc)) p0024
  have p0026 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqval_1 hyp_wpppowateqval_2
      hyp_wpppowateqval_3
  have p0027 := @g_wpporbitfnndv F D
  have p0028 := Nominal.mp p0026 p0027
  have p0029 := @g_fnfun (syn_cnnc) (syn_cfrec F D)
  have p0030 := Nominal.mp p0028 p0029
  have p0031 := @g_funsi (syn_cfrec F D)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @g_a1i (syn_wfun (syn_csi (syn_cfrec F D))) (.classMem (.cv n) (syn_cnnc)) p0032
  have p0034 :=
    @g_fvex (syn_csn (.cv n))
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0038 := @g_fndm (syn_cvv) (syn_cwppimageat D)
  have p0039 := Nominal.mp p0008 p0038
  have p0040 :=
    @g_eleqtrri
      (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
        (syn_csn (.cv n)))
      (syn_cvv) (syn_cdm (syn_cwppimageat D)) p0034 p0039
  have p0041 :=
    @g_a1i
      (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
          (syn_csn (.cv n))) (syn_cdm (syn_cwppimageat D)))
      (.classMem (.cv n) (syn_cnnc)) p0040
  have p0053 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (.classMem (.cv n) (syn_cnnc)) p0021
  have p0054 := @g_nntccl (.cv n)
  have p0056 := @g_tcfnfv (.cv n) p0002
  have p0057 :=
    @g_a1i (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)))
      (.classMem (.cv n) (syn_cnnc)) p0056
  have p0058 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
      (syn_ctc (.cv n)) (syn_cnnc) p0057
  have p0059 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0054 p0058
  have p0063 := @g_fndm (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0064 := Nominal.mp p0013 p0063
  have p0065 :=
    @g_eleq2i (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cnnc)
      (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) p0064
  have p0066 :=
    @g_a1i
      (syn_wb (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
          (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
        (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0065
  have p0067 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
        (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) p0059 p0066
  have p0072 := @g_snel1c (.cv n) p0002
  have p0074 := @g_fndm (syn_c1c) (syn_ctcfn)
  have p0075 := Nominal.mp p0016 p0074
  have p0076 := @g_eleqtrri (syn_csn (.cv n)) (syn_c1c) (syn_cdm (syn_ctcfn)) p0072 p0075
  have p0077 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn)))
      p0018 p0076
  have p0078 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0079 := Nominal.mp p0077 p0078
  have p0080 :=
    @g_a1i
      (syn_wb (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
        (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
          (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
      (.classMem (.cv n) (syn_cnnc)) p0079
  have p0081 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n))
        (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))
        (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      p0067 p0080
  have p0082 :=
    @g_jca (.classMem (.cv n) (syn_cnnc))
      (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (.classMem (syn_csn (.cv n))
        (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      p0053 p0081
  have p0083 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cwppimageat D)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0084 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
        (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
      (syn_wb (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D)
              (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classMem
          (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
            (syn_csn (.cv n))) (syn_cdm (syn_cwppimageat D))))
      p0082 p0083
  have p0085 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
      (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
          (syn_csn (.cv n))) (syn_cdm (syn_cwppimageat D)))
      p0041 p0084
  have p0086 := @g_snelpw1 (.cv n) (syn_cnnc)
  have p0087 :=
    @g_biimpri (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0086
  have p0088 := @g_dmsi (syn_cfrec F D)
  have p0092 := @g_fndm (syn_cnnc) (syn_cfrec F D)
  have p0093 := Nominal.mp p0028 p0092
  have p0094 := @g_pw1eq (syn_cdm (syn_cfrec F D)) (syn_cnnc)
  have p0095 := Nominal.mp p0093 p0094
  have p0096 :=
    @g_eqtri (syn_cdm (syn_csi (syn_cfrec F D))) (syn_cpw1 (syn_cdm (syn_cfrec F D)))
      (syn_cpw1 (syn_cnnc)) p0088 p0095
  have p0097 :=
    @g_a1i (.classEq (syn_cdm (syn_csi (syn_cfrec F D))) (syn_cpw1 (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0096
  have p0098 :=
    @g_eleqtrrd (.classMem (.cv n) (syn_cnnc)) (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc))
      (syn_cdm (syn_csi (syn_cfrec F D))) p0087 p0097
  have p0099 :=
    @g_jca (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
      (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F D)))) p0085 p0098
  have p0100 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc))
      (syn_wfun (syn_ccom (syn_cwppimageat D)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
      (syn_wfun (syn_csi (syn_cfrec F D)))
      (syn_wa (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D)
              (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
        (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F D)))))
      p0025 p0033 p0099
  have p0101 :=
    @g_funeqfix (syn_csn (.cv n))
      (syn_ccom (syn_cwppimageat D)
        (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (syn_csi (syn_cfrec F D))
  have p0102 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_w3a (syn_wfun (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
        (syn_wfun (syn_csi (syn_cfrec F D))) (syn_wa (.classMem (syn_csn (.cv n)) (syn_cdm
              (syn_ccom (syn_cwppimageat D)
                (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
          (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F D))))))
      (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv
                (syn_ccom (syn_cwppimageat D)
                  (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
              (syn_csi (syn_cfrec F D))))) (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D)
              (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
            (syn_csn (.cv n))) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n)))))
      p0100 p0101
  have p0103 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowateq F D))
      (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D)
                (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))
            (syn_csi (syn_cfrec F D)))))
      (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
          (syn_csn (.cv n))) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n))))
      p0005 p0102
  have p0145 :=
    @g_fvco (syn_csn (.cv n)) (syn_cwppimageat D)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0146 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
        (.classMem (syn_csn (.cv n))
          (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))))
      (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
          (syn_csn (.cv n))) (syn_cfv (syn_cwppimageat D)
          (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
            (syn_csn (.cv n)))))
      p0082 p0145
  have p0150 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn (.cv n)) (syn_c1c))
      p0016 p0072
  have p0151 :=
    @g_fvco2 (syn_c1c) (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      (syn_ctcfn)
  have p0152 := Nominal.mp p0150 p0151
  have p0155 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0056
  have p0156 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
        (syn_csn (.cv n)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_cfv (syn_ctcfn) (syn_csn (.cv n))))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0152 p0155
  have p0157 :=
    @g_a1i
      (.classEq (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
          (syn_csn (.cv n)))
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0156
  have p0158 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
        (syn_csn (.cv n)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
      (syn_cwppimageat D) p0157
  have p0159 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppimageat D)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))
      (syn_cfv (syn_cwppimageat D)
        (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
          (syn_csn (.cv n))))
      (syn_cfv (syn_cwppimageat D)
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      p0146 p0158
  have p0162 := @g_fvex (syn_ctc (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0163 :=
    @g_wppimageatfv D
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0007 p0162
  have p0164 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppimageat D)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
          (syn_csn D)))
      (.classMem (.cv n) (syn_cnnc)) p0163
  have p0165 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppimageat D)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))
      (syn_cfv (syn_cwppimageat D)
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
        (syn_csn D))
      p0159 p0164
  have p0169 := @g_sifnvalv n (syn_cnnc) (syn_cfrec F D)
  have p0170 :=
    @g_mpan (syn_wfn (syn_cfrec F D) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n)))
        (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))))
      p0028 p0169
  have p0171 :=
    @g_eqeq12d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppimageat D)
          (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n)))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
        (syn_csn D))
      (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n)))
      (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))) p0165 p0170
  have p0172 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowateq F D))
      (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D)
            (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
          (syn_csn (.cv n))) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n))))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))))
      p0103 p0171
  exact p0172

@[expose]
noncomputable def g_wpppowateqvalcl (B : Class) (D : Class) (F : Class)
    (hyp_wpppowateqvalcl_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpppowateqvalcl_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wpppowateqvalcl_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq
            (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))
              (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B))))) :=
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
      ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq
              (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))
                (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B)))))).fv :=
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
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwpppowateq F D) p0001
  have p0006 := @g_tceq (.cv n) B
  have p0007 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0001 p0006
  have p0008 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B)
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0007
  have p0009 :=
    @g_imaeq1d (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D) p0008
  have p0011 := @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F D) p0001
  have p0012 :=
    @g_sneqd (.classEq (.cv n) B) (syn_cfv (syn_cfrec F D) (.cv n))
      (syn_cfv (syn_cfrec F D) B) p0011
  have p0013 :=
    @g_eqeq12d (.classEq (.cv n) B)
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
        (syn_csn D))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D))
      (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))) (syn_csn (syn_cfv (syn_cfrec F D) B))
      p0009 p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwpppowateq F D))
      (.classMem B (syn_cwpppowateq F D))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B)))
      p0004 p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classEq
          (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
            (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))))
      (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq
          (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))
            (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B))))
      p0002 p0014
  have p0016 :=
    @g_wpppowateqval D n F hyp_wpppowateqvalcl_1 hyp_wpppowateqvalcl_2
      hyp_wpppowateqvalcl_3
  have p0017 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D))
          (.classEq (syn_cima
              (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
              (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))))))
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq
            (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))
              (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B)))))
      n B (syn_cnnc) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq
          (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B))
            (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B))))
      p0000 p0017
  exact p0018

@[expose]
noncomputable def g_wpppowcoresuccl (B : Class) (F : Class)
    (hyp_wpppowcoresuccl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (.classEq
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) :=
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
      ((Wff.imp (.classMem B (syn_cnnc)) (.classEq
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
            (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))).fv :=
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
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_addceq1d (.classEq (.cv n) B) (.cv n) B (syn_c1c) p0001
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc B (syn_c1c))
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0004
  have p0007 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      p0001
  have p0008 :=
    @g_coeq2d (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F p0007
  have p0009 :=
    @g_eqeq12d (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) p0005 p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (.classEq
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))
      p0002 p0009
  have p0011 := @g_wpppowcoresuc n F dv_cache_0001 hyp_wpppowcoresuccl_1
  have p0012 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))))
      (.imp (.classMem B (syn_cnnc)) (.classEq
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))
      n B (syn_cnnc) dv_cache_0002 dv_cache_0003 p0010 p0011
  have p0013 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))
      p0000 p0012
  exact p0013

@[expose]
noncomputable def g_wpppowateqall (D : Class) (F : Class) (N : Class)
    (hyp_wpppowateqall_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpppowateqall_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wpppowateqall_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_cwpppowateq F D))) :=
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
  have dv_cache_0001 : n ∉ ((syn_cwpppowateq F D)).fv := by
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
  have dv_cache_0003 : n ∉ ((Wff.classMem (.cv m) (syn_cwpppowateq F D))).fv :=
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
  have dv_cache_0004 : m ∉ ((Wff.classMem (.cv n) (syn_cwpppowateq F D))).fv :=
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
  have dv_cache_0005 : n ∉ ((Wff.classMem (syn_c0c) (syn_cwpppowateq F D))).fv :=
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
  have dv_cache_0006 : n ∉ ((Wff.classMem N (syn_cwpppowateq F D))).fv :=
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
    n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D))).fv :=
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
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wpppowateqall_1 p0000
  have p0002 := @g_elex D (syn_cdm F)
  have p0003 := Nominal.mp hyp_wpppowateqall_2 p0002
  have p0004 := @g_wpppowateqex D F p0001 p0003
  have p0005 := @g_abid2 n (syn_cwpppowateq F D) dv_cache_0001
  have p0006 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cwpppowateq F D))) (syn_cwpppowateq F D)
      (syn_cvv) p0005
  have p0007 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cwpppowateq F D))) (syn_cvv))
      (.classMem (syn_cwpppowateq F D) (syn_cvv)) p0004 p0006
  have p0008 := @g_id (.classEq (.cv n) (syn_c0c))
  have p0009 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cwpppowateq F D) p0008
  have p0010 := @g_id (.classEq (.cv n) (.cv m))
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwpppowateq F D) p0010
  have p0012 := @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0013 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n)
      (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D) p0012
  have p0014 := @g_id (.classEq (.cv n) N)
  have p0015 := @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cwpppowateq F D) p0014
  have p0016 := @g_tc0c
  have p0017 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      p0016
  have p0020 := @g_wpppowcore0 F p0001
  have p0021 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) p0017 p0020
  have p0022 :=
    @g_imaeq1i (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
      (syn_cid) (syn_csn D) p0021
  have p0023 := @g_imai (syn_csn D)
  have p0024 :=
    @g_eqtri
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
        (syn_csn D))
      (syn_cima (syn_cid) (syn_csn D)) (syn_csn D) p0022 p0023
  have p0025 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqall_1 hyp_wpppowateqall_2
      hyp_wpppowateqall_3
  have p0026 := @g_wpporbit0ndv F D
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @g_sneqi (syn_cfv (syn_cfrec F D) (syn_c0c)) D p0027
  have p0029 := @g_eqcomi (syn_csn (syn_cfv (syn_cfrec F D) (syn_c0c))) (syn_csn D) p0028
  have p0030 :=
    @g_eqtri
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
        (syn_csn D))
      (syn_csn D) (syn_csn (syn_cfv (syn_cfrec F D) (syn_c0c))) p0024 p0029
  have p0031 := @g_peano1
  have p0032 :=
    @g_wpppowateqvalcl (syn_c0c) D F hyp_wpppowateqall_1 hyp_wpppowateqall_2
      hyp_wpppowateqall_3
  have p0033 := Nominal.mp p0031 p0032
  have p0034 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwpppowateq F D))
      (.classEq
        (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c)))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (syn_c0c))))
      p0030 p0033
  have p0035 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0036 := @g_nntcsuc (.cv m)
  have p0037 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      p0035 p0036
  have p0038 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0037
  have p0040 := @g_nntccl (.cv m)
  have p0041 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0035 p0040
  have p0044 := @g_wpppowcoresuccl (syn_ctc (.cv m)) F p0001
  have p0045 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (syn_ctc (.cv m)) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_ccom F
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))))
      p0041 p0044
  have p0046 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_ctc (syn_cplc (.cv m) (syn_c1c))))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))))
      p0038 p0045
  have p0047 :=
    @g_imaeq1d
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_ctc (syn_cplc (.cv m) (syn_c1c))))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))))
      (syn_csn D) p0046
  have p0048 :=
    @g_imaco F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
      (syn_csn D)
  have p0049 :=
    @g_a1i
      (.classEq (syn_cima (syn_ccom F
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))) (syn_csn D))
        (syn_cima F
          (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
            (syn_csn D))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      p0048
  have p0050 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D))
      (syn_cima (syn_ccom F
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))) (syn_csn D))
      (syn_cima F
        (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
          (syn_csn D)))
      p0047 p0049
  have p0051 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0053 :=
    @g_wpppowateqval D m F hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0054 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wb (.classMem (.cv m) (syn_cwpppowateq F D)) (.classEq
          (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
            (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))))
      p0035 p0053
  have p0055 :=
    @g_biimpd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cwpppowateq F D))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))))
      p0054
  have p0056 :=
    @g_mpd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cwpppowateq F D))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))))
      p0051 p0055
  have p0057 :=
    @g_imaeq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
        (syn_csn D))
      (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))) F p0056
  have p0058 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D))
      (syn_cima F
        (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))
          (syn_csn D)))
      (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) p0050 p0057
  have p0059 := @g_elfunsi F
  have p0060 := Nominal.mp hyp_wpppowateqall_1 p0059
  have p0061 := @g_funfn F
  have p0062 := @g_biimpi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0061
  have p0063 := Nominal.mp p0060 p0062
  have p0064 :=
    @g_a1i (syn_wfn F (syn_cdm F))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      p0063
  have p0067 := @g_frecdomfv F D (.cv m)
  have p0068 :=
    @g_mpan
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F)) p0025 p0067
  have p0069 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F)) p0035 p0068
  have p0070 :=
    @g_jca
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_wfn F (syn_cdm F)) (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F))
      p0064 p0069
  have p0071 := @g_fnsnfv (syn_cdm F) (syn_cfv (syn_cfrec F D) (.cv m)) F
  have p0072 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_wa (syn_wfn F (syn_cdm F)) (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F)))
      (.classEq (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))))
        (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))))
      p0070 p0071
  have p0073 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))))
      (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) p0072
  have p0074 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D))
      (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))))
      (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) p0058 p0073
  have p0077 := @g_wpporbitsucndv F D (.cv m)
  have p0078 :=
    @g_mpan
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))))
      p0025 p0077
  have p0079 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))))
      p0035 p0078
  have p0080 :=
    @g_sneqd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))
      (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))) p0079
  have p0081 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c))))
      (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) p0080
  have p0082 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D))
      (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))))
      (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))) p0074 p0081
  have p0084 := @g_peano2 (.cv m)
  have p0085 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      p0035 p0084
  have p0086 :=
    @g_wpppowateqvalcl (syn_cplc (.cv m) (syn_c1c)) D F hyp_wpppowateqall_1
      hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0087 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D)) (.classEq (syn_cima
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
              (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D))
          (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c))))))
      p0085 p0086
  have p0088 :=
    @g_mpbird
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
            (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D))
        (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))))
      p0082 p0087
  have p0089 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D)) p0088
  have p0090_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D))
          (.classMem (.cv m) (syn_cwpppowateq F D)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpppowateq syn_cuni1 syn_cuni syn_wex syn_wa syn_cin syn_ccompl
          syn_cnin syn_wnan syn_c1c syn_cfix syn_crn syn_cima syn_wrex syn_wbr syn_cop
          syn_cun syn_cvv syn_ccom syn_copab syn_ccnv syn_csi syn_cfrec syn_cclos1
          syn_cint syn_csn syn_cpprod syn_ctxp syn_cmpt syn_cplc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0090 :=
    @g_finds (.classMem (.cv n) (syn_cwpppowateq F D))
      (.classMem (syn_c0c) (syn_cwpppowateq F D))
      (.classMem (.cv m) (syn_cwpppowateq F D))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D))
      (.classMem N (syn_cwpppowateq F D)) n m N dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0007 p0009
      p0090_e02_recanon p0013 p0015 p0034 p0089
  exact p0090

@[expose]
noncomputable def g_wpppowatact (D : Class) (F : Class) (N : Class)
    (hyp_wpppowatact_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpppowatact_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wpppowatact_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (.classEq
          (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc N))
            (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) N)))) :=
  by
  have p0000 :=
    @g_wpppowateqall D F N hyp_wpppowatact_1 hyp_wpppowatact_2 hyp_wpppowatact_3
  have p0001 :=
    @g_wpppowateqvalcl N D F hyp_wpppowatact_1 hyp_wpppowatact_2 hyp_wpppowatact_3
  have p0002 :=
    @g_mpbid (.classMem N (syn_cnnc)) (.classMem N (syn_cwpppowateq F D))
      (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc N))
          (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) N)))
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

@[expose]
noncomputable def g_wpppreimaactsnd (ph : Wff) (D : Class) (R : Class) (U : Class)
    (O : Class) (_hyp_wpppreimaactsnd_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_wpppreimaactsnd_2 : Nominal.NPrf (.classMem O (syn_cvv)))
    (hyp_wpppreimaactsnd_3 :
      Nominal.NPrf (.imp ph (.classEq (syn_cima R (syn_csn D)) (syn_csn O)))) :
    Nominal.NPrf
      (.imp ph (syn_wb (.classMem D (syn_cima (syn_ccnv R) U)) (.classMem O U))) :=
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
  have dv_cache_0002 : x ∉ ((syn_ccnv R)).fv :=
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
  have p0000 := @g_elima x D (syn_ccnv R) U dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_a1i
      (syn_wb (.classMem D (syn_cima (syn_ccnv R) U))
        (syn_wrex x U (syn_wbr (.cv x) (syn_ccnv R) D)))
      ph p0000
  have p0002 := @g_brcnv (.cv x) D R
  have p0003 := (Nominal.biimpRefl (syn_wbr D R (.cv x)))
  have p0004 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv R) D) (syn_wbr D R (.cv x))
      (.classMem (syn_cop D (.cv x)) R) p0002 p0003
  have p0005 := @g_elimasn R D (.cv x)
  have p0006 :=
    @g_bicomi (.classMem (.cv x) (syn_cima R (syn_csn D)))
      (.classMem (syn_cop D (.cv x)) R) p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (syn_cop D (.cv x)) R)
      (.classMem (.cv x) (syn_cima R (syn_csn D))) p0004 p0006
  have p0008 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (.cv x) (syn_cima R (syn_csn D))))
      ph p0007
  have p0009 :=
    @g_eleq2d ph (syn_cima R (syn_csn D)) (syn_csn O) (.cv x) hyp_wpppreimaactsnd_3
  have p0010 :=
    @g_bitrd ph (syn_wbr (.cv x) (syn_ccnv R) D)
      (.classMem (.cv x) (syn_cima R (syn_csn D))) (.classMem (.cv x) (syn_csn O)) p0008
      p0009
  have p0011 :=
    @g_rexbidv ph (syn_wbr (.cv x) (syn_ccnv R) D) (.classMem (.cv x) (syn_csn O)) x U
      dv_cache_0004 p0010
  have p0012 :=
    @g_bitrd ph (.classMem D (syn_cima (syn_ccnv R) U))
      (syn_wrex x U (syn_wbr (.cv x) (syn_ccnv R) D))
      (syn_wrex x U (.classMem (.cv x) (syn_csn O))) p0001 p0011
  have p0013 := (Nominal.biimpRefl (syn_wrex x U (.classMem (.cv x) (syn_csn O))))
  have p0014 := @g_ancom (.classMem (.cv x) U) (.classMem (.cv x) (syn_csn O))
  have p0015 :=
    @g_exbii (syn_wa (.classMem (.cv x) U) (.classMem (.cv x) (syn_csn O)))
      (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U)) x p0014
  have p0016 :=
    @g_bitri (syn_wrex x U (.classMem (.cv x) (syn_csn O)))
      (syn_wex x (syn_wa (.classMem (.cv x) U) (.classMem (.cv x) (syn_csn O))))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U))) p0013
      p0015
  have p0017 := (Nominal.biimpRefl (syn_wrex x (syn_csn O) (.classMem (.cv x) U)))
  have p0018 :=
    @g_bicomi (syn_wrex x (syn_csn O) (.classMem (.cv x) U))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U))) p0017
  have p0019 :=
    @g_bitri (syn_wrex x U (.classMem (.cv x) (syn_csn O)))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn O)) (.classMem (.cv x) U)))
      (syn_wrex x (syn_csn O) (.classMem (.cv x) U)) p0016 p0018
  have p0020 := @g_id (.classEq (.cv x) O)
  have p0021 := @g_eleq1d (.classEq (.cv x) O) (.cv x) O U p0020
  have p0022 :=
    @g_rexsn (.classMem (.cv x) U) (.classMem O U) x O dv_cache_0005 dv_cache_0006
      hyp_wpppreimaactsnd_2 p0021
  have p0023 :=
    @g_bitri (syn_wrex x U (.classMem (.cv x) (syn_csn O)))
      (syn_wrex x (syn_csn O) (.classMem (.cv x) U)) (.classMem O U) p0019 p0022
  have p0024 :=
    @g_a1i (syn_wb (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (.classMem O U)) ph
      p0023
  have p0025 :=
    @g_bitrd ph (.classMem D (syn_cima (syn_ccnv R) U))
      (syn_wrex x U (.classMem (.cv x) (syn_csn O))) (.classMem O U) p0012 p0024
  exact p0025

@[expose]
noncomputable def g_wpppowlayerorb (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_n : n ∉ C.fv) (dv_F_n : n ∉ F.fv)
    (hyp_wpppowlayerorb_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpppowlayerorb_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wpppowlayerorb_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc))
        (syn_wb (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) :=
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
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wpppowlayerorb_1 p0000
  have p0002 := @g_wpppowlayerseqfv C n F dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_eleq2d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))
      (syn_cima
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_clec) (syn_csn C)))
      D p0002
  have p0004 := @g_elex D (syn_cdm F)
  have p0005 := Nominal.mp hyp_wpppowlayerorb_2 p0004
  have p0006 := @g_fvex (.cv n) (syn_cfrec F D)
  have p0007 :=
    @g_wpppowatact D F (.cv n) hyp_wpppowlayerorb_1 hyp_wpppowlayerorb_2
      hyp_wpppowlayerorb_3
  have p0008 :=
    @g_wpppreimaactsnd (.classMem (.cv n) (syn_cnnc)) D
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
      (syn_cima (syn_clec) (syn_csn C)) (syn_cfv (syn_cfrec F D) (.cv n)) p0005 p0006
      p0007
  have p0009 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
      (.classMem D (syn_cima (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
          (syn_cima (syn_clec) (syn_csn C))))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C)))
      p0003 p0008
  have p0010 := @g_elimasn (syn_clec) C (syn_cfv (syn_cfrec F D) (.cv n))
  have p0011 :=
    (Nominal.biimpRefl (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))
  have p0012 :=
    @g_bicomi (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
      (.classMem (syn_cop C (syn_cfv (syn_cfrec F D) (.cv n))) (syn_clec)) p0011
  have p0013 :=
    @g_bitri
      (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C)))
      (.classMem (syn_cop C (syn_cfv (syn_cfrec F D) (.cv n))) (syn_clec))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) p0010 p0012
  have p0014 :=
    @g_a1i
      (syn_wb (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0013
  have p0015 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc))
      (.classMem D (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) p0009 p0014
  exact p0015

@[expose]
noncomputable def g_wppprecompex (F : Class)
    (_hyp_wppprecompex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppprecomp F) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppprecomp F))
  have p0001 := @g_composeex
  have p0002 := @g_idex
  have p0003 := @g_vvex
  have p0004 := @g_snex F
  have p0005 := @g_xpex (syn_cvv) (syn_csn F) p0003 p0004
  have p0006 := @g_txpex (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)) p0002 p0005
  have p0007 :=
    @g_coex (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0001
      p0006
  have p0008 :=
    @g_eqeltri (syn_cwppprecomp F)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))))
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wppprecompfn (F : Class)
    (hyp_wppprecompfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwppprecomp F) (syn_cvv)) :=
  by
  have p0000 := @g_composefn
  have p0001 := @g_f1ovi
  have p0002 := @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0005 := Nominal.mp hyp_wppprecompfn_1 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) p0003 p0005
  have p0007 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0009
  have p0011 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_fncovv (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0000
      p0011
  have p0013 := (Nominal.classEqRefl (syn_cwppprecomp F))
  have p0014 :=
    @g_fneq1i (syn_cvv) (syn_cwppprecomp F)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) p0013
  have p0015 :=
    @g_mpbir (syn_wfn (syn_cwppprecomp F) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))))
        (syn_cvv))
      p0012 p0014
  exact p0015

@[expose]
noncomputable def g_wppprecompfv (R : Class) (F : Class)
    (hyp_wppprecompfv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppprecompfv_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwppprecomp F) R) (syn_ccom R F)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppprecomp F))
  have p0001 :=
    @g_fveq1i R (syn_cwppprecomp F)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) p0000
  have p0002 := @g_f1ovi
  have p0003 := @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0006 := Nominal.mp hyp_wppprecompfv_1 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) p0004 p0006
  have p0008 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_inidm (syn_cvv)
  have p0011 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) p0010
  have p0012 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) (syn_cvv))
      (.classMem R (syn_cvv)) p0012 hyp_wppprecompfv_2
  have p0014 :=
    @g_fvco2 (syn_cvv) R (syn_ccompose)
      (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))
  have p0015 := Nominal.mp p0013 p0014
  have p0021 :=
    @g_fvtxpvv R (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)) p0004 p0006 hyp_wppprecompfv_2
  have p0022 := @g_fvi R (syn_cvv)
  have p0023 := Nominal.mp hyp_wppprecompfv_2 p0022
  have p0024 := @g_fvconst2 (syn_cvv) F R hyp_wppprecompfv_1
  have p0025 := Nominal.mp hyp_wppprecompfv_2 p0024
  have p0026 :=
    @g_opeq12i (syn_cfv (syn_cid) R) R (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R) F p0023
      p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) R)
      (syn_cop (syn_cfv (syn_cid) R) (syn_cfv (syn_cxp (syn_cvv) (syn_csn F)) R))
      (syn_cop R F) p0021 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) R)
      (syn_cop R F) (syn_ccompose) p0027
  have p0029 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R)
      (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F))) R))
      (syn_cfv (syn_ccompose) (syn_cop R F)) p0015 p0028
  have p0030 := (Nominal.classEqRefl (syn_co R (syn_ccompose) F))
  have p0031 :=
    @g_eqcomi (syn_co R (syn_ccompose) F) (syn_cfv (syn_ccompose) (syn_cop R F)) p0030
  have p0032 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R)
      (syn_cfv (syn_ccompose) (syn_cop R F)) (syn_co R (syn_ccompose) F) p0029 p0031
  have p0033 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem F (syn_cvv)) hyp_wppprecompfv_2
      hyp_wppprecompfv_1
  have p0034 := @g_composevalg R F (syn_cvv) (syn_cvv)
  have p0035 := Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R)
      (syn_co R (syn_ccompose) F) (syn_ccom R F) p0032 p0035
  have p0037 :=
    @g_eqtri (syn_cfv (syn_cwppprecomp F) R)
      (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_cid) (syn_cxp (syn_cvv) (syn_csn F)))) R)
      (syn_ccom R F) p0001 p0036
  exact p0037

@[expose]
noncomputable def g_wpppowcommeqex (F : Class)
    (hyp_wpppowcommeqex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppowcommeq F) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowcommeq F))
  have p0001 := @g_wppprecompex F hyp_wpppowcommeqex_1
  have p0002 := @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0003 := @g_wpppostcompex F hyp_wpppowcommeqex_1
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid)
      p0002 p0003
  have p0005 :=
    @g_coex (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0001 p0004
  have p0006 :=
    @g_cnvex (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
      p0005
  have p0011 :=
    @g_coex (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0003 p0004
  have p0012 :=
    @g_coex
      (syn_ccnv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) p0006
      p0011
  have p0013 :=
    @g_fixex
      (syn_ccom (syn_ccnv
          (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
        (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      p0012
  have p0014 :=
    @g_eqeltri (syn_cwpppowcommeq F)
      (syn_cfix (syn_ccom (syn_ccnv
            (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
      (syn_cvv) p0000 p0013
  exact p0014

@[expose]
noncomputable def g_wpppowcommeqval (n : Var) (F : Class)
    (hyp_wpppowcommeqval_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F))
          (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
            (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowcommeq F))
  have p0001 :=
    @g_eleq2i (syn_cwpppowcommeq F)
      (syn_cfix (syn_ccom (syn_ccnv
            (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
      (.cv n) p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classMem (.cv n) (syn_cfix (syn_ccom
              (syn_ccnv
                (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
              (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))))
      (.classMem (.cv n) (syn_cnnc)) p0001
  have p0003 := @g_wppprecompfn F hyp_wpppowcommeqval_1
  have p0004 := @g_wpppowcorefn F hyp_wpppowcommeqval_1
  have p0005 := @g_ssv (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0006 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwppprecomp F) (syn_cvv))
      (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc))
      (syn_wss (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cvv)) p0003 p0004
      p0005
  have p0007 :=
    @g_fnco (syn_cvv) (syn_cnnc) (syn_cwppprecomp F)
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_fnfun (syn_cnnc)
      (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_a1i
      (syn_wfun (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (.classMem (.cv n) (syn_cnnc)) p0010
  have p0012 := @g_wpppostcompfn F hyp_wpppowcommeqval_1
  have p0015 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwpppostcomp F) (syn_cvv))
      (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc))
      (syn_wss (syn_crn (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cvv)) p0012 p0004
      p0005
  have p0016 :=
    @g_fnco (syn_cvv) (syn_cnnc) (syn_cwpppostcomp F)
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_fnfun (syn_cnnc)
      (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_a1i
      (syn_wfun (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (.classMem (.cv n) (syn_cnnc)) p0019
  have p0021 := @g_id (.classMem (.cv n) (syn_cnnc))
  have p0028 :=
    @g_fndm (syn_cnnc)
      (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0029 := Nominal.mp p0008 p0028
  have p0030 :=
    @g_a1i
      (.classEq (syn_cdm
          (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc)) p0029
  have p0031 :=
    @g_eleqtrrd (.classMem (.cv n) (syn_cnnc)) (.cv n) (syn_cnnc)
      (syn_cdm (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      p0021 p0030
  have p0039 :=
    @g_fndm (syn_cnnc)
      (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0040 := Nominal.mp p0017 p0039
  have p0041 :=
    @g_a1i
      (.classEq (syn_cdm
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
        (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc)) p0040
  have p0042 :=
    @g_eleqtrrd (.classMem (.cv n) (syn_cnnc)) (.cv n) (syn_cnnc)
      (syn_cdm (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      p0021 p0041
  have p0043 :=
    @g_jca (.classMem (.cv n) (syn_cnnc))
      (.classMem (.cv n) (syn_cdm
          (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
      (.classMem (.cv n) (syn_cdm
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
      p0031 p0042
  have p0044 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc))
      (syn_wfun (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (syn_wfun (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
      (syn_wa (.classMem (.cv n) (syn_cdm
            (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
        (.classMem (.cv n) (syn_cdm
            (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))))
      p0011 p0020 p0043
  have p0045 :=
    @g_funeqfix (.cv n)
      (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
      (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
  have p0046 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_w3a (syn_wfun
          (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_wfun
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (syn_wa
          (.classMem (.cv n) (syn_cdm
              (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))
          (.classMem (.cv n) (syn_cdm (syn_ccom (syn_cwpppostcomp F)
                (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))))))
      (syn_wb (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv
                (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
              (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))))
        (.classEq (syn_cfv
            (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n))
          (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
            (.cv n))))
      p0044 p0045
  have p0047 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowcommeq F))
      (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv
              (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))
            (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))))
      (.classEq
        (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
          (.cv n)) (syn_cfv
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)))
      p0002 p0046
  have p0049 :=
    @g_a1i (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc)) p0004
  have p0051 :=
    @g_jca (.classMem (.cv n) (syn_cnnc))
      (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc)) p0049 p0021
  have p0052 :=
    @g_fvco2 (syn_cnnc) (.cv n) (syn_cwppprecomp F)
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0053 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc))
        (.classMem (.cv n) (syn_cnnc)))
      (.classEq
        (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
          (.cv n)) (syn_cfv (syn_cwppprecomp F)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      p0051 p0052
  have p0054 := @g_fvex (.cv n) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0055 :=
    @g_wppprecompfv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F
      hyp_wpppowcommeqval_1 p0054
  have p0056 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppprecomp F)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
        (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F))
      (.classMem (.cv n) (syn_cnnc)) p0055
  have p0057 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
        (.cv n))
      (syn_cfv (syn_cwppprecomp F) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F) p0053
      p0056
  have p0062 :=
    @g_fvco2 (syn_cnnc) (.cv n) (syn_cwpppostcomp F)
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0063 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (syn_wfn (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cnnc))
        (.classMem (.cv n) (syn_cnnc)))
      (.classEq (syn_cfv
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n))
        (syn_cfv (syn_cwpppostcomp F)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      p0051 p0062
  have p0065 :=
    @g_wpppostcompfv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F
      hyp_wpppowcommeqval_1 p0054
  have p0066 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwpppostcomp F)
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      (.classMem (.cv n) (syn_cnnc)) p0065
  have p0067 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
        (.cv n))
      (syn_cfv (syn_cwpppostcomp F)
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) p0063
      p0066
  have p0068 :=
    @g_eqeq12d (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
        (.cv n))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
      (syn_cfv (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
        (.cv n))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) p0057
      p0067
  have p0069 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowcommeq F))
      (.classEq
        (syn_cfv (syn_ccom (syn_cwppprecomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))
          (.cv n)) (syn_cfv
          (syn_ccom (syn_cwpppostcomp F) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (.cv n)))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      p0047 p0068
  exact p0069

@[expose]
noncomputable def g_wpppowcommeqvalcl (B : Class) (F : Class)
    (hyp_wpppowcommeqvalcl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F))
          (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
            (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))) :=
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
      ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F))
            (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
              (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))))).fv :=
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
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwpppowcommeq F) p0001
  have p0006 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      p0001
  have p0007 :=
    @g_coeq1d (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F p0006
  have p0010 :=
    @g_coeq2d (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F p0006
  have p0011 :=
    @g_eqeq12d (.classEq (.cv n) B)
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) p0007 p0010
  have p0012 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwpppowcommeq F))
      (.classMem B (syn_cwpppowcommeq F))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))
      p0004 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F)) (.classEq
          (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))))
      (syn_wb (.classMem B (syn_cwpppowcommeq F))
        (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))
      p0002 p0012
  have p0014 := @g_wpppowcommeqval n F hyp_wpppowcommeqvalcl_1
  have p0015 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F))
          (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) F)
            (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))))
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowcommeq F))
          (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
            (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))))
      n B (syn_cnnc) dv_cache_0001 dv_cache_0002 p0013 p0014
  have p0016 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem B (syn_cwpppowcommeq F))
        (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_wpppowcommall (F : Class) (N : Class)
    (hyp_wpppowcommall_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_cwpppowcommeq F))) :=
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
  have dv_cache_0001 : n ∉ ((syn_cwpppowcommeq F)).fv := by
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
  have dv_cache_0004 : n ∉ ((Wff.classMem (.cv m) (syn_cwpppowcommeq F))).fv :=
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
  have dv_cache_0005 : m ∉ ((Wff.classMem (.cv n) (syn_cwpppowcommeq F))).fv :=
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
  have dv_cache_0006 : n ∉ ((Wff.classMem (syn_c0c) (syn_cwpppowcommeq F))).fv :=
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
  have dv_cache_0007 : n ∉ ((Wff.classMem N (syn_cwpppowcommeq F))).fv :=
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
    n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F))).fv :=
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
  have p0000 := @g_wpppowcommeqex F hyp_wpppowcommall_1
  have p0001 := @g_abid2 n (syn_cwpppowcommeq F) dv_cache_0001
  have p0002 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cwpppowcommeq F))) (syn_cwpppowcommeq F)
      (syn_cvv) p0001
  have p0003 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cwpppowcommeq F))) (syn_cvv))
      (.classMem (syn_cwpppowcommeq F) (syn_cvv)) p0000 p0002
  have p0004 := @g_id (.classEq (.cv n) (syn_c0c))
  have p0005 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cwpppowcommeq F) p0004
  have p0006 := @g_id (.classEq (.cv n) (.cv m))
  have p0007 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwpppowcommeq F) p0006
  have p0008 := @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0009 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n)
      (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F) p0008
  have p0010 := @g_id (.classEq (.cv n) N)
  have p0011 := @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cwpppowcommeq F) p0010
  have p0012 := @g_wpppowcore0 F hyp_wpppowcommall_1
  have p0013 :=
    @g_coeq1i (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) F
      p0012
  have p0014 := @g_coi2 F
  have p0015 :=
    @g_eqtri (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) F)
      (syn_ccom (syn_cid) F) F p0013 p0014
  have p0017 :=
    @g_coeq2i (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) F
      p0012
  have p0018 := @g_coi1 F
  have p0019 :=
    @g_eqtri (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)))
      (syn_ccom F (syn_cid)) F p0017 p0018
  have p0020 :=
    @g_eqcomi (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)))
      F p0019
  have p0021 :=
    @g_eqtri (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) F) F
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c))) p0015
      p0020
  have p0022 := @g_peano1
  have p0023 := @g_wpppowcommeqvalcl (syn_c0c) F hyp_wpppowcommall_1
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwpppowcommeq F))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c))))
      p0021 p0024
  have p0026 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0027 := @g_wpppowcoresuc m F dv_cache_0002 hyp_wpppowcommall_1
  have p0028 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (.cv m) (syn_cnnc))
      (.classEq
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))))
      p0026 p0027
  have p0029 :=
    @g_coeq1d
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F p0028
  have p0030 := @g_coass F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F
  have p0031 :=
    @g_a1i
      (.classEq (syn_ccom
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F)
        (syn_ccom F (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      p0030
  have p0032 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_ccom
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F)
      (syn_ccom (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F)
      (syn_ccom F (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F))
      p0029 p0031
  have p0033 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
  have p0035 := @g_wpppowcommeqval m F hyp_wpppowcommall_1
  have p0036 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wb (.classMem (.cv m) (syn_cwpppowcommeq F)) (.classEq
          (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))))
      p0026 p0035
  have p0037 :=
    @g_biimpd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (.cv m) (syn_cwpppowcommeq F))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))))
      p0036
  have p0038 :=
    @g_mpd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (.cv m) (syn_cwpppowcommeq F))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))))
      p0033 p0037
  have p0039 :=
    @g_coeq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F)
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) F p0038
  have p0040 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_ccom
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F)
      (syn_ccom F (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)) F))
      (syn_ccom F (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))))
      p0032 p0039
  have p0044 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))) p0028
  have p0045 :=
    @g_coeq2d
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F
      p0044
  have p0046 :=
    @g_eqtrd
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (syn_ccom
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F)
      (syn_ccom F (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv m))))
      (syn_ccom F
        (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))))
      p0040 p0045
  have p0048 := @g_peano2 (.cv m)
  have p0049 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      p0026 p0048
  have p0050 := @g_wpppowcommeqvalcl (syn_cplc (.cv m) (syn_c1c)) F hyp_wpppowcommall_1
  have p0051 :=
    @g_syl
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F)) (.classEq (syn_ccom
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c))) F)
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
              (syn_cplc (.cv m) (syn_c1c))))))
      p0049 p0050
  have p0052 :=
    @g_mpbird
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
            (syn_cplc (.cv m) (syn_c1c))) F) (syn_ccom F
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv m) (syn_c1c)))))
      p0046 p0051
  have p0053 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowcommeq F))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F)) p0052
  have p0054_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cwpppowcommeq F))
          (.classMem (.cv m) (syn_cwpppowcommeq F)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpppowcommeq syn_cfix syn_crn syn_cima syn_wrex syn_wex syn_wa
          syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_cvv syn_cin syn_cid
          syn_copab syn_ccom syn_ccnv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0054 :=
    @g_finds (.classMem (.cv n) (syn_cwpppowcommeq F))
      (.classMem (syn_c0c) (syn_cwpppowcommeq F))
      (.classMem (.cv m) (syn_cwpppowcommeq F))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowcommeq F))
      (.classMem N (syn_cwpppowcommeq F)) n m N dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0003 p0005
      p0054_e02_recanon p0009 p0011 p0025 p0053
  exact p0054

@[expose]
noncomputable def g_wpppowcomm (B : Class) (F : Class)
    (hyp_wpppowcomm_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc))
        (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
          (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) :=
  by
  have p0000 := @g_wpppowcommall F B hyp_wpppowcomm_1
  have p0001 := @g_wpppowcommeqvalcl B F hyp_wpppowcomm_1
  have p0002 :=
    @g_mpbid (.classMem B (syn_cnnc)) (.classMem B (syn_cwpppowcommeq F))
      (.classEq (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
        (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wpppowcorersuccl (B : Class) (F : Class)
    (hyp_wpppowcorersuccl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (.classEq
          (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
          (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F))) :=
  by
  have p0000 := @g_wpppowcoresuccl B F hyp_wpppowcorersuccl_1
  have p0001 := @g_wpppowcomm B F hyp_wpppowcorersuccl_1
  have p0002 :=
    @g_eqcomd (.classMem B (syn_cnnc))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F)
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) p0001
  have p0003 :=
    @g_eqtrd (.classMem B (syn_cnnc))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c)))
      (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F) p0000 p0002
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

@[expose]
noncomputable def g_wpppowlayerseqfvcl (B : Class) (C : Class) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wpppowlayerseqfvcl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))
          (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
            (syn_cima (syn_clec) (syn_csn C))))) :=
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
      ((Wff.imp (.classMem B (syn_cnnc))
          (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima
              (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
              (syn_cima (syn_clec) (syn_csn C)))))).fv :=
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
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_sneqd (.classEq (.cv n) B) (.cv n) B p0001
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_csn (.cv n)) (syn_csn B) (syn_cwpppowlayerseq F C)
      p0004
  have p0007 := @g_tceq (.cv n) B
  have p0008 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0001 p0007
  have p0009 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B)
      (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0008
  have p0010 :=
    @g_cnveqd (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) p0009
  have p0011 :=
    @g_imaeq1d (.classEq (.cv n) B)
      (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
      (syn_cima (syn_clec) (syn_csn C)) p0010
  have p0012 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))
      (syn_cima
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
        (syn_cima (syn_clec) (syn_csn C)))
      p0005 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
          (syn_cima (syn_clec) (syn_csn C))))
      (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima
          (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
          (syn_cima (syn_clec) (syn_csn C))))
      p0002 p0012
  have p0014 :=
    @g_wpppowlayerseqfv C n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wpppowlayerseqfvcl_1
  have p0015 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc))
        (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_cima (syn_ccnv
              (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
            (syn_cima (syn_clec) (syn_csn C)))))
      (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))
          (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
            (syn_cima (syn_clec) (syn_csn C)))))
      n B (syn_cnnc) dv_cache_0004 dv_cache_0005 p0013 p0014
  have p0016 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (syn_cima
          (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)))
          (syn_cima (syn_clec) (syn_csn C))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_wpppowlayerseqsuc (C : Class) (n : Var) (F : Class)
    (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wpppowlayerseqsuc_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq
          (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c))))
          (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (F).fv := by
    exact
      (show Disjoint (C).fv (F).fv from (show Disjoint (C).fv (F).fv from (by exact dv_C_F)))
  have p0000 := @g_id (.classMem (.cv n) (syn_cnnc))
  have p0001 := @g_peano2 (.cv n)
  have p0002 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_wpppowlayerseqfvcl (syn_cplc (.cv n) (syn_c1c)) C F dv_cache_0001
      hyp_wpppowlayerseqsuc_1
  have p0004 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classEq (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c))))
        (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
              (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C))))
      p0002 p0003
  have p0005 := @g_nntcsuc (.cv n)
  have p0006 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (syn_ctc (.cv n)) (syn_c1c)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
      p0005
  have p0007 := @g_nntccl (.cv n)
  have p0008 := @g_wpppowcorersuccl (syn_ctc (.cv n)) F hyp_wpppowlayerseqsuc_1
  have p0009 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc))
      (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_cplc (syn_ctc (.cv n)) (syn_c1c)))
        (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F))
      p0007 p0008
  have p0010 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_cplc (syn_ctc (.cv n)) (syn_c1c)))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)
      p0006 p0009
  have p0011 :=
    @g_cnveqd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
        (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F)
      p0010
  have p0012 :=
    @g_imaeq1d (.classMem (.cv n) (syn_cnnc))
      (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
          (syn_ctc (syn_cplc (.cv n) (syn_c1c)))))
      (syn_ccnv (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
          F))
      (syn_cima (syn_clec) (syn_csn C)) p0011
  have p0013 :=
    @g_cnvco (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F
  have p0014 :=
    @g_a1i
      (.classEq (syn_ccnv
          (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F))
        (syn_ccom (syn_ccnv F) (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))))
      (.classMem (.cv n) (syn_cnnc)) p0013
  have p0015 :=
    @g_imaeq1d (.classMem (.cv n) (syn_cnnc))
      (syn_ccnv (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))
          F))
      (syn_ccom (syn_ccnv F)
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))))
      (syn_cima (syn_clec) (syn_csn C)) p0014
  have p0016 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
            (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccnv
          (syn_ccom (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) F))
        (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccom (syn_ccnv F) (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))))
        (syn_cima (syn_clec) (syn_csn C)))
      p0012 p0015
  have p0017 :=
    @g_imaco (syn_ccnv F)
      (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
      (syn_cima (syn_clec) (syn_csn C))
  have p0018 :=
    @g_a1i
      (.classEq (syn_cima (syn_ccom (syn_ccnv F) (syn_ccnv
              (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))))
          (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv
              (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
            (syn_cima (syn_clec) (syn_csn C)))))
      (.classMem (.cv n) (syn_cnnc)) p0017
  have p0019 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
            (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccom (syn_ccnv F) (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))))
        (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
          (syn_cima (syn_clec) (syn_csn C))))
      p0016 p0018
  have p0020 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c))))
      (syn_cima (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
            (syn_ctc (syn_cplc (.cv n) (syn_c1c))))) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
          (syn_cima (syn_clec) (syn_csn C))))
      p0004 p0019
  have p0021 := @g_wpppowlayerseqfvcl (.cv n) C F dv_cache_0001 hyp_wpppowlayerseqsuc_1
  have p0022 :=
    @g_eqcomd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))
      (syn_cima
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_clec) (syn_csn C)))
      p0021
  have p0023 :=
    @g_imaeq2d (.classMem (.cv n) (syn_cnnc))
      (syn_cima
        (syn_ccnv (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
        (syn_cima (syn_clec) (syn_csn C)))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))) (syn_ccnv F) p0022
  have p0024 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (syn_cplc (.cv n) (syn_c1c))))
      (syn_cima (syn_ccnv F) (syn_cima (syn_ccnv
            (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))))
          (syn_cima (syn_clec) (syn_csn C))))
      (syn_cima (syn_ccnv F) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))) p0020
      p0023
  exact p0024

@[expose]
noncomputable def g_wppreachincblayerscl (B : Class) (C : Class) (F : Class) (d : Var)
    (dv_B_d : d ∉ B.fv) (dv_C_F : Disjoint C.fv F.fv) (dv_C_d : d ∉ C.fv)
    (dv_F_d : d ∉ F.fv)
    (hyp_wppreachincblayerscl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C))
          (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                  (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                  (syn_ctc B)))
              (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))))) :=
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
      ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C))
            (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                    (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                    (syn_ctc B))) (.classMem (.cv d)
                  (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))))))).fv :=
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
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_id (.classEq (.cv n) B)
  have p0002 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0004 := @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwppreachincb F C) p0001
  have p0006 := @g_tceq (.cv n) B
  have p0007 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B)
      (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0001 p0006
  have p0008 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0007
  have p0009 :=
    @g_eleq2d (.classEq (.cv n) B)
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (.cv n)))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc B))
      (.cv d) p0008
  have p0011 := @g_sneqd (.classEq (.cv n) B) (.cv n) B p0001
  have p0012 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_csn (.cv n)) (syn_csn B) (syn_cwpppowlayerseq F C)
      p0011
  have p0013 :=
    @g_eleq2d (.classEq (.cv n) B) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))
      (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)) (.cv d) p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv n) B)
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv n))))
      (.classMem (.cv d)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc B)))
      (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))
      (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))) p0009 p0013
  have p0015 :=
    @g_ralbidv (.classEq (.cv n) B)
      (syn_wb (.classMem (.cv d)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv n))))
        (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))
      (syn_wb (.classMem (.cv d)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc B))) (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))
      d (syn_cdm F) dv_cache_0001 p0014
  have p0016 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwppreachincb F C))
      (.classMem B (syn_cwppreachincb F C))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv n))))
          (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))))
      (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc B)))
          (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))))
      p0004 p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc))
      (.classMem B (syn_cnnc))
      (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb
            (.classMem (.cv d) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc (.cv n))))
            (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n)))))))
      (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb
            (.classMem (.cv d) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc B)))
            (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))))
      p0002 p0016
  have p0018 :=
    @g_wppreachincblayers C n F d dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 hyp_wppreachincblayerscl_1
  have p0019 :=
    @g_vtoclg
      (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppreachincb F C))
          (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                  (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                  (syn_ctc (.cv n)))) (.classMem (.cv d)
                (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn (.cv n))))))))
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppreachincb F C))
          (syn_wral d (syn_cdm F) (syn_wb (.classMem (.cv d) (syn_cfv
                  (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                  (syn_ctc B)))
              (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B)))))))
      n B (syn_cnnc) dv_cache_0008 dv_cache_0009 p0017 p0018
  have p0020 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem B (syn_cwppreachincb F C)) (syn_wral d (syn_cdm F) (syn_wb
            (.classMem (.cv d) (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc B)))
            (.classMem (.cv d) (syn_cfv (syn_cwpppowlayerseq F C) (syn_csn B))))))
      p0000 p0019
  exact p0020


end NFChoice.DirectNominalPrf.WPPReplay

end
