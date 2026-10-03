/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnimageopval (B : Class) (R : Class)
    (hyp_lnimageopval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnimageopval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_cima R B)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnimageop))
  have p0001 :=
    @g_fveq1i (syn_cop R B) (syn_clnimageop) (syn_ccom (syn_cranfn) (syn_clnimageresfn))
      p0000
  have p0002 := @g_fnlndifop
  have p0003 := @g_ln1stfn
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0003
      p0002
  have p0006 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_inidm (syn_cvv)
  have p0009 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop))
      p0008
  have p0010 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0007 p0009
  have p0011 := @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0002 p0010
  have p0012 := (Nominal.classEqRefl (syn_clninterop))
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_clninterop)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0012
  have p0014 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv))
      p0011 p0013
  have p0016 := @g_fncross
  have p0017 := @g_ln2ndfn
  have p0018 := @g_vvex
  have p0019 := @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0017 p0020
  have p0022 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0023 := Nominal.mp p0021 p0022
  have p0025 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0008
  have p0026 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv))
      p0023 p0025
  have p0027 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))
      p0016 p0026
  have p0028 := (Nominal.classEqRefl (syn_clnimagecrossfn))
  have p0029 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))))
      p0028
  have p0030 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross)
          (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv))
      p0027 p0029
  have p0031 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv))
      p0003 p0030
  have p0032 := @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0033 := Nominal.mp p0031 p0032
  have p0035 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0008
  have p0036 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0033 p0035
  have p0037 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0014 p0036
  have p0038 := (Nominal.classEqRefl (syn_clnimageresfn))
  have p0039 :=
    @g_fneq1i (syn_cvv) (syn_clnimageresfn)
      (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0038
  have p0040 :=
    @g_mpbir (syn_wfn (syn_clnimageresfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)))
        (syn_cvv))
      p0037 p0039
  have p0041 := @g_opex R B hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_clnimageresfn) (syn_cvv)) (.classMem (syn_cop R B) (syn_cvv))
      p0040 p0041
  have p0043 := @g_fvco2 (syn_cvv) (syn_cop R B) (syn_cranfn) (syn_clnimageresfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B))
      (syn_cfv (syn_ccom (syn_cranfn) (syn_clnimageresfn)) (syn_cop R B))
      (syn_cfv (syn_cranfn) (syn_cfv (syn_clnimageresfn) (syn_cop R B))) p0001 p0044
  have p0046 := @g_lnimageresfnval B R hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0047 :=
    @g_fveq2i (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cres R B) (syn_cranfn)
      p0046
  have p0048 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B))
      (syn_cfv (syn_cranfn) (syn_cfv (syn_clnimageresfn) (syn_cop R B)))
      (syn_cfv (syn_cranfn) (syn_cres R B)) p0045 p0047
  have p0049 := @g_resex R B hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0050 := @g_fvranfn (syn_cres R B) (syn_cvv)
  have p0051 := Nominal.mp p0049 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B))
      (syn_cfv (syn_cranfn) (syn_cres R B)) (syn_crn (syn_cres R B)) p0048 p0051
  have p0053 := @g_dfima3 R B
  have p0054 := @g_eqcomi (syn_cima R B) (syn_crn (syn_cres R B)) p0053
  have p0055 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_crn (syn_cres R B))
      (syn_cima R B) p0052 p0054
  exact p0055

@[expose]
noncomputable def g_lnpwcnvkerfnval (D : Class) (R : Class)
    (hyp_lnpwcnvkerfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwcnvkerfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_ccnv (syn_clnker R))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwcnvkerfn))
  have p0001 :=
    @g_fveq1i (syn_cop R D) (syn_clnpwcnvkerfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0000
  have p0002 := @g_lnpwkerfnfn
  have p0003 := @g_opex R D hyp_lnpwcnvkerfnval_1 hyp_lnpwcnvkerfnval_2
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_clnpwkerfn) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv))
      p0002 p0003
  have p0005 := @g_fvco2 (syn_cvv) (syn_cop R D) (syn_cimage (syn_cswap)) (syn_clnpwkerfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_eqtri (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D))
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cop R D))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_clnpwkerfn) (syn_cop R D))) p0001
      p0006
  have p0008 := @g_lnpwkerfnval D R hyp_lnpwcnvkerfnval_1 hyp_lnpwcnvkerfnval_2
  have p0009 :=
    @g_fveq2i (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_clnker R)
      (syn_cimage (syn_cswap)) p0008
  have p0010 :=
    @g_eqtri (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_clnpwkerfn) (syn_cop R D)))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_clnker R)) p0007 p0009
  have p0011 := @g_swapex
  have p0012 := @g_lnkerex R hyp_lnpwcnvkerfnval_1
  have p0013 := @g_fvimagecl (syn_clnker R) (syn_cswap) p0011 p0012
  have p0014 := @g_dfcnv2 (syn_clnker R)
  have p0015 :=
    @g_eqcomi (syn_ccnv (syn_clnker R)) (syn_cima (syn_cswap) (syn_clnker R)) p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cswap)) (syn_clnker R))
      (syn_cima (syn_cswap) (syn_clnker R)) (syn_ccnv (syn_clnker R)) p0013 p0015
  have p0017 :=
    @g_eqtri (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_clnker R)) (syn_ccnv (syn_clnker R)) p0010
      p0016
  exact p0017

@[expose]
noncomputable def g_lnpwclasspairfnval (D : Class) (R : Class) (S : Class)
    (hyp_lnpwclasspairfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwclasspairfnval_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_lnpwclasspairfnval_3 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S))
        (syn_cop (syn_ccnv (syn_clnker R)) S)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwclasspairfn))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) S) (syn_clnpwclasspairfn)
      (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0000
  have p0002 := @g_imageswapfn
  have p0003 := @g_lnpwkerfnfn
  have p0004 := @g_fncovv (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_clnpwcnvkerfn))
  have p0006 :=
    @g_fneq1i (syn_cvv) (syn_clnpwcnvkerfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_clnpwcnvkerfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv)) p0004 p0006
  have p0008 := @g_ln1stfn
  have p0009 := @g_fncovv (syn_clnpwcnvkerfn) (syn_c1st) p0007 p0008
  have p0010 := @g_ln2ndfn
  have p0011 := @g_opex R D hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0012 := @g_opex (syn_cop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0013 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) S) (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st))
      (syn_c2nd) p0009 p0010 p0012
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) S) (syn_cvv)) p0008 p0012
  have p0018 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) S) (syn_clnpwcnvkerfn) (syn_c1st)
  have p0019 := Nominal.mp p0017 p0018
  have p0021 := @g_opfv1st (syn_cop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0022 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) S)) (syn_cop R D)
      (syn_clnpwcnvkerfn) p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_clnpwcnvkerfn) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) S)))
      (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) p0019 p0022
  have p0024 := @g_lnpwcnvkerfnval D R hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0025 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_ccnv (syn_clnker R)) p0023 p0024
  have p0027 := @g_opfv2nd (syn_cop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0028 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S))
      (syn_ccnv (syn_clnker R)) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) S)) S p0025
      p0027
  have p0029 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd))
        (syn_cop (syn_cop R D) S))
      (syn_cop (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) S)))
      (syn_cop (syn_ccnv (syn_clnker R)) S) p0013 p0028
  have p0030 :=
    @g_eqtri (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd))
        (syn_cop (syn_cop R D) S))
      (syn_cop (syn_ccnv (syn_clnker R)) S) p0001 p0029
  exact p0030

@[expose]
noncomputable def g_lnpwclassfnfn : Nominal.NPrf (syn_wfn (syn_clnpwclassfn) (syn_cvv)) :=
  by
  have p0000 := @g_lnimageopfn
  have p0001 := @g_imageswapfn
  have p0002 := @g_lnpwkerfnfn
  have p0003 := @g_fncovv (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_clnpwcnvkerfn))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwcnvkerfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwcnvkerfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv)) p0003 p0005
  have p0007 := @g_ln1stfn
  have p0008 := @g_fncovv (syn_clnpwcnvkerfn) (syn_c1st) p0006 p0007
  have p0009 := @g_ln2ndfn
  have p0010 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_inidm (syn_cvv)
  have p0014 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0013
  have p0015 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv))
      p0012 p0014
  have p0016 := (Nominal.classEqRefl (syn_clnpwclasspairfn))
  have p0017 :=
    @g_fneq1i (syn_cvv) (syn_clnpwclasspairfn)
      (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0016
  have p0018 :=
    @g_mpbir (syn_wfn (syn_clnpwclasspairfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv))
      p0015 p0017
  have p0019 := @g_fncovv (syn_clnimageop) (syn_clnpwclasspairfn) p0000 p0018
  have p0020 := (Nominal.classEqRefl (syn_clnpwclassfn))
  have p0021 :=
    @g_fneq1i (syn_cvv) (syn_clnpwclassfn)
      (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) p0020
  have p0022 :=
    @g_mpbir (syn_wfn (syn_clnpwclassfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) (syn_cvv)) p0019 p0021
  exact p0022

@[expose]
noncomputable def g_lnpwclassfnex :
    Nominal.NPrf (.classMem (syn_clnpwclassfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwclassfn))
  have p0001 := @g_lnimageopex
  have p0002 := (Nominal.classEqRefl (syn_clnpwclasspairfn))
  have p0003 := (Nominal.classEqRefl (syn_clnpwcnvkerfn))
  have p0004 := @g_swapex
  have p0005 := @g_imageex (syn_cswap) p0004
  have p0006 := @g_lnpwkerfnex
  have p0007 := @g_coex (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0005 p0006
  have p0008 :=
    @g_eqeltri (syn_clnpwcnvkerfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn))
      (syn_cvv) p0003 p0007
  have p0009 := @g_n_1stex
  have p0010 := @g_coex (syn_clnpwcnvkerfn) (syn_c1st) p0008 p0009
  have p0011 := @g_n_2ndex
  have p0012 := @g_txpex (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd) p0010 p0011
  have p0013 :=
    @g_eqeltri (syn_clnpwclasspairfn)
      (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv) p0002
      p0012
  have p0014 := @g_coex (syn_clnimageop) (syn_clnpwclasspairfn) p0001 p0013
  have p0015 :=
    @g_eqeltri (syn_clnpwclassfn) (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn))
      (syn_cvv) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_lnpwclassfnval (D : Class) (R : Class) (S : Class)
    (hyp_lnpwclassfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwclassfnval_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_lnpwclassfnval_3 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S))
        (syn_cima (syn_ccnv (syn_clnker R)) S)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwclassfn))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) S) (syn_clnpwclassfn)
      (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) p0000
  have p0002 := @g_imageswapfn
  have p0003 := @g_lnpwkerfnfn
  have p0004 := @g_fncovv (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_clnpwcnvkerfn))
  have p0006 :=
    @g_fneq1i (syn_cvv) (syn_clnpwcnvkerfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_clnpwcnvkerfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv)) p0004 p0006
  have p0008 := @g_ln1stfn
  have p0009 := @g_fncovv (syn_clnpwcnvkerfn) (syn_c1st) p0007 p0008
  have p0010 := @g_ln2ndfn
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @g_inidm (syn_cvv)
  have p0015 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0014
  have p0016 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv))
      p0013 p0015
  have p0017 := (Nominal.classEqRefl (syn_clnpwclasspairfn))
  have p0018 :=
    @g_fneq1i (syn_cvv) (syn_clnpwclasspairfn)
      (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0017
  have p0019 :=
    @g_mpbir (syn_wfn (syn_clnpwclasspairfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv))
      p0016 p0018
  have p0020 := @g_opex R D hyp_lnpwclassfnval_1 hyp_lnpwclassfnval_2
  have p0021 := @g_opex (syn_cop R D) S p0020 hyp_lnpwclassfnval_3
  have p0022 :=
    @g_pm3_2i (syn_wfn (syn_clnpwclasspairfn) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) S) (syn_cvv)) p0019 p0021
  have p0023 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) S) (syn_clnimageop) (syn_clnpwclasspairfn)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_clnimageop) (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S)))
      p0001 p0024
  have p0026 :=
    @g_lnpwclasspairfnval D R S hyp_lnpwclassfnval_1 hyp_lnpwclassfnval_2
      hyp_lnpwclassfnval_3
  have p0027 :=
    @g_fveq2i (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S))
      (syn_cop (syn_ccnv (syn_clnker R)) S) (syn_clnimageop) p0026
  have p0028 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_clnimageop) (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S)))
      (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_clnker R)) S)) p0025 p0027
  have p0029 := @g_lnkerex R hyp_lnpwclassfnval_1
  have p0030 := @g_cnvex (syn_clnker R) p0029
  have p0031 := @g_lnimageopval S (syn_ccnv (syn_clnker R)) p0030 hyp_lnpwclassfnval_3
  have p0032 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S))
      (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_clnker R)) S))
      (syn_cima (syn_ccnv (syn_clnker R)) S) p0028 p0031
  exact p0032

@[expose]
noncomputable def g_lnpwpw1secondfnfn :
    Nominal.NPrf (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) :=
  by
  have p0000 := @g_fnfullfun (syn_cpw1fn)
  have p0001 := @g_n_2ndex
  have p0002 := @g_wppimagefn (syn_c2nd) p0001
  have p0003 := @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_clnpwpw1secondfn))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn)
      (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv))
      p0003 p0005
  exact p0006

@[expose]
noncomputable def g_lnpwpw1secondfnex :
    Nominal.NPrf (.classMem (syn_clnpwpw1secondfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwpw1secondfn))
  have p0001 := @g_pw1fnex
  have p0002 := @g_fullfunex (syn_cpw1fn) p0001
  have p0003 := @g_n_2ndex
  have p0004 := @g_imageex (syn_c2nd) p0003
  have p0005 := @g_coex (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0002 p0004
  have p0006 :=
    @g_eqeltri (syn_clnpwpw1secondfn)
      (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_lnpwpw1secondfnval (D : Class) (R : Class)
    (hyp_lnpwpw1secondfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwpw1secondfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D)) :=
  by
  have dv_cache_0001 : Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c2nd)).fv := by
    exact
      (show Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c2nd)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
          exact (show Disjoint (((syn_cop R D)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (syn_clnpwpw1secondfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwpw1secondfn)
      (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0000
  have p0002 := @g_n_2ndex
  have p0003 := @g_wppimagefn (syn_c2nd) p0002
  have p0004 := @g_snex (syn_cop R D)
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv))
      (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_cfullfun (syn_cpw1fn))
      (syn_cimage (syn_c2nd))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)))
        (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cfullfun (syn_cpw1fn))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D))))
      p0001 p0007
  have p0011 := @g_wppfvimage (syn_csn (syn_cop R D)) (syn_c2nd) dv_cache_0001 p0002 p0004
  have p0012 := @g_ln2ndfn
  have p0013 := @g_opex R D hyp_lnpwpw1secondfnval_1 hyp_lnpwpw1secondfnval_2
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0012
      p0013
  have p0015 := @g_fnsnfv (syn_cvv) (syn_cop R D) (syn_c2nd)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_eqcomi (syn_csn (syn_cfv (syn_c2nd) (syn_cop R D)))
      (syn_cima (syn_c2nd) (syn_csn (syn_cop R D))) p0016
  have p0018 := @g_opfv2nd R D hyp_lnpwpw1secondfnval_1 hyp_lnpwpw1secondfnval_2
  have p0019 := @g_sneqi (syn_cfv (syn_c2nd) (syn_cop R D)) D p0018
  have p0020 :=
    @g_eqtri (syn_cima (syn_c2nd) (syn_csn (syn_cop R D)))
      (syn_csn (syn_cfv (syn_c2nd) (syn_cop R D))) (syn_csn D) p0017 p0019
  have p0021 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D)))
      (syn_cima (syn_c2nd) (syn_csn (syn_cop R D))) (syn_csn D) p0011 p0020
  have p0022 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D))) (syn_csn D)
      (syn_cfullfun (syn_cpw1fn)) p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cfullfun (syn_cpw1fn))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D))))
      (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn D)) p0008 p0022
  have p0024 := @g_fvfullfun (syn_csn D) (syn_cpw1fn)
  have p0025 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn D)) (syn_cfv (syn_cpw1fn) (syn_csn D))
      p0023 p0024
  have p0026 := @g_pw1fnval D hyp_lnpwpw1secondfnval_2
  have p0027 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cpw1fn) (syn_csn D)) (syn_cpw1 D) p0025 p0026
  exact p0027

@[expose]
noncomputable def g_lnpwquoinputfnfn :
    Nominal.NPrf (syn_wfn (syn_clnpwquoinputfn) (syn_cvv)) :=
  by
  have p0000 := @g_fncross
  have p0001 := @g_fnresi (syn_cvv)
  have p0002 := @g_resid (syn_cid)
  have p0003 := @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0002
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0001 p0003
  have p0005 := @g_fnfullfun (syn_cpw1fn)
  have p0006 := @g_n_2ndex
  have p0007 := @g_wppimagefn (syn_c2nd) p0006
  have p0008 := @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0005 p0007
  have p0009 := (Nominal.classEqRefl (syn_clnpwpw1secondfn))
  have p0010 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn)
      (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0009
  have p0011 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv))
      p0008 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv))
      p0004 p0011
  have p0013 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_clnpwpw1secondfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @g_inidm (syn_cvv)
  have p0016 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0015
  have p0017 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cvv)) p0014 p0016
  have p0018 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0000 p0017
  have p0019 := (Nominal.classEqRefl (syn_clnpwquoinputfn))
  have p0020 :=
    @g_fneq1i (syn_cvv) (syn_clnpwquoinputfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) p0019
  have p0021 :=
    @g_mpbir (syn_wfn (syn_clnpwquoinputfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) (syn_cvv))
      p0018 p0020
  exact p0021

@[expose]
noncomputable def g_lnpwquoinputfnex :
    Nominal.NPrf (.classMem (syn_clnpwquoinputfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwquoinputfn))
  have p0001 := @g_crossex
  have p0002 := @g_idex
  have p0003 := (Nominal.classEqRefl (syn_clnpwpw1secondfn))
  have p0004 := @g_pw1fnex
  have p0005 := @g_fullfunex (syn_cpw1fn) p0004
  have p0006 := @g_n_2ndex
  have p0007 := @g_imageex (syn_c2nd) p0006
  have p0008 := @g_coex (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0005 p0007
  have p0009 :=
    @g_eqeltri (syn_clnpwpw1secondfn)
      (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv) p0003 p0008
  have p0010 := @g_txpex (syn_cid) (syn_clnpwpw1secondfn) p0002 p0009
  have p0011 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0001 p0010
  have p0012 :=
    @g_eqeltri (syn_clnpwquoinputfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) (syn_cvv) p0000
      p0011
  exact p0012

@[expose]
noncomputable def g_lnpwquoinputfnval (D : Class) (R : Class)
    (hyp_lnpwquoinputfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwquoinputfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
        (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwquoinputfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwquoinputfn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) p0000
  have p0002 := @g_fnresi (syn_cvv)
  have p0003 := @g_resid (syn_cid)
  have p0004 := @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0003
  have p0005 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0002 p0004
  have p0006 := @g_fnfullfun (syn_cpw1fn)
  have p0007 := @g_n_2ndex
  have p0008 := @g_wppimagefn (syn_c2nd) p0007
  have p0009 := @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0006 p0008
  have p0010 := (Nominal.classEqRefl (syn_clnpwpw1secondfn))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn)
      (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv))
      p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv))
      p0005 p0012
  have p0014 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_clnpwpw1secondfn)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_inidm (syn_cvv)
  have p0017 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0016
  have p0018 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cvv)) p0015 p0017
  have p0019 := @g_snex (syn_cop R D)
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cvv))
      (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_ccross)
      (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)))
        (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccross)
        (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D))))
      p0001 p0022
  have p0036 :=
    @g_fvtxpvv (syn_csn (syn_cop R D)) (syn_cid) (syn_clnpwpw1secondfn) p0005 p0012 p0019
  have p0038 := @g_fvi (syn_csn (syn_cop R D)) (syn_cvv)
  have p0039 := Nominal.mp p0019 p0038
  have p0040 := @g_lnpwpw1secondfnval D R hyp_lnpwquoinputfnval_1 hyp_lnpwquoinputfnval_2
  have p0041 :=
    @g_opeq12i (syn_cfv (syn_cid) (syn_csn (syn_cop R D))) (syn_csn (syn_cop R D))
      (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D) p0039 p0040
  have p0042 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D)))
      (syn_cop (syn_cfv (syn_cid) (syn_csn (syn_cop R D)))
        (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))))
      (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D)) p0036 p0041
  have p0043 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D)))
      (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_ccross) p0042
  have p0044 :=
    @g_eqtri (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccross)
        (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D))))
      (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0023 p0043
  have p0045 :=
    (Nominal.classEqRefl (syn_co (syn_csn (syn_cop R D)) (syn_ccross) (syn_cpw1 D)))
  have p0046 :=
    @g_eqcomi (syn_co (syn_csn (syn_cop R D)) (syn_ccross) (syn_cpw1 D))
      (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0045
  have p0048 := @g_pw1ex D hyp_lnpwquoinputfnval_2
  have p0049 :=
    @g_pm3_2i (.classMem (syn_csn (syn_cop R D)) (syn_cvv))
      (.classMem (syn_cpw1 D) (syn_cvv)) p0019 p0048
  have p0050 := @g_ovcross (syn_csn (syn_cop R D)) (syn_cpw1 D) (syn_cvv) (syn_cvv)
  have p0051 := Nominal.mp p0049 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_co (syn_csn (syn_cop R D)) (syn_ccross) (syn_cpw1 D))
      (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) p0046 p0051
  have p0053 :=
    @g_eqtri (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) p0044 p0052
  exact p0053

@[expose]
noncomputable def g_lnpwquofnfn : Nominal.NPrf (syn_wfn (syn_clnpwquofn) (syn_cvv)) :=
  by
  have p0000 := @g_lnpwclassfnex
  have p0001 := @g_wppimagefn (syn_clnpwclassfn) p0000
  have p0002 := @g_lnpwquoinputfnfn
  have p0003 :=
    @g_fncovv (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn) p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_clnpwquofn))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwquofn)
      (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwquofn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) (syn_cvv))
      p0003 p0005
  exact p0006

@[expose]
noncomputable def g_lnpwquofnex : Nominal.NPrf (.classMem (syn_clnpwquofn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwquofn))
  have p0001 := @g_lnpwclassfnex
  have p0002 := @g_imageex (syn_clnpwclassfn) p0001
  have p0003 := @g_lnpwquoinputfnex
  have p0004 := @g_coex (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_clnpwquofn)
      (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) (syn_cvv) p0000
      p0004
  exact p0005

@[expose]
noncomputable def g_lnpwquofnrawval (D : Class) (R : Class)
    (hyp_lnpwquofnrawval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwquofnrawval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D)))
        (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwquofn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwquofn)
      (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) p0000
  have p0002 := @g_lnpwquoinputfnfn
  have p0003 := @g_snex (syn_cop R D)
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_clnpwquoinputfn) (syn_cvv))
      (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_cimage (syn_clnpwclassfn))
      (syn_clnpwquoinputfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn))
        (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cimage (syn_clnpwclassfn))
        (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))))
      p0001 p0006
  have p0008 := @g_lnpwquoinputfnval D R hyp_lnpwquofnrawval_1 hyp_lnpwquofnrawval_2
  have p0009 :=
    @g_fveq2i (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
      (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cimage (syn_clnpwclassfn)) p0008
  have p0010 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cimage (syn_clnpwclassfn))
        (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))))
      (syn_cfv (syn_cimage (syn_clnpwclassfn)) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      p0007 p0009
  have p0011 := @g_lnpwclassfnex
  have p0013 := @g_pw1ex D hyp_lnpwquofnrawval_2
  have p0014 := @g_xpex (syn_csn (syn_cop R D)) (syn_cpw1 D) p0003 p0013
  have p0015 :=
    @g_fvimagecl (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_clnpwclassfn) p0011
      p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_cimage (syn_clnpwclassfn)) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0010
      p0015
  exact p0016

@[expose]
noncomputable def g_lnpwclassfnsnval (D : Class) (R : Class) (X : Class)
    (hyp_lnpwclassfnsnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwclassfnsnval_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (_hyp_lnpwclassfnsnval_3 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn X)))
        (syn_cec X (syn_clnker R))) :=
  by
  have p0000 := @g_snex X
  have p0001 :=
    @g_lnpwclassfnval D R (syn_csn X) hyp_lnpwclassfnsnval_1 hyp_lnpwclassfnsnval_2 p0000
  have p0002 := (Nominal.classEqRefl (syn_clnker R))
  have p0003 := @g_cnveqi (syn_clnker R) (syn_cin R (syn_ccnv R)) p0002
  have p0004 := @g_cnvin R (syn_ccnv R)
  have p0005 := @g_cnvcnv R
  have p0006 := @g_ineq2i (syn_ccnv (syn_ccnv R)) R (syn_ccnv R) p0005
  have p0007 :=
    @g_eqtri (syn_ccnv (syn_cin R (syn_ccnv R)))
      (syn_cin (syn_ccnv R) (syn_ccnv (syn_ccnv R))) (syn_cin (syn_ccnv R) R) p0004 p0006
  have p0008 :=
    @g_eqtri (syn_ccnv (syn_clnker R)) (syn_ccnv (syn_cin R (syn_ccnv R)))
      (syn_cin (syn_ccnv R) R) p0003 p0007
  have p0009 := @g_incom (syn_ccnv R) R
  have p0010 :=
    @g_eqtri (syn_ccnv (syn_clnker R)) (syn_cin (syn_ccnv R) R) (syn_cin R (syn_ccnv R))
      p0008 p0009
  have p0012 := @g_eqcomi (syn_clnker R) (syn_cin R (syn_ccnv R)) p0002
  have p0013 :=
    @g_eqtri (syn_ccnv (syn_clnker R)) (syn_cin R (syn_ccnv R)) (syn_clnker R) p0010 p0012
  have p0014 := @g_imaeq1i (syn_ccnv (syn_clnker R)) (syn_clnker R) (syn_csn X) p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn X)))
      (syn_cima (syn_ccnv (syn_clnker R)) (syn_csn X))
      (syn_cima (syn_clnker R) (syn_csn X)) p0001 p0014
  have p0016 := (Nominal.classEqRefl (syn_cec X (syn_clnker R)))
  have p0017 :=
    @g_eqcomi (syn_cec X (syn_clnker R)) (syn_cima (syn_clnker R) (syn_csn X)) p0016
  have p0018 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn X)))
      (syn_cima (syn_clnker R) (syn_csn X)) (syn_cec X (syn_clnker R)) p0015 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnpwquofnrawexact (D : Class) (R : Class)
    (hyp_lnpwquofnrawexact_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwquofnrawexact_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
        (syn_cqs D (syn_clnker R))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let c : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_c_ne_z : c ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_c : z ≠ c := Ne.symm fresh_c_ne_z
  have fresh_c_ne_s : c ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_s_ne_c : s ≠ c := Ne.symm fresh_c_ne_s
  have fresh_c_ne_p : c ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_c : p ≠ c := Ne.symm fresh_c_ne_p
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_z_ne_s : z ≠ s :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_z : s ≠ z := Ne.symm fresh_z_ne_s
  have fresh_z_ne_p : z ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
  have fresh_s_ne_p : s ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_s : p ≠ s := Ne.symm fresh_s_ne_p
  have fresh_s_ne_x : s ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_s : x ≠ s := Ne.symm fresh_s_ne_x
  have dv_cache_0001 : z ∉ ((Class.cv c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_c, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_D, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_clnpwclassfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_csn (syn_cop R D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_D, or_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_csn (syn_cop R D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_p_not_R, fresh_p_not_D, or_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_csn (syn_cop R D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_s_not_R, fresh_s_not_D, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_z_not_D,
          not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0009 : s ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_s_not_D,
          not_false_eq_true])
  have dv_cache_0010 :
    p ∉ ((Wff.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_z, fresh_p_ne_c, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    s ∉ ((Wff.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_z, fresh_s_ne_c, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    z ∉
      ((Wff.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_s, fresh_z_ne_c,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : z ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show z ≠ p from (by exact fresh_z_ne_p))
  have dv_cache_0014 : z ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show z ≠ s from (by exact fresh_z_ne_s))
  have dv_cache_0015 : p ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show p ≠ s from (by exact fresh_p_ne_s))
  have dv_cache_0016 : s ∉ ((Wff.classEq (.cv p) (syn_cop R D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_p, fresh_s_not_R, fresh_s_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_cop R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_p_not_R, fresh_p_not_D, or_false, not_false_eq_true])
  have dv_cache_0018 :
    p ∉
      ((syn_wrex s (syn_cpw1 D)
          (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s)))
            (.cv c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_p_not_D, fresh_p_not_R, fresh_p_ne_s, fresh_p_ne_c,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_s, not_false_eq_true])
  have dv_cache_0020 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0021 :
    x ∉
      ((Wff.imp (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
          (.classMem (.cv c) (syn_cqs D (syn_clnker R))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_R, fresh_x_not_D, fresh_x_ne_s, fresh_x_ne_c,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : s ∉ ((Wff.classMem (.cv c) (syn_cqs D (syn_clnker R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_c, fresh_s_not_D, fresh_s_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0023 :
    c ∉
      ((syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_c_not_R, fresh_c_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0024 : c ∉ ((syn_cqs D (syn_clnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cqs,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          fresh_c_not_D, fresh_c_not_R, or_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_c, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_clnker R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          fresh_x_not_R, not_false_eq_true])
  have dv_cache_0027 :
    x ∉
      ((Wff.classMem (.cv c) (syn_cima (syn_clnpwclassfn)
            (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_c, fresh_x_not_R, fresh_x_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_lnpwclassfnfn
  have p0001 := @g_fnfun (syn_cvv) (syn_clnpwclassfn)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_fvelima z (.cv c) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_clnpwclassfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_mpan (syn_wfun (syn_clnpwclassfn))
      (.classMem (.cv c)
        (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))
      (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c)))
      p0002 p0003
  have p0005 := @g_id (.classEq (.cv z) (syn_cop (.cv p) (.cv s)))
  have p0006 :=
    @g_fveq2d (.classEq (.cv z) (syn_cop (.cv p) (.cv s))) (.cv z)
      (syn_cop (.cv p) (.cv s)) (syn_clnpwclassfn) p0005
  have p0007 :=
    @g_eqeq1d (.classEq (.cv z) (syn_cop (.cv p) (.cv s)))
      (syn_cfv (syn_clnpwclassfn) (.cv z))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c) p0006
  have p0008 :=
    @g_rexxp (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c)) z p s
      (syn_csn (syn_cop R D)) (syn_cpw1 D) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 p0007
  have p0009 := @g_opex R D hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2
  have p0010 := @g_id (.classEq (.cv p) (syn_cop R D))
  have p0011 :=
    @g_opeq1d (.classEq (.cv p) (syn_cop R D)) (.cv p) (syn_cop R D) (.cv s) p0010
  have p0012 :=
    @g_fveq2d (.classEq (.cv p) (syn_cop R D)) (syn_cop (.cv p) (.cv s))
      (syn_cop (syn_cop R D) (.cv s)) (syn_clnpwclassfn) p0011
  have p0013 :=
    @g_eqeq1d (.classEq (.cv p) (syn_cop R D))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s)))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c) p0012
  have p0014 :=
    @g_rexbidv (.classEq (.cv p) (syn_cop R D))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)) s
      (syn_cpw1 D) dv_cache_0016 p0013
  have p0015 :=
    @g_rexsn
      (syn_wrex s (syn_cpw1 D)
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c)))
      (syn_wrex s (syn_cpw1 D)
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      p (syn_cop R D) dv_cache_0017 dv_cache_0018 p0009 p0014
  have p0016 :=
    @g_bitri
      (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c)))
      (syn_wrex p (syn_csn (syn_cop R D)) (syn_wrex s (syn_cpw1 D)
          (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (.cv p) (.cv s))) (.cv c))))
      (syn_wrex s (syn_cpw1 D)
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      p0008 p0015
  have p0017 := @g_elpw1 x (.cv s) D dv_cache_0019 dv_cache_0020
  have p0018 :=
    @g_n_3simpc (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0019 :=
    @g_simpr (.classEq (.cv s) (syn_csn (.cv x)))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0020 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (syn_wa (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
      p0018 p0019
  have p0021 :=
    @g_eqcomd
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c) p0020
  have p0022 :=
    @g_n_3simpa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
  have p0023 := @g_simpr (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
  have p0024 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (syn_wa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))))
      (.classEq (.cv s) (syn_csn (.cv x))) p0022 p0023
  have p0025 := @g_id (.classEq (.cv s) (syn_csn (.cv x)))
  have p0026 :=
    @g_opeq2d (.classEq (.cv s) (syn_csn (.cv x))) (.cv s) (syn_csn (.cv x)) (syn_cop R D)
      p0025
  have p0027 :=
    @g_fveq2d (.classEq (.cv s) (syn_csn (.cv x))) (syn_cop (syn_cop R D) (.cv s))
      (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnpwclassfn) p0026
  have p0028 := @g_vex x
  have p0029 :=
    @g_lnpwclassfnsnval D R (.cv x) hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2 p0028
  have p0030 :=
    @g_syl6eq (.classEq (.cv s) (syn_csn (.cv x)))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s)))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cec (.cv x) (syn_clnker R)) p0027 p0029
  have p0031 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (.classEq (.cv s) (syn_csn (.cv x)))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s)))
        (syn_cec (.cv x) (syn_clnker R)))
      p0024 p0030
  have p0032 :=
    @g_eqcomd
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s)))
      (syn_cec (.cv x) (syn_clnker R)) p0031
  have p0033 :=
    @g_eqtr4d
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (.cv c) (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s)))
      (syn_cec (.cv x) (syn_clnker R)) p0021 p0032
  have p0035 := @g_simpl (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
  have p0036 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (syn_wa (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x))))
      (.classMem (.cv x) D) p0022 p0035
  have p0037 := @g_lnkerex R hyp_lnpwquofnrawexact_1
  have p0038 := @g_ecelqsi D (.cv x) (syn_clnker R) p0037
  have p0039 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (.classMem (.cv x) D)
      (.classMem (syn_cec (.cv x) (syn_clnker R)) (syn_cqs D (syn_clnker R))) p0036 p0038
  have p0040 :=
    @g_eqeltrd
      (syn_w3a (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (.cv c) (syn_cec (.cv x) (syn_clnker R)) (syn_cqs D (syn_clnker R)) p0033 p0039
  have p0041 :=
    @g_n_3exp (.classMem (.cv x) D) (.classEq (.cv s) (syn_csn (.cv x)))
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
      (.classMem (.cv c) (syn_cqs D (syn_clnker R))) p0040
  have p0042 :=
    @g_rexlimiv (.classEq (.cv s) (syn_csn (.cv x)))
      (.imp (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
        (.classMem (.cv c) (syn_cqs D (syn_clnker R))))
      x D dv_cache_0021 p0041
  have p0043 :=
    @g_sylbi (.classMem (.cv s) (syn_cpw1 D))
      (syn_wrex x D (.classEq (.cv s) (syn_csn (.cv x))))
      (.imp (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
        (.classMem (.cv c) (syn_cqs D (syn_clnker R))))
      p0017 p0042
  have p0044 :=
    @g_rexlimiv
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c))
      (.classMem (.cv c) (syn_cqs D (syn_clnker R))) s (syn_cpw1 D) dv_cache_0022 p0043
  have p0045 :=
    @g_sylbi
      (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c)))
      (syn_wrex s (syn_cpw1 D)
        (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (.cv s))) (.cv c)))
      (.classMem (.cv c) (syn_cqs D (syn_clnker R))) p0016 p0044
  have p0046 :=
    @g_syl
      (.classMem (.cv c)
        (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))
      (syn_wrex z (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
        (.classEq (syn_cfv (syn_clnpwclassfn) (.cv z)) (.cv c)))
      (.classMem (.cv c) (syn_cqs D (syn_clnker R))) p0004 p0045
  have p0047 :=
    @g_ssriv c
      (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_cqs D (syn_clnker R)) dv_cache_0023 dv_cache_0024 p0046
  have p0048 := @g_eqid (syn_cqs D (syn_clnker R))
  have p0049 := @g_id (.classEq (syn_cec (.cv x) (syn_clnker R)) (.cv c))
  have p0050 :=
    @g_eleq1d (.classEq (syn_cec (.cv x) (syn_clnker R)) (.cv c))
      (syn_cec (.cv x) (syn_clnker R)) (.cv c)
      (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0049
  have p0053 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cec (.cv x) (syn_clnker R)))
      (.classMem (.cv x) D) p0029
  have p0055 := @g_snid (syn_cop R D) p0009
  have p0056 :=
    @g_a1i (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (.classMem (.cv x) D) p0055
  have p0057 := @g_id (.classMem (.cv x) D)
  have p0058 := @g_snelpw1 (.cv x) D
  have p0059 :=
    @g_sylibr (.classMem (.cv x) D) (.classMem (.cv x) D)
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0057 p0058
  have p0060 :=
    @g_jca (.classMem (.cv x) D) (.classMem (syn_cop R D) (syn_csn (syn_cop R D)))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0056 p0059
  have p0061 :=
    @g_opelxp (syn_cop R D) (syn_csn (.cv x)) (syn_csn (syn_cop R D)) (syn_cpw1 D)
  have p0062 :=
    @g_sylibr (.classMem (.cv x) D)
      (syn_wa (.classMem (syn_cop R D) (syn_csn (syn_cop R D)))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 D)))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      p0060 p0061
  have p0067 := @g_snex (.cv x)
  have p0068 := @g_opex (syn_cop R D) (syn_csn (.cv x)) p0009 p0067
  have p0070 := @g_fndm (syn_cvv) (syn_clnpwclassfn)
  have p0071 := Nominal.mp p0000 p0070
  have p0072 :=
    @g_eleqtrri (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)
      (syn_cdm (syn_clnpwclassfn)) p0068 p0071
  have p0073 :=
    @g_pm3_2i (syn_wfun (syn_clnpwclassfn))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cdm (syn_clnpwclassfn)))
      p0002 p0072
  have p0074 :=
    @g_funfvima (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
      (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnpwclassfn)
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @g_syl (.classMem (.cv x) D)
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (.classMem (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))
      p0062 p0075
  have p0077 :=
    @g_eqeltrrd (.classMem (.cv x) D)
      (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cec (.cv x) (syn_clnker R))
      (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0053
      p0076
  have p0078 :=
    @g_ectocl
      (.classMem (syn_cec (.cv x) (syn_clnker R))
        (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))
      (.classMem (.cv c)
        (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))))
      x (.cv c) D (syn_clnker R) (syn_cqs D (syn_clnker R)) dv_cache_0025 dv_cache_0020
      dv_cache_0026 dv_cache_0027 p0048 p0050 p0077
  have p0079 :=
    @g_ssriv c (syn_cqs D (syn_clnker R))
      (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      dv_cache_0024 dv_cache_0023 p0078
  have p0080 :=
    @g_eqssi (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_cqs D (syn_clnker R)) p0047 p0079
  exact p0080

@[expose]
noncomputable def g_lnpwquofnval (D : Class) (R : Class)
    (hyp_lnpwquofnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwquofnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D)))
        (syn_cqs D (syn_clnker R))) :=
  by
  have p0000 := @g_lnpwquofnrawval D R hyp_lnpwquofnval_1 hyp_lnpwquofnval_2
  have p0001 := @g_lnpwquofnrawexact D R hyp_lnpwquofnval_1 hyp_lnpwquofnval_2
  have p0002 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D)))
      (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_cqs D (syn_clnker R)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_lnpairraisefnfn :
    Nominal.NPrf (syn_wfn (syn_clnpairraisefn) (syn_cvv)) :=
  by
  have p0000 := @g_n_1stex
  have p0001 := @g_wppimagefn (syn_c1st) p0000
  have p0002 := @g_n_2ndex
  have p0003 := @g_wppimagefn (syn_c2nd) p0002
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv)) p0001 p0003
  have p0005 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_inidm (syn_cvv)
  have p0008 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0007
  have p0009 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0006
      p0008
  have p0010 := (Nominal.classEqRefl (syn_clnpairraisefn))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnpairraisefn)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnpairraisefn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0009
      p0011
  exact p0012

@[expose]
noncomputable def g_lnpairraisefnval (X : Class) (Y : Class)
    (hyp_lnpairraisefnval_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_lnpairraisefnval_2 : Nominal.NPrf (.classMem Y (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop X Y)))
        (syn_cop (syn_csn X) (syn_csn Y))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c1st)).fv := by
    exact
      (show Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c1st)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
          exact (show Disjoint (((syn_cop X Y)).fv) ((∅ : Finset Var)) from (by simp))))
  have dv_cache_0002 : Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c2nd)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((syn_csn (syn_cop X Y))).fv ((syn_c2nd)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
          exact (show Disjoint (((syn_cop X Y)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (syn_clnpairraisefn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop X Y)) (syn_clnpairraisefn)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0000
  have p0002 := @g_eqid (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
  have p0003 := @g_n_1stex
  have p0004 := @g_wppimagefn (syn_c1st) p0003
  have p0005 := @g_snex (syn_cop X Y)
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv))
      (.classMem (syn_csn (syn_cop X Y)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_fnbrfvb (syn_cvv) (syn_csn (syn_cop X Y))
      (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_cimage (syn_c1st))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
        (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))))
      (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c1st))
        (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))))
      p0002 p0008
  have p0010 := @g_eqid (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))
  have p0011 := @g_n_2ndex
  have p0012 := @g_wppimagefn (syn_c2nd) p0011
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv))
      (.classMem (syn_csn (syn_cop X Y)) (syn_cvv)) p0012 p0005
  have p0015 :=
    @g_fnbrfvb (syn_cvv) (syn_csn (syn_cop X Y))
      (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_cimage (syn_c2nd))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_mpbi
      (.classEq (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))
      (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c2nd))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))
      p0010 p0016
  have p0018 :=
    @g_pm3_2i
      (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c1st))
        (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))))
      (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c2nd))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))
      p0009 p0017
  have p0019 :=
    @g_trtxp (syn_csn (syn_cop X Y))
      (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
      (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_cimage (syn_c1st))
      (syn_cimage (syn_c2nd))
  have p0020 :=
    @g_mpbir
      (syn_wbr (syn_csn (syn_cop X Y))
        (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
        (syn_cop (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
          (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))))
      (syn_wa (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c1st))
          (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))))
        (syn_wbr (syn_csn (syn_cop X Y)) (syn_cimage (syn_c2nd))
          (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))))
      p0018 p0019
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv)) p0004 p0012
  have p0026 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @g_inidm (syn_cvv)
  have p0029 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) p0028
  have p0030 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0027
      p0029
  have p0031 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @g_funbrfv (syn_csn (syn_cop X Y))
      (syn_cop (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
  have p0034 := Nominal.mp p0032 p0033
  have p0035 := Nominal.mp p0020 p0034
  have p0038 := @g_wppfvimage (syn_csn (syn_cop X Y)) (syn_c1st) dv_cache_0001 p0003 p0005
  have p0039 := @g_dfdm4 (syn_csn (syn_cop X Y))
  have p0040 :=
    @g_eqcomi (syn_cdm (syn_csn (syn_cop X Y)))
      (syn_cima (syn_c1st) (syn_csn (syn_cop X Y))) p0039
  have p0041 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
      (syn_cima (syn_c1st) (syn_csn (syn_cop X Y))) (syn_cdm (syn_csn (syn_cop X Y)))
      p0038 p0040
  have p0042 := @g_dmsnop X Y hyp_lnpairraisefnval_2
  have p0043 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
      (syn_cdm (syn_csn (syn_cop X Y))) (syn_csn X) p0041 p0042
  have p0046 := @g_wppfvimage (syn_csn (syn_cop X Y)) (syn_c2nd) dv_cache_0002 p0011 p0005
  have p0047 := @g_dfrn5 (syn_csn (syn_cop X Y))
  have p0048 :=
    @g_eqcomi (syn_crn (syn_csn (syn_cop X Y)))
      (syn_cima (syn_c2nd) (syn_csn (syn_cop X Y))) p0047
  have p0049 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))
      (syn_cima (syn_c2nd) (syn_csn (syn_cop X Y))) (syn_crn (syn_csn (syn_cop X Y)))
      p0046 p0048
  have p0050 := @g_rnsnop X Y hyp_lnpairraisefnval_1
  have p0051 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y)))
      (syn_crn (syn_csn (syn_cop X Y))) (syn_csn Y) p0049 p0050
  have p0052 :=
    @g_opeq12i (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y))) (syn_csn X)
      (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))) (syn_csn Y) p0043 p0051
  have p0053 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
        (syn_csn (syn_cop X Y)))
      (syn_cop (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop X Y)))
        (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop X Y))))
      (syn_cop (syn_csn X) (syn_csn Y)) p0035 p0052
  have p0054 :=
    @g_eqtri (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop X Y)))
      (syn_cfv (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)))
        (syn_csn (syn_cop X Y)))
      (syn_cop (syn_csn X) (syn_csn Y)) p0001 p0053
  exact p0054

@[expose]
noncomputable def g_lnsifnfn : Nominal.NPrf (syn_wfn (syn_clnsifn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpairraisefn))
  have p0001 := @g_n_1stex
  have p0002 := @g_imageex (syn_c1st) p0001
  have p0003 := @g_n_2ndex
  have p0004 := @g_imageex (syn_c2nd) p0003
  have p0005 := @g_txpex (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)) p0002 p0004
  have p0006 :=
    @g_eqeltri (syn_clnpairraisefn)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv) p0000 p0005
  have p0007 := @g_wppimagefn (syn_clnpairraisefn) p0006
  have p0008 := @g_fnfullfun (syn_cpw1fn)
  have p0009 :=
    @g_fncovv (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)) p0007 p0008
  have p0010 := (Nominal.classEqRefl (syn_clnsifn))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnsifn)
      (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnsifn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)))
        (syn_cvv))
      p0009 p0011
  exact p0012

@[expose]
noncomputable def g_lnsifnex : Nominal.NPrf (.classMem (syn_clnsifn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnsifn))
  have p0001 := (Nominal.classEqRefl (syn_clnpairraisefn))
  have p0002 := @g_n_1stex
  have p0003 := @g_imageex (syn_c1st) p0002
  have p0004 := @g_n_2ndex
  have p0005 := @g_imageex (syn_c2nd) p0004
  have p0006 := @g_txpex (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)) p0003 p0005
  have p0007 :=
    @g_eqeltri (syn_clnpairraisefn)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv) p0001 p0006
  have p0008 := @g_imageex (syn_clnpairraisefn) p0007
  have p0009 := @g_pw1fnex
  have p0010 := @g_fullfunex (syn_cpw1fn) p0009
  have p0011 :=
    @g_coex (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)) p0008 p0010
  have p0012 :=
    @g_eqeltri (syn_clnsifn)
      (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) (syn_cvv)
      p0000 p0011
  exact p0012

@[expose]
noncomputable def g_lnsifnrawval (R : Class)
    (hyp_lnsifnrawval_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnsifn) (syn_csn R))
        (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_cpw1 R)).fv ((syn_clnpairraisefn)).fv := by
    exact
      (show Disjoint ((syn_cpw1 R)).fv ((syn_clnpairraisefn)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn];
          exact (show Disjoint ((R).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (syn_clnsifn))
  have p0001 :=
    @g_fveq1i (syn_csn R) (syn_clnsifn)
      (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn))) p0000
  have p0002 := @g_fnfullfun (syn_cpw1fn)
  have p0003 := @g_snex R
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cfullfun (syn_cpw1fn)) (syn_cvv))
      (.classMem (syn_csn R) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_csn R) (syn_cimage (syn_clnpairraisefn))
      (syn_cfullfun (syn_cpw1fn))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_fvfullfun (syn_csn R) (syn_cpw1fn)
  have p0008 := @g_pw1fnval R hyp_lnsifnrawval_1
  have p0009 :=
    @g_eqtri (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn R))
      (syn_cfv (syn_cpw1fn) (syn_csn R)) (syn_cpw1 R) p0007 p0008
  have p0010 :=
    @g_fveq2i (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn R)) (syn_cpw1 R)
      (syn_cimage (syn_clnpairraisefn)) p0009
  have p0011 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)))
        (syn_csn R))
      (syn_cfv (syn_cimage (syn_clnpairraisefn))
        (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn R)))
      (syn_cfv (syn_cimage (syn_clnpairraisefn)) (syn_cpw1 R)) p0006 p0010
  have p0012 := (Nominal.classEqRefl (syn_clnpairraisefn))
  have p0013 := @g_n_1stex
  have p0014 := @g_imageex (syn_c1st) p0013
  have p0015 := @g_n_2ndex
  have p0016 := @g_imageex (syn_c2nd) p0015
  have p0017 := @g_txpex (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd)) p0014 p0016
  have p0018 :=
    @g_eqeltri (syn_clnpairraisefn)
      (syn_ctxp (syn_cimage (syn_c1st)) (syn_cimage (syn_c2nd))) (syn_cvv) p0012 p0017
  have p0019 := @g_pw1ex R hyp_lnsifnrawval_1
  have p0020 := @g_wppfvimage (syn_cpw1 R) (syn_clnpairraisefn) dv_cache_0001 p0018 p0019
  have p0021 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)))
        (syn_csn R))
      (syn_cfv (syn_cimage (syn_clnpairraisefn)) (syn_cpw1 R))
      (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) p0011 p0020
  have p0022 :=
    @g_eqtri (syn_cfv (syn_clnsifn) (syn_csn R))
      (syn_cfv (syn_ccom (syn_cimage (syn_clnpairraisefn)) (syn_cfullfun (syn_cpw1fn)))
        (syn_csn R))
      (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) p0001 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnsifnimageexactg (R : Class) :
    Nominal.NPrf
      (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
        (.classEq (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R))) :=
  by
  let proofSupport : Finset Var := R.fv
  let c : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (h)
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (h)
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (h)
  have fresh_c_ne_s : c ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_c : s ≠ c := Ne.symm fresh_c_ne_s
  have fresh_c_ne_p : c ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_c : p ≠ c := Ne.symm fresh_c_ne_p
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_y : c ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_c : y ≠ c := Ne.symm fresh_c_ne_y
  have fresh_s_ne_p : s ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_s : p ≠ s := Ne.symm fresh_s_ne_p
  have fresh_s_ne_x : s ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_s : x ≠ s := Ne.symm fresh_s_ne_x
  have fresh_s_ne_y : s ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_s : y ≠ s := Ne.symm fresh_s_ne_y
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_p : y ≠ p := Ne.symm fresh_p_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have dv_cache_0001 : s ∉ ((Class.cv c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_c, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((syn_cpw1 R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_s_not_R,
          not_false_eq_true])
  have dv_cache_0003 : s ∉ ((syn_clnpairraisefn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_s, not_false_eq_true])
  have dv_cache_0005 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_p, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 :
    y ∉
      ((Wff.imp (.classEq (.cv s) (syn_csn (.cv p)))
          (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
            (.classMem (.cv c) (syn_csi R))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_s, fresh_y_ne_p, fresh_y_ne_c, fresh_y_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    y ∉ ((syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((Wff.imp (.classEq (.cv s) (syn_csn (.cv p)))
          (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
            (.classMem (.cv c) (syn_csi R))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_s, fresh_x_ne_p, fresh_x_ne_c, fresh_x_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    x ∉ ((syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_R, fresh_x_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    p ∉
      ((Wff.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (syn_csi R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_s, fresh_p_ne_c, fresh_p_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_p_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : s ∉ ((Wff.classMem (.cv c) (syn_csi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_c, fresh_s_not_R, or_false, not_false_eq_true])
  have dv_cache_0018 : s ∉ ((syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_s_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : c ∉ ((syn_cima (syn_clnpairraisefn) (syn_cpw1 R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_c_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : c ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_c_not_R,
          not_false_eq_true])
  have dv_cache_0021 : c ∉ ((syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_c_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0026 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0027 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0028 :
    y ∉ ((syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 :
    x ∉ ((syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, fresh_x_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_a_not_R,
          not_false_eq_true])
  have dv_cache_0031 : b ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_b_not_R,
          not_false_eq_true])
  have dv_cache_0032 : a ∉ ((syn_cima (syn_clnpairraisefn) (syn_cpw1 R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_a_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((syn_cima (syn_clnpairraisefn) (syn_cpw1 R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_b_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0034 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 := @g_lnpairraisefnfn
  have p0001 := @g_fnfun (syn_cvv) (syn_clnpairraisefn)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_fvelima s (.cv c) (syn_cpw1 R) (syn_clnpairraisefn) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0004 :=
    @g_mpan (syn_wfun (syn_clnpairraisefn))
      (.classMem (.cv c) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      (syn_wrex s (syn_cpw1 R) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      p0002 p0003
  have p0005 :=
    @g_a1i
      (.imp (.classMem (.cv c) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
        (syn_wrex s (syn_cpw1 R) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0004
  have p0006 := @g_elpw1 p (.cv s) R dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_a1i
      (syn_wb (.classMem (.cv s) (syn_cpw1 R))
        (syn_wrex p R (.classEq (.cv s) (syn_csn (.cv p)))))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0006
  have p0008 := @g_id (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
  have p0009 :=
    @g_sselda (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) R (syn_cxp (syn_cvv) (syn_cvv))
      (.cv p) p0008
  have p0010 :=
    @g_elxp x y (.cv p) (syn_cvv) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0011 :=
    @g_sylib (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (.classMem (.cv p) (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      p0009 p0010
  have p0012 :=
    @g_simpr (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p)))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0013 :=
    @g_n_3simpb
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (.cv s) (syn_csn (.cv p)))
      (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p)))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      p0012 p0013
  have p0015 :=
    @g_simpr
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)) p0014 p0015
  have p0017 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c) p0016
  have p0019 :=
    @g_n_3simpa
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (.cv s) (syn_csn (.cv p)))
      (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p)))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p))))
      p0012 p0019
  have p0021 :=
    @g_simpr
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (.cv s) (syn_csn (.cv p)))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p))))
      (.classEq (.cv s) (syn_csn (.cv p))) p0020 p0021
  have p0026 :=
    @g_simpl
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (.cv s) (syn_csn (.cv p)))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_wa (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      p0020 p0026
  have p0028 :=
    @g_simpl (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0027 p0028
  have p0030 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.cv p) (syn_cop (.cv x) (.cv y)) p0029
  have p0031 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.cv s) (syn_csn (.cv p)) (syn_csn (syn_cop (.cv x) (.cv y))) p0022 p0030
  have p0032 :=
    @g_fveq2d
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.cv s) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_clnpairraisefn) p0031
  have p0033 := @g_vex x
  have p0034 := @g_vex y
  have p0035 := @g_lnpairraisefnval (.cv x) (.cv y) p0033 p0034
  have p0036 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y))))
        (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))))
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      p0035
  have p0037 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_cfv (syn_clnpairraisefn) (.cv s))
      (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) p0032 p0036
  have p0038 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.cv c) (syn_cfv (syn_clnpairraisefn) (.cv s))
      (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) p0017 p0037
  have p0046 :=
    @g_simpl (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p)))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
  have p0047 := @g_simpr (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (.classMem (.cv p) R) p0046 p0047
  have p0049 :=
    @g_eqeltrrd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.cv p) (syn_cop (.cv x) (.cv y)) R p0029 p0048
  have p0052 := @g_opsnelsi (.cv x) (.cv y) R p0033 p0034
  have p0053 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.classMem (syn_cop (.cv x) (.cv y)) R)
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (syn_csi R)) p0049 p0052
  have p0054 :=
    @g_eqeltrd
      (syn_wa (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)) (syn_w3a
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
          (.classEq (.cv s) (syn_csn (.cv p)))
          (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))))
      (.cv c) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (syn_csi R) p0038 p0053
  have p0055 :=
    @g_ex (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_w3a (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
        (.classEq (.cv s) (syn_csn (.cv p)))
        (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      (.classMem (.cv c) (syn_csi R)) p0054
  have p0056 :=
    @g_n_3expd (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq (.cv s) (syn_csn (.cv p)))
      (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
      (.classMem (.cv c) (syn_csi R)) p0055
  have p0057 :=
    @g_exlimdv (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.imp (.classEq (.cv s) (syn_csn (.cv p)))
        (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (syn_csi R))))
      y dv_cache_0011 dv_cache_0012 p0056
  have p0058 :=
    @g_exlimdv (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_wex y (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (.imp (.classEq (.cv s) (syn_csn (.cv p)))
        (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (syn_csi R))))
      x dv_cache_0013 dv_cache_0014 p0057
  have p0059 :=
    @g_mpd (syn_wa (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      (.imp (.classEq (.cv s) (syn_csn (.cv p)))
        (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (syn_csi R))))
      p0011 p0058
  have p0060 :=
    @g_ex (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv p) R)
      (.imp (.classEq (.cv s) (syn_csn (.cv p)))
        (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (syn_csi R))))
      p0059
  have p0061 :=
    @g_rexlimdv (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (.classEq (.cv s) (syn_csn (.cv p)))
      (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
        (.classMem (.cv c) (syn_csi R)))
      p R dv_cache_0015 dv_cache_0016 p0060
  have p0062 :=
    @g_sylbid (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (.cv s) (syn_cpw1 R))
      (syn_wrex p R (.classEq (.cv s) (syn_csn (.cv p))))
      (.imp (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
        (.classMem (.cv c) (syn_csi R)))
      p0007 p0061
  have p0063 :=
    @g_rexlimdv (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c))
      (.classMem (.cv c) (syn_csi R)) s (syn_cpw1 R) dv_cache_0017 dv_cache_0018 p0062
  have p0064 :=
    @g_syld (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (.classMem (.cv c) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      (syn_wrex s (syn_cpw1 R) (.classEq (syn_cfv (syn_clnpairraisefn) (.cv s)) (.cv c)))
      (.classMem (.cv c) (syn_csi R)) p0005 p0063
  have p0065 :=
    @g_ssrdv (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) c
      (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R) dv_cache_0019 dv_cache_0020
      dv_cache_0021 p0064
  have p0066 := @g_id (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
  have p0067 := (Nominal.biimpRefl (syn_wbr (.cv a) (syn_csi R) (.cv b)))
  have p0068 :=
    @g_sylibr (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
      (syn_wbr (.cv a) (syn_csi R) (.cv b)) p0066 p0067
  have p0069 :=
    @g_brsi x y (.cv a) (.cv b) R dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0010
  have p0070 :=
    @g_n_3simpa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0071 :=
    @g_simpl (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
  have p0072 :=
    @g_syl
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))))
      (.classEq (.cv a) (syn_csn (.cv x))) p0070 p0071
  have p0074 :=
    @g_simpr (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
  have p0075 :=
    @g_syl
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y))))
      (.classEq (.cv b) (syn_csn (.cv y))) p0070 p0074
  have p0076 :=
    @g_opeq12d
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (.cv a) (syn_csn (.cv x)) (.cv b) (syn_csn (.cv y)) p0072 p0075
  have p0080 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y))))
        (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))))
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      p0035
  have p0081 :=
    @g_eqtr4d
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_cop (.cv a) (.cv b)) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))
      (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y)))) p0076 p0080
  have p0082 :=
    @g_n_3simpb (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0083 := @g_simpr (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv x) R (.cv y))
  have p0084 :=
    @g_syl
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0082 p0083
  have p0085 := (Nominal.biimpRefl (syn_wbr (.cv x) R (.cv y)))
  have p0086 :=
    @g_sylib
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) R) p0084 p0085
  have p0087 := @g_snelpw1 (syn_cop (.cv x) (.cv y)) R
  have p0088 :=
    @g_sylibr
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (.classMem (syn_cop (.cv x) (.cv y)) R)
      (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cpw1 R)) p0086 p0087
  have p0092 := @g_snex (syn_cop (.cv x) (.cv y))
  have p0094 := @g_fndm (syn_cvv) (syn_clnpairraisefn)
  have p0095 := Nominal.mp p0000 p0094
  have p0096 :=
    @g_eleqtrri (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cvv)
      (syn_cdm (syn_clnpairraisefn)) p0092 p0095
  have p0097 :=
    @g_pm3_2i (syn_wfun (syn_clnpairraisefn))
      (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cdm (syn_clnpairraisefn))) p0002
      p0096
  have p0098 :=
    @g_funfvima (syn_cpw1 R) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_clnpairraisefn)
  have p0099 := Nominal.mp p0097 p0098
  have p0100 :=
    @g_syl
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cpw1 R))
      (.classMem (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y))))
        (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      p0088 p0099
  have p0101 :=
    @g_eqeltrd
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_cop (.cv a) (.cv b))
      (syn_cfv (syn_clnpairraisefn) (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) p0081 p0100
  have p0102 :=
    (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)))
  have p0103 :=
    @g_sylibr
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) p0101 p0102
  have p0104 :=
    @g_exlimiv
      (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) y
      dv_cache_0028 p0103
  have p0105 :=
    @g_exlimiv
      (syn_wex y
        (syn_w3a (.classEq (.cv a) (syn_csn (.cv x))) (.classEq (.cv b) (syn_csn (.cv y)))
          (syn_wbr (.cv x) R (.cv y))))
      (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) x
      dv_cache_0029 p0104
  have p0106 :=
    @g_sylbi (syn_wbr (.cv a) (syn_csi R) (.cv b))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv a) (syn_csn (.cv x)))
            (.classEq (.cv b) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) p0069 p0105
  have p0107 :=
    @g_syl (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
      (syn_wbr (.cv a) (syn_csi R) (.cv b))
      (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b)) p0068 p0106
  have p0109 :=
    @g_biimpi (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      p0102
  have p0110 :=
    @g_syl (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
      (syn_wbr (.cv a) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      p0107 p0109
  have p0111 := Nominal.gen p0110 b
  have p0112 := Nominal.gen p0111 a
  have p0113 :=
    @g_ssrel a b (syn_csi R) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) dv_cache_0030
      dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
  have p0114 :=
    @g_mpbir (syn_wss (syn_csi R) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      (.all a (.all b (.imp (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi R))
            (.classMem (syn_cop (.cv a) (.cv b))
              (syn_cima (syn_clnpairraisefn) (syn_cpw1 R))))))
      p0112 p0113
  have p0115 :=
    @g_a1i (syn_wss (syn_csi R) (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0114
  have p0116 :=
    @g_eqssd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R) p0065 p0115
  exact p0116


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnsifnvalg (R : Class)
    (hyp_lnsifnvalg_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
        (.classEq (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_csi R))) :=
  by
  have p0000 := @g_lnsifnrawval R hyp_lnsifnvalg_1
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnsifn) (syn_csn R))
        (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0000
  have p0002 := @g_lnsifnimageexactg R
  have p0003 :=
    @g_eqtrd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (syn_cfv (syn_clnsifn) (syn_csn R))
      (syn_cima (syn_clnpairraisefn) (syn_cpw1 R)) (syn_csi R) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_lnpwsirelfnfn : Nominal.NPrf (syn_wfn (syn_clnpwsirelfn) (syn_cvv)) :=
  by
  have p0000 := @g_lnsifnfn
  have p0001 := @g_n_1stex
  have p0002 := @g_wppimagefn (syn_c1st) p0001
  have p0003 := @g_fncovv (syn_clnsifn) (syn_cimage (syn_c1st)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_clnpwsirelfn))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwsirelfn)
      (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwsirelfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_cvv)) p0003 p0005
  exact p0006

@[expose]
noncomputable def g_lnpwsirelfnex :
    Nominal.NPrf (.classMem (syn_clnpwsirelfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnpwsirelfn))
  have p0001 := @g_lnsifnex
  have p0002 := @g_n_1stex
  have p0003 := @g_imageex (syn_c1st) p0002
  have p0004 := @g_coex (syn_clnsifn) (syn_cimage (syn_c1st)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_clnpwsirelfn) (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st)))
      (syn_cvv) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_lnpwsirelfnrawval (D : Class) (R : Class)
    (_hyp_lnpwsirelfnrawval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwsirelfnrawval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
        (syn_cfv (syn_clnsifn) (syn_csn R))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c1st)).fv := by
    exact
      (show Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c1st)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
          exact (show Disjoint (((syn_cop R D)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (syn_clnpwsirelfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwsirelfn)
      (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) p0000
  have p0002 := @g_n_1stex
  have p0003 := @g_wppimagefn (syn_c1st) p0002
  have p0004 := @g_snex (syn_cop R D)
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c1st)) (syn_cvv))
      (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_clnsifn) (syn_cimage (syn_c1st))
  have p0007 := Nominal.mp p0005 p0006
  have p0010 := @g_wppfvimage (syn_csn (syn_cop R D)) (syn_c1st) dv_cache_0001 p0002 p0004
  have p0011 := @g_dfdm4 (syn_csn (syn_cop R D))
  have p0012 :=
    @g_eqcomi (syn_cdm (syn_csn (syn_cop R D)))
      (syn_cima (syn_c1st) (syn_csn (syn_cop R D))) p0011
  have p0013 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D)))
      (syn_cima (syn_c1st) (syn_csn (syn_cop R D))) (syn_cdm (syn_csn (syn_cop R D)))
      p0010 p0012
  have p0014 := @g_dmsnop R D hyp_lnpwsirelfnrawval_2
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D)))
      (syn_cdm (syn_csn (syn_cop R D))) (syn_csn R) p0013 p0014
  have p0016 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D))) (syn_csn R)
      (syn_clnsifn) p0015
  have p0017 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_clnsifn) (syn_cfv (syn_cimage (syn_c1st)) (syn_csn (syn_cop R D))))
      (syn_cfv (syn_clnsifn) (syn_csn R)) p0007 p0016
  have p0018 :=
    @g_eqtri (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_ccom (syn_clnsifn) (syn_cimage (syn_c1st))) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_clnsifn) (syn_csn R)) p0001 p0017
  exact p0018

@[expose]
noncomputable def g_lnpwsirelfnvalg (D : Class) (R : Class)
    (hyp_lnpwsirelfnvalg_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnpwsirelfnvalg_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
        (.classEq (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_csi R))) :=
  by
  have p0000 := @g_lnpwsirelfnrawval D R hyp_lnpwsirelfnvalg_1 hyp_lnpwsirelfnvalg_2
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
        (syn_cfv (syn_clnsifn) (syn_csn R)))
      (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0000
  have p0002 := @g_lnsifnvalg R hyp_lnpwsirelfnvalg_1
  have p0003 :=
    @g_eqtrd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D)))
      (syn_cfv (syn_clnsifn) (syn_csn R)) (syn_csi R) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_pw1subuniss (x : Var) (A : Class) :
    Nominal.NPrf (.imp (syn_wss (.cv x) (syn_cpw1 A)) (syn_wss (syn_cuni (.cv x)) A)) :=
  by
  have p0000 := @g_uniss (.cv x) (syn_cpw1 A)
  have p0001 := @g_unipw1 A
  have p0002 := @g_sseq2i (syn_cuni (syn_cpw1 A)) A (syn_cuni (.cv x)) p0001
  have p0003 :=
    @g_biimpi (syn_wss (syn_cuni (.cv x)) (syn_cuni (syn_cpw1 A)))
      (syn_wss (syn_cuni (.cv x)) A) p0002
  have p0004 :=
    @g_syl (syn_wss (.cv x) (syn_cpw1 A))
      (syn_wss (syn_cuni (.cv x)) (syn_cuni (syn_cpw1 A))) (syn_wss (syn_cuni (.cv x)) A)
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_pw1subunine (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (syn_wne (syn_cuni (.cv x)) (syn_c0))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_x, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_wne (syn_cuni (.cv x)) (syn_c0))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    q ∉ ((syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @g_simpr (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))
  have p0001 := @g_n0 q (.cv x) dv_cache_0001
  have p0002 :=
    @g_biimpi (syn_wne (.cv x) (syn_c0)) (syn_wex q (.classMem (.cv q) (.cv x))) p0001
  have p0003 :=
    @g_syl (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
      (syn_wne (.cv x) (syn_c0)) (syn_wex q (.classMem (.cv q) (.cv x))) p0000 p0002
  have p0004 := @g_vex q
  have p0005 := @g_uniex (.cv q) p0004
  have p0006 := @g_snid (syn_cuni (.cv q)) p0005
  have p0007 :=
    @g_a1i (.classMem (syn_cuni (.cv q)) (syn_csn (syn_cuni (.cv q))))
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
      (.classMem (.cv q) (.cv x))
  have p0009 := @g_simpl (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cpw1 A)) p0008 p0009
  have p0011 :=
    @g_simpr (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
      (.classMem (.cv q) (.cv x))
  have p0012 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (.cv x) (syn_cpw1 A) (.cv q) p0010 p0011
  have p0013 := @g_hnwpw1argcl A q
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (.cv q) (syn_cpw1 A))
      (syn_wa (.classMem (syn_cuni (.cv q)) A) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0012 p0013
  have p0015 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (syn_cuni (.cv q)) A) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
      p0014
  have p0016 :=
    @g_eleqtrrd
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (syn_cuni (.cv q)) (syn_csn (syn_cuni (.cv q))) (.cv q) p0007 p0015
  have p0018 :=
    @g_jca
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (syn_cuni (.cv q)) (.cv q)) (.classMem (.cv q) (.cv x)) p0016 p0011
  have p0019 := @g_elunii (syn_cuni (.cv q)) (.cv q) (.cv x)
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (.cv q)) (.classMem (.cv q) (.cv x)))
      (.classMem (syn_cuni (.cv q)) (syn_cuni (.cv x))) p0018 p0019
  have p0021 := @g_ne0i (syn_cuni (.cv x)) (syn_cuni (.cv q))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (syn_cuni (.cv q)) (syn_cuni (.cv x)))
      (syn_wne (syn_cuni (.cv x)) (syn_c0)) p0020 p0021
  have p0023 :=
    @g_exlimddv (syn_wa (syn_wss (.cv x) (syn_cpw1 A)) (syn_wne (.cv x) (syn_c0)))
      (.classMem (.cv q) (.cv x)) (syn_wne (syn_cuni (.cv x)) (syn_c0)) q dv_cache_0002
      dv_cache_0003 p0003 p0022
  exact p0023

@[expose]
noncomputable def g_wppreachopfn (F : Class)
    (hyp_wppreachopfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cimage (syn_ccnv F)) (syn_cvv)) :=
  by
  have p0000 := @g_cnvex F hyp_wppreachopfn_1
  have p0001 := @g_wppimagefn (syn_ccnv F) p0000
  exact p0001

@[expose]
noncomputable def g_wppreachupperex (C : Class) :
    Nominal.NPrf (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)) :=
  by
  have p0000 := @g_lecex
  have p0001 := @g_snex C
  have p0002 := @g_imaex (syn_clec) (syn_csn C) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wppreach0 (C : Class) (F : Class) (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wppreachorbitfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_c0c)) (syn_cima (syn_clec) (syn_csn C))) :=
  by
  have dv_cache_0001 :
    Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv := by
    exact
      (show Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show Disjoint (((syn_ccnv F)).fv) ((((syn_clec)).fv) ∪ (((syn_csn C)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (((syn_ccnv F)).fv) (((syn_clec)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((syn_clec)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec];
                            exact
                              (show Disjoint ((F).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint (((syn_ccnv F)).fv) (((syn_csn C)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((syn_csn C)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                            exact
                              (show Disjoint (F).fv (C).fv from
                                (by exact dv_C_F.symm))))))⟩))))
  have p0000 := @g_cnvex F hyp_wppreachorbitfn_1
  have p0001 := @g_wppimagefn (syn_ccnv F) p0000
  have p0002 := @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @g_imageex (syn_ccnv F) p0000
  have p0006 := @g_elfuns (syn_cimage (syn_ccnv F)) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (syn_wfun (syn_cimage (syn_ccnv F))) p0003 p0006
  have p0008 := @g_lecex
  have p0009 := @g_snex C
  have p0010 := @g_imaex (syn_clec) (syn_csn C) p0008 p0009
  have p0013 := @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0014 := Nominal.mp p0001 p0013
  have p0015 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0010 p0014
  have p0016 := @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0021 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0016 p0014
  have p0022 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
      (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))
      p0007 p0015 p0021
  have p0023 :=
    @g_wpporbit0 (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) dv_cache_0001
  have p0024 := Nominal.mp p0022 p0023
  exact p0024

@[expose]
noncomputable def g_elwppcand (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_cwppcand F C))
        (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C))
          (.classMem D (syn_cwppreach F C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcand F C))
  have p0001 :=
    @g_eleq2i (syn_cwppcand F C)
      (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
        (syn_cwppreach F C))
      D p0000
  have p0002 :=
    @g_elin D
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_cwppreach F C)
  have p0003 :=
    @g_elin D (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0004 := @g_eliniseg (syn_clec) C D
  have p0005 :=
    @g_anbi2i (.classMem D (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_wbr D (syn_clec) C) (.classMem D (syn_chwcards (syn_cvv))) p0004
  have p0006 :=
    @g_bitri
      (.classMem D
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_wa (.classMem D (syn_chwcards (syn_cvv)))
        (.classMem D (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C)) p0003 p0005
  have p0007 :=
    @g_anbi1i
      (.classMem D
        (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
      (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C))
      (.classMem D (syn_cwppreach F C)) p0006
  have p0008 :=
    @g_bitri
      (.classMem D (syn_cin
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
          (syn_cwppreach F C)))
      (syn_wa (.classMem D
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))
        (.classMem D (syn_cwppreach F C)))
      (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C))
        (.classMem D (syn_cwppreach F C)))
      p0002 p0007
  have p0009 :=
    @g_bitri (.classMem D (syn_cwppcand F C))
      (.classMem D (syn_cin
          (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
          (syn_cwppreach F C)))
      (syn_wa (syn_wa (.classMem D (syn_chwcards (syn_cvv))) (syn_wbr D (syn_clec) C))
        (.classMem D (syn_cwppreach F C)))
      p0001 p0008
  exact p0009

@[expose]
noncomputable def g_hwcnwendv (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (A).fv from (by exact dv_A_u)))))),
                  (show Disjoint ((A).fv) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 := @g_hwcnpair u A
  have p0001 := @g_hwcnraw u A
  have p0002 :=
    @g_eqeltrrd (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)
      p0000 p0001
  have p0003 := @g_fvex (.cv u) (syn_c1st)
  have p0004 := @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_elhwcodes A (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001
      p0003 p0004
  have p0006 :=
    @g_biimpi
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      p0005
  have p0007 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      p0002 p0006
  have p0008 :=
    @g_simpl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)
  have p0009 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0007
      p0008
  exact p0009

@[expose]
noncomputable def g_hwbaseswev (r : Var) (d : Var) (dv_d_r : d ≠ r) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv d) (syn_chwbases (syn_cvv)))
        (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d)))) :=
  by
  let proofSupport : Finset Var := ({ r } : Finset Var) ∪ ({ d } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u := Ne.symm fresh_u_ne_r
  have fresh_u_ne_d : u ≠ d := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : Disjoint ((syn_cvv)).fv ((Class.cv d)).fv := by
    exact
      (show Disjoint ((syn_cvv)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact (show Disjoint ((∅ : Finset Var)) (({ d } : Finset Var)) from (by simp))))
  have dv_cache_0002 : u ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_d, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    r ∉ ((syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_u, (Ne.symm dv_d_r), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_r, fresh_u_ne_d,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 :
    Disjoint ((syn_cvv)).fv ((syn_cin (.cv r) (syn_cxp (.cv d) (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((syn_cvv)).fv ((syn_cin (.cv r) (syn_cxp (.cv d) (.cv d)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
          exact
            (show
              Disjoint ((∅ : Finset Var))
                ((((Class.cv r)).fv) ∪ (((syn_cxp (.cv d) (.cv d))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((∅ : Finset Var)) (((Class.cv r)).fv) from (by simp)),
                  (show Disjoint ((∅ : Finset Var)) (((syn_cxp (.cv d) (.cv d))).fv) from
                    (by simp))⟩))))
  have dv_cache_0008 :
    u ∉ ((syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_r, fresh_u_ne_d, or_false, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_chwcn (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0010 :
    u ∉
      ((Wff.classEq (.cv d) (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_d, fresh_u_ne_r, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((Wff.classMem (.cv d) (syn_chwbases (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_d_r), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elhwbases u (syn_cvv) (.cv d) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_chwbases (syn_cvv)))
      (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      p0000
  have p0002 := @g_hwcnwendv u (syn_cvv) dv_cache_0002
  have p0003 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn (syn_cvv)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))) p0002
  have p0004 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn (syn_cvv)))
      (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))
  have p0005 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      (.cv d) (syn_cfv (syn_c2nd) (.cv u)) p0004
  have p0006 :=
    @g_breq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (.cv u)) (.cv d) (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0005
  have p0007 :=
    @g_mpbid
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d)) p0003 p0006
  have p0008 := @g_fvex (.cv u) (syn_c1st)
  have p0009 := @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0010 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
      (syn_cfv (syn_c1st) (.cv u)) (.cv d) (syn_cwe) p0009
  have p0011 :=
    @g_spcev (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d)) r
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0004 dv_cache_0005 p0008 p0010
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (.cv d))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0007 p0011
  have p0013 :=
    @g_ex (.classMem (.cv u) (syn_chwcn (syn_cvv)))
      (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0012
  have p0014 :=
    @g_rexlimiv (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) u (syn_chwcn (syn_cvv))
      dv_cache_0006 p0013
  have p0015 :=
    @g_syl (.classMem (.cv d) (syn_chwbases (syn_cvv)))
      (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0001 p0014
  have p0016 := @g_id (syn_wbr (.cv r) (syn_cwe) (.cv d))
  have p0017 := @g_ssid (.cv d)
  have p0018 := @g_a1i (syn_wss (.cv d) (.cv d)) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0017
  have p0019 := @g_brex (.cv r) (.cv d) (syn_cwe)
  have p0020 := @g_simpr (.classMem (.cv r) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0021 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv d) (syn_cvv)))
      (.classMem (.cv d) (syn_cvv)) p0019 p0020
  have p0022 :=
    @g_werestrndv (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.cv d) (.cv d) (.cv r) p0016 p0018
      p0021
  have p0023 := @g_ssv (.cv d)
  have p0024 :=
    @g_a1i (syn_wss (.cv d) (syn_cvv)) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0023
  have p0025 :=
    @g_jca (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cwe) (.cv d))
      (syn_wss (.cv d) (syn_cvv)) p0022 p0024
  have p0026 := @g_vex r
  have p0027 := @g_vex d
  have p0029 := @g_xpex (.cv d) (.cv d) p0027 p0027
  have p0030 := @g_inex (.cv r) (syn_cxp (.cv d) (.cv d)) p0026 p0029
  have p0032 :=
    @g_elhwcodes (syn_cvv) (.cv d) (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d)))
      dv_cache_0007 p0030 p0027
  have p0033 :=
    @g_biimpri
      (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
        (syn_chwcodes (syn_cvv)))
      (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cwe) (.cv d))
        (syn_wss (.cv d) (syn_cvv)))
      p0032
  have p0034 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cwe) (.cv d))
        (syn_wss (.cv d) (syn_cvv)))
      (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
        (syn_chwcodes (syn_cvv)))
      p0025 p0033
  have p0035 := @g_inss2 (.cv r) (syn_cxp (.cv d) (.cv d))
  have p0042 := @g_opfv1st (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0030 p0027
  have p0049 := @g_opfv2nd (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0030 p0027
  have p0057 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (.cv d)
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (.cv d) p0049 p0049
  have p0058 :=
    @g_sseq12i
      (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d)))
      (syn_cxp
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))
      (syn_cxp (.cv d) (.cv d)) p0042 p0057
  have p0059 :=
    @g_mpbir
      (syn_wss
        (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))))
      (syn_wss (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (syn_cxp (.cv d) (.cv d)))
      p0035 p0058
  have p0060 :=
    @g_a1i
      (syn_wss
        (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))))
      (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0059
  have p0061 :=
    @g_jca (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
        (syn_chwcodes (syn_cvv)))
      (syn_wss
        (syn_cfv (syn_c1st) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))))
      p0034 p0060
  have p0068 := @g_opex (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d) p0030 p0027
  have p0069 :=
    @g_elhwcncl (syn_cvv) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
  have p0070 := Nominal.mp p0068 p0069
  have p0071 :=
    @g_biimpri
      (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
        (syn_chwcn (syn_cvv)))
      (syn_wa (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
          (syn_chwcodes (syn_cvv))) (syn_wss (syn_cfv (syn_c1st)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
            (syn_cfv (syn_c2nd)
              (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))))
      p0070
  have p0072 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wa (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
          (syn_chwcodes (syn_cvv))) (syn_wss (syn_cfv (syn_c1st)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))) (syn_cxp
            (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
            (syn_cfv (syn_c2nd)
              (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))))
      (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
        (syn_chwcn (syn_cvv)))
      p0061 p0071
  have p0080 :=
    @g_eqcomi
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (.cv d) p0049
  have p0081 :=
    @g_a1i
      (.classEq (.cv d) (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))
      (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0080
  have p0082 :=
    @g_jca (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
        (syn_chwcn (syn_cvv)))
      (.classEq (.cv d) (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))
      p0072 p0081
  have p0083 :=
    @g_id (.classEq (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
  have p0084 :=
    @g_fveq2d
      (.classEq (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)) (syn_c2nd)
      p0083
  have p0085 :=
    @g_eqeq2d
      (.classEq (.cv u) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))
      (.cv d) p0084
  have p0086 :=
    @g_rspcev (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u)))
      (.classEq (.cv d) (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))))
      u (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
      (syn_chwcn (syn_cvv)) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0085
  have p0087 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wa (.classMem (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d))
          (syn_chwcn (syn_cvv))) (.classEq (.cv d) (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (.cv r) (syn_cxp (.cv d) (.cv d))) (.cv d)))))
      (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      p0082 p0086
  have p0089 :=
    @g_biimpri (.classMem (.cv d) (syn_chwbases (syn_cvv)))
      (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      p0000
  have p0090 :=
    @g_syl (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (syn_wrex u (syn_chwcn (syn_cvv)) (.classEq (.cv d) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv d) (syn_chwbases (syn_cvv))) p0087 p0089
  have p0091 :=
    @g_exlimiv (syn_wbr (.cv r) (syn_cwe) (.cv d))
      (.classMem (.cv d) (syn_chwbases (syn_cvv))) r dv_cache_0011 p0090
  have p0092 :=
    @g_impbii (.classMem (.cv d) (syn_chwbases (syn_cvv)))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0015 p0091
  exact p0092

@[expose]
noncomputable def g_elhwcardswev (k : Var) (s : Var) (d : Var) (dv_d_k : d ≠ k)
    (dv_d_s : d ≠ s) (dv_k_s : k ≠ s) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
              (.classEq (.cv k) (syn_cnc (.cv d))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ k } : Finset Var) ∪ ({ s } : Finset Var) ∪ ({ d } : Finset Var)
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_s : r ≠ s := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have fresh_r_ne_d : r ≠ d := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_r : d ≠ r := Ne.symm fresh_r_ne_d
  have dv_cache_0001 : Disjoint ((syn_cvv)).fv ((Class.cv k)).fv := by
    exact
      (show Disjoint ((syn_cvv)).fv ((Class.cv k)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact (show Disjoint ((∅ : Finset Var)) (({ k } : Finset Var)) from (by simp))))
  have dv_cache_0002 : r ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_k, not_false_eq_true])
  have dv_cache_0004 : r ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0005 : s ∉ ((Wff.classEq (.cv k) (syn_cnc (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_s), fresh_s_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0006 : s ∉ ((Wff.classEq (.cv d) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_d_s), fresh_s_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0007 : d ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_r, not_false_eq_true])
  have dv_cache_0008 :
    d ∉
      ((syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r))
            (.classEq (.cv k) (syn_cnc (.cv r)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_d_s, fresh_d_ne_r, dv_d_k,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    r ∉
      ((syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
              (.classEq (.cv k) (syn_cnc (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_ne_s, fresh_r_ne_d,
          fresh_r_ne_k, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_s, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((syn_wbr (.cv s) (syn_cwe) (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_s, fresh_r_ne_d, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0013 : r ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_d, not_false_eq_true])
  have dv_cache_0014 : r ∉ ((syn_chwbases (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0015 : r ∉ ((Wff.classEq (.cv k) (syn_cnc (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_k, fresh_r_ne_d, or_false, not_false_eq_true])
  have dv_cache_0016 : d ∉ ((Wff.classMem (.cv k) (syn_chwcards (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, dv_d_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0017 : s ∉ ((Wff.classMem (.cv k) (syn_chwcards (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_s), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_vex k
  have p0001 :=
    @g_elhwcards (syn_cvv) (.cv k) r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) p0001
  have p0003 := @g_hwbaseswev s r dv_cache_0004
  have p0004 :=
    @g_biimpi (.classMem (.cv r) (syn_chwbases (syn_cvv)))
      (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) p0003
  have p0005 :=
    @g_adantr (.classMem (.cv r) (syn_chwbases (syn_cvv)))
      (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (.classEq (.cv k) (syn_cnc (.cv r)))
      p0004
  have p0006 :=
    Nominal.ax1 (.classEq (.cv k) (syn_cnc (.cv r))) (syn_wbr (.cv s) (syn_cwe) (.cv r))
  have p0007 :=
    @g_alrimiv (.classEq (.cv k) (syn_cnc (.cv r)))
      (.imp (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))) s
      dv_cache_0005 p0006
  have p0008 :=
    @g_exintrbi (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))) s
  have p0009 :=
    @g_syl (.classEq (.cv k) (syn_cnc (.cv r)))
      (.all s (.imp (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))
      (syn_wb (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))))))
      p0007 p0008
  have p0010 :=
    @g_adantl (.classEq (.cv k) (syn_cnc (.cv r)))
      (syn_wb (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r))) (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r))))))
      (.classMem (.cv r) (syn_chwbases (syn_cvv))) p0009
  have p0011 :=
    @g_mpbid
      (syn_wa (.classMem (.cv r) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv r))))
      (syn_wex s (syn_wbr (.cv s) (syn_cwe) (.cv r)))
      (syn_wex s
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))
      p0005 p0010
  have p0012 := @g_vex r
  have p0013 := @g_id (.classEq (.cv d) (.cv r))
  have p0014 :=
    @g_breq2d (.classEq (.cv d) (.cv r)) (.cv d) (.cv r) (.cv s) (syn_cwe) p0013
  have p0016 := @g_nceqd (.classEq (.cv d) (.cv r)) (.cv d) (.cv r) p0013
  have p0017 :=
    @g_eqeq2d (.classEq (.cv d) (.cv r)) (syn_cnc (.cv d)) (syn_cnc (.cv r)) (.cv k) p0016
  have p0018 :=
    @g_anbi12d (.classEq (.cv d) (.cv r)) (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv d)))
      (.classEq (.cv k) (syn_cnc (.cv r))) p0014 p0017
  have p0019 :=
    @g_exbidv (.classEq (.cv d) (.cv r))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))) s
      dv_cache_0006 p0018
  have p0020 :=
    @g_spcev
      (syn_wex s
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))
      (syn_wex s
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))
      d (.cv r) dv_cache_0007 dv_cache_0008 p0012 p0019
  have p0021 :=
    @g_syl
      (syn_wa (.classMem (.cv r) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv r))))
      (syn_wex s
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv r)) (.classEq (.cv k) (syn_cnc (.cv r)))))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      p0011 p0020
  have p0022 :=
    @g_ex (.classMem (.cv r) (syn_chwbases (syn_cvv)))
      (.classEq (.cv k) (syn_cnc (.cv r)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      p0021
  have p0023 :=
    @g_rexlimiv (.classEq (.cv k) (syn_cnc (.cv r)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      r (syn_chwbases (syn_cvv)) dv_cache_0009 p0022
  have p0024 :=
    @g_syl (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r))))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      p0002 p0023
  have p0025 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))
  have p0026 := @g_vex s
  have p0027 := @g_id (.classEq (.cv r) (.cv s))
  have p0028 :=
    @g_breq1d (.classEq (.cv r) (.cv s)) (.cv r) (.cv s) (.cv d) (syn_cwe) p0027
  have p0029 :=
    @g_spcev (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv d)) r
      (.cv s) dv_cache_0010 dv_cache_0011 p0026 p0028
  have p0030 := @g_hwbaseswev r d dv_cache_0012
  have p0031 :=
    @g_biimpri (.classMem (.cv d) (syn_chwbases (syn_cvv)))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d))) p0030
  have p0032 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wex r (syn_wbr (.cv r) (syn_cwe) (.cv d)))
      (.classMem (.cv d) (syn_chwbases (syn_cvv))) p0029 p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv d) (syn_chwbases (syn_cvv)))
      p0025 p0032
  have p0034 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))
  have p0035 :=
    @g_jca
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (.classMem (.cv d) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv d)))
      p0033 p0034
  have p0036 := @g_id (.classEq (.cv r) (.cv d))
  have p0037 := @g_nceqd (.classEq (.cv r) (.cv d)) (.cv r) (.cv d) p0036
  have p0038 :=
    @g_eqeq2d (.classEq (.cv r) (.cv d)) (syn_cnc (.cv r)) (syn_cnc (.cv d)) (.cv k) p0037
  have p0039 :=
    @g_rspcev (.classEq (.cv k) (syn_cnc (.cv r))) (.classEq (.cv k) (syn_cnc (.cv d))) r
      (.cv d) (syn_chwbases (syn_cvv)) dv_cache_0013 dv_cache_0014 dv_cache_0015 p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wa (.classMem (.cv d) (syn_chwbases (syn_cvv))) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) p0035
      p0039
  have p0043 :=
    @g_biimpri (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r)))) p0001
  have p0044 :=
    @g_syl
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wrex r (syn_chwbases (syn_cvv)) (.classEq (.cv k) (syn_cnc (.cv r))))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) p0040 p0043
  have p0045 :=
    @g_exlimivv
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) d s dv_cache_0016 dv_cache_0017 p0044
  have p0046 :=
    @g_impbii (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      p0024 p0045
  exact p0046


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwcardslecanti (k : Var) (m : Var) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (.classMem (.cv m) (syn_chwcards (syn_cvv)))) (.imp
          (syn_wa (syn_wbr (.cv k) (syn_clec) (.cv m)) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (.classEq (.cv k) (.cv m)))) :=
  by
  have p0000 :=
    @g_simpl (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (.classMem (.cv m) (syn_chwcards (syn_cvv)))
  have p0001 := @g_hwcardssnc (syn_cvv)
  have p0002 := @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv k)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (.classMem (.cv m) (syn_chwcards (syn_cvv))))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv k) (syn_cncs)) p0000
      p0003
  have p0005 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (.classMem (.cv m) (syn_chwcards (syn_cvv)))
  have p0007 := @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv m)
  have p0008 := Nominal.mp p0001 p0007
  have p0009 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (.classMem (.cv m) (syn_chwcards (syn_cvv))))
      (.classMem (.cv m) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_cncs)) p0005
      p0008
  have p0010 :=
    @g_jca
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (.classMem (.cv m) (syn_chwcards (syn_cvv))))
      (.classMem (.cv k) (syn_cncs)) (.classMem (.cv m) (syn_cncs)) p0004 p0009
  have p0011 := @g_sbth (.cv k) (.cv m)
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
        (.classMem (.cv m) (syn_chwcards (syn_cvv))))
      (syn_wa (.classMem (.cv k) (syn_cncs)) (.classMem (.cv m) (syn_cncs)))
      (.imp (syn_wa (syn_wbr (.cv k) (syn_clec) (.cv m)) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (.classEq (.cv k) (.cv m)))
      p0010 p0011
  exact p0012

@[expose]
noncomputable def g_wpporbitfnndv (F : Class) (I : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wfn (syn_cfrec F I) (syn_cnnc))) :=
  by
  have p0000 := @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0002 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_fnfrec
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_cfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_wpporbit0ndv (F : Class) (I : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (.classEq (syn_cfv (syn_cfrec F I) (syn_c0c)) I)) :=
  by
  have p0000 := @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0002 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_frec0
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_cfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_wpporbitsucndv (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c)))
          (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) :=
  by
  have p0000 := @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0002 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem F (syn_cfuns)) p0001 p0002
  have p0005 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0006 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem I (syn_cdm F)) p0001 p0005
  have p0008 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0009 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wss (syn_crn F) (syn_cdm F)) p0001 p0008
  have p0010 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0011 :=
    @g_frecsuc
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_cfrec F I) F I N p0000 p0003 p0006 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_lnwpwccore (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv)
    (hyp_lnwpwccore_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_lnwpwccore_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnwpwccore_3 : Nominal.NPrf (.classMem (syn_cop R A) (syn_clnpwc A))) :
    Nominal.NPrf
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
          (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_ellnpwcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnwpwccore_2 hyp_lnwpwccore_1
  have p0001 :=
    @g_mpbi (.classMem (syn_cop R A) (syn_clnpwc A))
      (syn_wa (.classMem (syn_cop R A) (syn_clntpc A))
        (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A))
      hyp_lnwpwccore_3 p0000
  have p0002 :=
    @g_simpl (.classMem (syn_cop R A) (syn_clntpc A))
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_ellntpcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnwpwccore_1 hyp_lnwpwccore_2
      hyp_lnwpwccore_1
  have p0005 :=
    @g_mpbi (.classMem (syn_cop R A) (syn_clntpc A))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
            (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))) (.classEq A A))
      p0003 p0004
  have p0006 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
          (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A)))
      (.classEq A A)
  have p0007 := Nominal.mp p0005 p0006
  exact p0007

@[expose]
noncomputable def g_lnworigqordwe (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv)
    (hyp_lnworigqordwe_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_lnworigqordwe_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_lnworigqordwe_3 : Nominal.NPrf (.classMem (syn_cop R A) (syn_clnpwc A))) :
    Nominal.NPrf (syn_wbr (syn_clnqord R A) (syn_cwe) (syn_clnquo R A)) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem A (syn_cvv)) hyp_lnworigqordwe_2
      hyp_lnworigqordwe_1
  have p0001 :=
    @g_lnwpwccore A R dv_cache_0001 hyp_lnworigqordwe_1 hyp_lnworigqordwe_2
      hyp_lnworigqordwe_3
  have p0002 :=
    @g_pm3_2i (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
          (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A)))
      p0000 p0001
  have p0003 :=
    @g_ellnpwcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnworigqordwe_2
      hyp_lnworigqordwe_1
  have p0004 :=
    @g_biimpi (.classMem (syn_cop R A) (syn_clnpwc A))
      (syn_wa (.classMem (syn_cop R A) (syn_clntpc A))
        (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A))
      p0003
  have p0005 := Nominal.mp hyp_lnworigqordwe_3 p0004
  have p0006 :=
    @g_simpr (.classMem (syn_cop R A) (syn_clntpc A))
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A))
            (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))))
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A) p0002 p0007
  have p0009 := @g_lnqordwe A R dv_cache_0001
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

@[expose]
noncomputable def g_wppreachsucndv (C : Class) (F : Class) (N : Class)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv)
    (dv_F_N : Disjoint F.fv N.fv)
    (hyp_wppreachsucndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (.classEq
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_cplc N (syn_c1c))) (syn_cima (syn_ccnv F) (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)))) :=
  by
  have dv_cache_0001 :
    Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv := by
    exact
      (show Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show Disjoint (((syn_ccnv F)).fv) ((((syn_clec)).fv) ∪ (((syn_csn C)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (((syn_ccnv F)).fv) (((syn_clec)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((syn_clec)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec];
                            exact
                              (show Disjoint ((F).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint (((syn_ccnv F)).fv) (((syn_csn C)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((syn_csn C)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                            exact
                              (show Disjoint (F).fv (C).fv from
                                (by exact dv_C_F.symm))))))⟩))))
  have dv_cache_0002 : Disjoint ((syn_cimage (syn_ccnv F))).fv (N).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((syn_cimage (syn_ccnv F))).fv (N).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage];
          exact
            (show Disjoint (((syn_ccnv F)).fv) ((N).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                exact (show Disjoint (F).fv (N).fv from (by exact dv_F_N))))))
  have dv_cache_0003 : Disjoint ((syn_cima (syn_clec) (syn_csn C))).fv (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((syn_cima (syn_clec) (syn_csn C))).fv (N).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show Disjoint ((((syn_clec)).fv) ∪ (((syn_csn C)).fv)) ((N).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((syn_clec)).fv) ((N).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec];
                      exact (show Disjoint ((∅ : Finset Var)) ((N).fv) from (by simp)))),
                  (show Disjoint (((syn_csn C)).fv) ((N).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                      exact (show Disjoint (C).fv (N).fv from (by exact dv_C_N))))⟩))))
  have p0000 := @g_wppreachopfn F hyp_wppreachsucndv_1
  have p0001 := @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_cnvex F hyp_wppreachsucndv_1
  have p0004 := @g_imageex (syn_ccnv F) p0003
  have p0005 := @g_elfuns (syn_cimage (syn_ccnv F)) p0004
  have p0006 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (syn_wfun (syn_cimage (syn_ccnv F))) p0002 p0005
  have p0007 := @g_wppreachupperex C
  have p0009 := @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0010 := Nominal.mp p0000 p0009
  have p0011 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0007 p0010
  have p0012 := @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0016 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0012 p0010
  have p0017 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
      (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))
      p0006 p0011 p0016
  have p0018 :=
    @g_a1i
      (syn_w3a (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
        (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
        (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))))
      (.classMem N (syn_cnnc)) p0017
  have p0019 := @g_id (.classMem N (syn_cnnc))
  have p0020 :=
    @g_jca (.classMem N (syn_cnnc))
      (syn_w3a (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
        (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
        (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))))
      (.classMem N (syn_cnnc)) p0018 p0019
  have p0021 :=
    @g_wpporbitsuc (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) N
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0022 :=
    @g_syl (.classMem N (syn_cnnc))
      (syn_wa (syn_w3a (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
          (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
          (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))))
        (.classMem N (syn_cnnc)))
      (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_cplc N (syn_c1c))) (syn_cfv (syn_cimage (syn_ccnv F))
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)))
      p0020 p0021
  have p0024 :=
    @g_fvex N (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0025 :=
    @g_fvimagecl
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)
      (syn_ccnv F) p0003 p0024
  have p0026 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cimage (syn_ccnv F))
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N))
        (syn_cima (syn_ccnv F)
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)))
      (.classMem N (syn_cnnc)) p0025
  have p0027 :=
    @g_eqtrd (.classMem N (syn_cnnc))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cplc N (syn_c1c)))
      (syn_cfv (syn_cimage (syn_ccnv F))
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N))
      (syn_cima (syn_ccnv F)
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N))
      p0022 p0026
  exact p0027

@[expose]
noncomputable def g_wpppredfamex (C : Class) (F : Class)
    (hyp_wpppredfamex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppredfam F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppredfam F C))
  have p0001 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0002 := @g_cnvex F hyp_wpppredfamex_1
  have p0003 := @g_imageex (syn_ccnv F) p0002
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0001 p0003
  have p0005 := @g_tcfnex
  have p0006 :=
    @g_coex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_ctcfn) p0004 p0005
  have p0007 :=
    @g_cnvex
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
      p0006
  have p0008 :=
    @g_imageex
      (syn_ccnv
        (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))
      p0007
  have p0009 := @g_ssetex
  have p0010 := @g_imageex (syn_csset) p0009
  have p0011 :=
    @g_coex
      (syn_cimage (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      (syn_cimage (syn_csset)) p0008 p0010
  have p0012 :=
    @g_eqeltri (syn_cwpppredfam F C)
      (syn_ccom (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cimage (syn_csset)))
      (syn_cvv) p0000 p0011
  exact p0012

@[expose]
noncomputable def g_wppimagefun (R : Class) : Nominal.NPrf (syn_wfun (syn_cimage R)) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (h)
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
  have dv_cache_0001 : x ∉ ((syn_cimage R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cimage R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cimage R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_z_not_R,
          not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @g_vex x
  have p0001 := @g_vex y
  have p0002 := @g_brimage (.cv x) (.cv y) R p0000 p0001
  have p0004 := @g_vex z
  have p0005 := @g_brimage (.cv x) (.cv z) R p0000 p0004
  have p0006 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_cimage R) (.cv y))
      (.classEq (.cv y) (syn_cima R (.cv x))) (syn_wbr (.cv x) (syn_cimage R) (.cv z))
      (.classEq (.cv z) (syn_cima R (.cv x))) p0002 p0005
  have p0007 := @g_eqtr3 (.cv y) (.cv z) (syn_cima R (.cv x))
  have p0008 :=
    @g_sylbi
      (syn_wa (syn_wbr (.cv x) (syn_cimage R) (.cv y)) (syn_wbr (.cv x) (syn_cimage R) (.cv z)))
      (syn_wa (.classEq (.cv y) (syn_cima R (.cv x))) (.classEq (.cv z) (syn_cima R (.cv x))))
      (.classEq (.cv y) (.cv z)) p0006 p0007
  have p0009 := Nominal.gen p0008 z
  have p0010 := Nominal.gen p0009 y
  have p0011 := Nominal.gen p0010 x
  have p0012 :=
    @g_dffun2 x y z (syn_cimage R) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0013_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wfun (syn_cimage R)) (.all x (.all y (.all z (.imp
                (syn_wa (syn_wbr (.cv x) (syn_cimage R) (.cv y))
                  (syn_wbr (.cv x) (syn_cimage R) (.cv z))) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cimage
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @g_mpbir (syn_wfun (syn_cimage R))
      (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cimage R) (.cv y))
                (syn_wbr (.cv x) (syn_cimage R) (.cv z))) (.classEq (.cv y) (.cv z))))))
      p0011 p0013_e01_recanon
  exact p0013

@[expose]
noncomputable def g_wppimagefv (B : Class) (G : Class)
    (hyp_wppimagefv_1 : Nominal.NPrf (.classMem G (syn_cvv)))
    (hyp_wppimagefv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage G) B) (syn_cima G B)) :=
  by
  have p0000 := @g_eqid (syn_cima G B)
  have p0001 := @g_imaex G B hyp_wppimagefv_1 hyp_wppimagefv_2
  have p0002 := @g_brimage B (syn_cima G B) G hyp_wppimagefv_2 p0001
  have p0003 :=
    @g_mpbir (syn_wbr B (syn_cimage G) (syn_cima G B))
      (.classEq (syn_cima G B) (syn_cima G B)) p0000 p0002
  have p0004 := @g_wppimagefun G
  have p0005 := @g_funbrfv B (syn_cima G B) (syn_cimage G)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := Nominal.mp p0003 p0006
  exact p0007

@[expose]
noncomputable def g_wppreachorbitfnndv (C : Class) (F : Class)
    (hyp_wppreachorbitfnndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (syn_wfn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cnnc)) :=
  by
  have p0000 := @g_cnvex F hyp_wppreachorbitfnndv_1
  have p0001 := @g_wppimagefn (syn_ccnv F) p0000
  have p0002 := @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @g_imageex (syn_ccnv F) p0000
  have p0006 := @g_elfuns (syn_cimage (syn_ccnv F)) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (syn_wfun (syn_cimage (syn_ccnv F))) p0003 p0006
  have p0008 := @g_lecex
  have p0009 := @g_snex C
  have p0010 := @g_imaex (syn_clec) (syn_csn C) p0008 p0009
  have p0013 := @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0014 := Nominal.mp p0001 p0013
  have p0015 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0010 p0014
  have p0016 := @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0021 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0016 p0014
  have p0022 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
      (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))
      p0007 p0015 p0021
  have p0023 :=
    @g_wpporbitfnndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0024 := Nominal.mp p0022 p0023
  exact p0024

@[expose]
noncomputable def g_wpppredfamfv (C : Class) (D : Class) (F : Class)
    (hyp_wpppredfamfv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))) (syn_cima (syn_ccnv
            (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppredfam F C))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn D)) (syn_cwpppredfam F C)
      (syn_ccom (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cimage (syn_csset)))
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
    @g_fvco (syn_csn (syn_csn D))
      (syn_cimage (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      (syn_cimage (syn_csset))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))
      (syn_cfv (syn_ccom (syn_cimage (syn_ccnv (syn_ccom
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctcfn)))) (syn_cimage (syn_csset))) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D))))
      p0001 p0014
  have p0018 := @g_wppimagefv (syn_csn (syn_csn D)) (syn_csset) p0005 p0004
  have p0019 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D)))
      (syn_cima (syn_csset) (syn_csn (syn_csn D)))
      (syn_cimage (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      p0018
  have p0020 :=
    @g_eqtri (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D))))
      (syn_cfv (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      p0015 p0019
  have p0021 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0022 := @g_cnvex F hyp_wpppredfamfv_1
  have p0023 := @g_imageex (syn_ccnv F) p0022
  have p0024 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0021 p0023
  have p0025 := @g_tcfnex
  have p0026 :=
    @g_coex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_ctcfn) p0024 p0025
  have p0027 :=
    @g_cnvex
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
      p0026
  have p0031 :=
    @g_wppimagefv (syn_cima (syn_csset) (syn_csn (syn_csn D)))
      (syn_ccnv
        (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))
      p0027 p0007
  have p0032 :=
    @g_eqtri (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))
      (syn_cfv (syn_cimage (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (syn_cima (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      p0020 p0031
  exact p0032

@[expose]
noncomputable def g_elwpppredfam (C : Class) (D : Class) (F : Class) (q : Var)
    (hyp_elwpppredfam_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_elwpppredfam_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv q))
          (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))) (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv q))))) :=
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
  have dv_cache_0005 :
    y ∉
      ((syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, fresh_y_not_F, fresh_y_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉
      ((Wff.classMem D (syn_cfv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)) (syn_csn (.cv q))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_q, fresh_y_not_F, fresh_y_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_wpppredfamfv C D F hyp_elwpppredfam_1
  have p0001 :=
    @g_eleq2i (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))
      (syn_cima (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
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
  have p0007 := @g_brssetsn D (.cv z) hyp_elwpppredfam_2 p0006
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
      (syn_ccnv
        (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))
      p0014
  have p0016 :=
    @g_eleq2i
      (syn_cima (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))
      (syn_cima (syn_ccnv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))) (.cab y (.classMem D (.cv y))))
      (syn_csn (.cv q)) p0015
  have p0017 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))))
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))))
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (.cab y (.classMem D (.cv y)))))
      p0001 p0016
  have p0018 := @g_wppreachorbitfnndv C F hyp_elwpppredfam_1
  have p0019 :=
    @g_fnfun (syn_cnnc)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @g_fntcfn
  have p0022 := @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 :=
    @g_pm3_2i
      (syn_wfun (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      (syn_wfun (syn_ctcfn)) p0020 p0023
  have p0025 :=
    @g_funco (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_ctcfn)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_funfn
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
  have p0028 :=
    @g_mpbi
      (syn_wfun
        (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))
      (syn_wfn (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)) (syn_cdm (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      p0026 p0027
  have p0029 :=
    @g_elpreima
      (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)))
      (syn_csn (.cv q)) (.cab y (.classMem D (.cv y)))
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @g_fvex (syn_csn (.cv q))
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
  have p0032 :=
    @g_id
      (.classEq (.cv y) (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))))
  have p0033 :=
    @g_eleq2d
      (.classEq (.cv y) (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))))
      (.cv y)
      (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)) (syn_csn (.cv q)))
      D p0032
  have p0034 :=
    @g_elab (.classMem D (.cv y))
      (.classMem D (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))))
      y
      (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)) (syn_csn (.cv q)))
      dv_cache_0005 dv_cache_0006 p0031 p0033
  have p0035 :=
    @g_elfvdm D (syn_csn (.cv q))
      (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctcfn))
  have p0036 :=
    @g_sylbi
      (.classMem (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))
      (.classMem D (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))))
      (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      p0034 p0035
  have p0037 :=
    @g_pm4_71ri
      (.classMem (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))
      (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctcfn))))
      p0036
  have p0038 :=
    @g_bicomi
      (.classMem (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))
      (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (.classMem (syn_cfv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))))
      p0037
  have p0039 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (.cab y (.classMem D (.cv y)))))
      (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)))) (.classMem (syn_cfv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))))
      (.classMem (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))
      p0030 p0038
  have p0044 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (.cab y (.classMem D (.cv y)))))
      (.classMem (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))
      (.classMem D (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))))
      p0039 p0034
  have p0046 := @g_vex q
  have p0047 := @g_snel1c (.cv q) p0046
  have p0048 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn (.cv q)) (syn_c1c))
      p0021 p0047
  have p0049 :=
    @g_fvco2 (syn_c1c) (syn_csn (.cv q))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)
  have p0050 := Nominal.mp p0048 p0049
  have p0052 := @g_tcfnfv (.cv q) p0046
  have p0053 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv q))) (syn_ctc (.cv q))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0052
  have p0054 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)) (syn_csn (.cv q)))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cfv (syn_ctcfn) (syn_csn (.cv q))))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (.cv q)))
      p0050 p0053
  have p0055 :=
    @g_eleq2i
      (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctcfn)) (syn_csn (.cv q)))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc (.cv q)))
      D p0054
  have p0056 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (.cab y (.classMem D (.cv y)))))
      (.classMem D (syn_cfv (syn_ccom
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
          (syn_csn (.cv q))))
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv q))))
      p0044 p0055
  have p0057 :=
    @g_bitri
      (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))))
      (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctcfn))) (.cab y (.classMem D (.cv y)))))
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv q))))
      p0017 p0056
  exact p0057

@[expose]
noncomputable def g_wpppostcompex (F : Class)
    (_hyp_wpppostcompex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppostcomp F) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppostcomp F))
  have p0001 := @g_composeex
  have p0002 := @g_vvex
  have p0003 := @g_snex F
  have p0004 := @g_xpex (syn_cvv) (syn_csn F) p0002 p0003
  have p0005 := @g_idex
  have p0006 := @g_txpex (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid) p0004 p0005
  have p0007 :=
    @g_coex (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0001
      p0006
  have p0008 :=
    @g_eqeltri (syn_cwpppostcomp F)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)))
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wppupperpreopex (C : Class) :
    Nominal.NPrf (.classMem (syn_cwppupperpreop C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppupperpreop C))
  have p0001 := @g_lnimageopex
  have p0002 := @g_swapex
  have p0003 := @g_imageex (syn_cswap) p0002
  have p0004 := @g_vvex
  have p0005 := @g_snex (syn_cima (syn_clec) (syn_csn C))
  have p0006 := @g_xpex (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))) p0004 p0005
  have p0007 :=
    @g_txpex (syn_cimage (syn_cswap))
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) p0003 p0006
  have p0008 :=
    @g_coex (syn_clnimageop)
      (syn_ctxp (syn_cimage (syn_cswap))
        (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))
      p0001 p0007
  have p0009 :=
    @g_eqeltri (syn_cwppupperpreop C)
      (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap))
          (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))))
      (syn_cvv) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_wpppowlayerseqex (C : Class) (F : Class)
    (hyp_wpppowlayerseqex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppowlayerseq F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowlayerseq F C))
  have p0001 := @g_wppupperpreopex C
  have p0002 := @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0003 := @g_wpppostcompex F hyp_wpppowlayerseqex_1
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid)
      p0002 p0003
  have p0005 := @g_tcfnex
  have p0006 := @g_coex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn) p0004 p0005
  have p0007 :=
    @g_coex (syn_cwppupperpreop C)
      (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_cwpppowlayerseq F C)
      (syn_ccom (syn_cwppupperpreop C)
        (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wpphitfamex (C : Class) (F : Class)
    (hyp_wpphitfamex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpphitfam F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphitfam F C))
  have p0001 := @g_wpppowlayerseqex C F hyp_wpphitfamex_1
  have p0002 := @g_cnvex (syn_cwpppowlayerseq F C) p0001
  have p0003 := @g_imageex (syn_ccnv (syn_cwpppowlayerseq F C)) p0002
  have p0004 := @g_ssetex
  have p0005 := @g_imageex (syn_csset) p0004
  have p0006 :=
    @g_coex (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))
      p0003 p0005
  have p0007 :=
    @g_eqeltri (syn_cwpphitfam F C)
      (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset)))
      (syn_cvv) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_wpppostcompfn (F : Class)
    (hyp_wpppostcompfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwpppostcomp F) (syn_cvv)) :=
  by
  have p0000 := @g_composefn
  have p0001 := @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0002 := Nominal.mp hyp_wpppostcompfn_1 p0001
  have p0003 := @g_f1ovi
  have p0004 := @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv))
      (syn_wfn (syn_cid) (syn_cvv)) p0002 p0005
  have p0007 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0009
  have p0011 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_fncovv (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0000
      p0011
  have p0013 := (Nominal.classEqRefl (syn_cwpppostcomp F))
  have p0014 :=
    @g_fneq1i (syn_cvv) (syn_cwpppostcomp F)
      (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) p0013
  have p0015 :=
    @g_mpbir (syn_wfn (syn_cwpppostcomp F) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)))
        (syn_cvv))
      p0012 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
