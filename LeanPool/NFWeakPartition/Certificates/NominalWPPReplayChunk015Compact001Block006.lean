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

/-- Checked nominal proof certificate identified upstream as `g_lnimageopval`. -/
@[expose]
noncomputable def gLnimageopval (B : Class) (R : Class)
    (hyp_lnimageopval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnimageopval_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synClnimageop) (synCop R B)) (synCima R B)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnimageop))
  have p0001 :=
    @gFveq1i (synCop R B) (synClnimageop) (synCcom (synCranfn) (synClnimageresfn))
      p0000
  have p0002 := @gFnlndifop
  have p0003 := @gLn1stfn
  have p0005 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClndifop) (synCvv)) p0003
      p0002
  have p0006 := @gFntxp (synCvv) (synCvv) (synC1st) (synClndifop)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gInidm (synCvv)
  have p0009 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv) (synCtxp (synC1st) (synClndifop))
      p0008
  have p0010 :=
    @gMpbi (synWfn (synCtxp (synC1st) (synClndifop)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClndifop)) (synCvv)) p0007 p0009
  have p0011 := @gFncovv (synClndifop) (synCtxp (synC1st) (synClndifop)) p0002 p0010
  have p0012 := (Nominal.classEqRefl (synClninterop))
  have p0013 :=
    @gFneq1i (synCvv) (synClninterop)
      (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) p0012
  have p0014 :=
    @gMpbir (synWfn (synClninterop) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synC1st) (synClndifop))) (synCvv))
      p0011 p0013
  have p0016 := @gFncross
  have p0017 := @gLn2ndfn
  have p0018 := @gVvex
  have p0019 := @gFnconstg (synCvv) (synCvv) (synCvv)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 :=
    @gPm32i (synWfn (synC2nd) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCvv))) (synCvv)) p0017 p0020
  have p0022 :=
    @gFntxp (synCvv) (synCvv) (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))
  have p0023 := Nominal.mp p0021 p0022
  have p0025 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) p0008
  have p0026 :=
    @gMpbi
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))) (synCvv))
      p0023 p0025
  have p0027 :=
    @gFncovv (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))
      p0016 p0026
  have p0028 := (Nominal.classEqRefl (synClnimagecrossfn))
  have p0029 :=
    @gFneq1i (synCvv) (synClnimagecrossfn)
      (synCcom (synCcross) (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv)))))
      p0028
  have p0030 :=
    @gMpbir (synWfn (synClnimagecrossfn) (synCvv))
      (synWfn (synCcom (synCcross)
          (synCtxp (synC2nd) (synCxp (synCvv) (synCsn (synCvv))))) (synCvv))
      p0027 p0029
  have p0031 :=
    @gPm32i (synWfn (synC1st) (synCvv)) (synWfn (synClnimagecrossfn) (synCvv))
      p0003 p0030
  have p0032 := @gFntxp (synCvv) (synCvv) (synC1st) (synClnimagecrossfn)
  have p0033 := Nominal.mp p0031 p0032
  have p0035 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synC1st) (synClnimagecrossfn)) p0008
  have p0036 :=
    @gMpbi
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synC1st) (synClnimagecrossfn)) (synCvv)) p0033 p0035
  have p0037 :=
    @gFncovv (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)) p0014 p0036
  have p0038 := (Nominal.classEqRefl (synClnimageresfn))
  have p0039 :=
    @gFneq1i (synCvv) (synClnimageresfn)
      (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn))) p0038
  have p0040 :=
    @gMpbir (synWfn (synClnimageresfn) (synCvv))
      (synWfn (synCcom (synClninterop) (synCtxp (synC1st) (synClnimagecrossfn)))
        (synCvv))
      p0037 p0039
  have p0041 := @gOpex R B hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0042 :=
    @gPm32i (synWfn (synClnimageresfn) (synCvv)) (.classMem (synCop R B) (synCvv))
      p0040 p0041
  have p0043 := @gFvco2 (synCvv) (synCop R B) (synCranfn) (synClnimageresfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0045 :=
    @gEqtri (synCfv (synClnimageop) (synCop R B))
      (synCfv (synCcom (synCranfn) (synClnimageresfn)) (synCop R B))
      (synCfv (synCranfn) (synCfv (synClnimageresfn) (synCop R B))) p0001 p0044
  have p0046 := @gLnimageresfnval B R hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0047 :=
    @gFveq2i (synCfv (synClnimageresfn) (synCop R B)) (synCres R B) (synCranfn)
      p0046
  have p0048 :=
    @gEqtri (synCfv (synClnimageop) (synCop R B))
      (synCfv (synCranfn) (synCfv (synClnimageresfn) (synCop R B)))
      (synCfv (synCranfn) (synCres R B)) p0045 p0047
  have p0049 := @gResex R B hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0050 := @gFvranfn (synCres R B) (synCvv)
  have p0051 := Nominal.mp p0049 p0050
  have p0052 :=
    @gEqtri (synCfv (synClnimageop) (synCop R B))
      (synCfv (synCranfn) (synCres R B)) (synCrn (synCres R B)) p0048 p0051
  have p0053 := @gDfima3 R B
  have p0054 := @gEqcomi (synCima R B) (synCrn (synCres R B)) p0053
  have p0055 :=
    @gEqtri (synCfv (synClnimageop) (synCop R B)) (synCrn (synCres R B))
      (synCima R B) p0052 p0054
  exact p0055

/-- Checked nominal proof certificate identified upstream as `g_lnpwcnvkerfnval`. -/
@[expose]
noncomputable def gLnpwcnvkerfnval (D : Class) (R : Class)
    (hyp_lnpwcnvkerfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwcnvkerfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwcnvkerfn) (synCop R D)) (synCcnv (synClnker R))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwcnvkerfn))
  have p0001 :=
    @gFveq1i (synCop R D) (synClnpwcnvkerfn)
      (synCcom (synCimage (synCswap)) (synClnpwkerfn)) p0000
  have p0002 := @gLnpwkerfnfn
  have p0003 := @gOpex R D hyp_lnpwcnvkerfnval_1 hyp_lnpwcnvkerfnval_2
  have p0004 :=
    @gPm32i (synWfn (synClnpwkerfn) (synCvv)) (.classMem (synCop R D) (synCvv))
      p0002 p0003
  have p0005 := @gFvco2 (synCvv) (synCop R D) (synCimage (synCswap)) (synClnpwkerfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gEqtri (synCfv (synClnpwcnvkerfn) (synCop R D))
      (synCfv (synCcom (synCimage (synCswap)) (synClnpwkerfn)) (synCop R D))
      (synCfv (synCimage (synCswap)) (synCfv (synClnpwkerfn) (synCop R D))) p0001
      p0006
  have p0008 := @gLnpwkerfnval D R hyp_lnpwcnvkerfnval_1 hyp_lnpwcnvkerfnval_2
  have p0009 :=
    @gFveq2i (synCfv (synClnpwkerfn) (synCop R D)) (synClnker R)
      (synCimage (synCswap)) p0008
  have p0010 :=
    @gEqtri (synCfv (synClnpwcnvkerfn) (synCop R D))
      (synCfv (synCimage (synCswap)) (synCfv (synClnpwkerfn) (synCop R D)))
      (synCfv (synCimage (synCswap)) (synClnker R)) p0007 p0009
  have p0011 := @gSwapex
  have p0012 := @gLnkerex R hyp_lnpwcnvkerfnval_1
  have p0013 := @gFvimagecl (synClnker R) (synCswap) p0011 p0012
  have p0014 := @gDfcnv2 (synClnker R)
  have p0015 :=
    @gEqcomi (synCcnv (synClnker R)) (synCima (synCswap) (synClnker R)) p0014
  have p0016 :=
    @gEqtri (synCfv (synCimage (synCswap)) (synClnker R))
      (synCima (synCswap) (synClnker R)) (synCcnv (synClnker R)) p0013 p0015
  have p0017 :=
    @gEqtri (synCfv (synClnpwcnvkerfn) (synCop R D))
      (synCfv (synCimage (synCswap)) (synClnker R)) (synCcnv (synClnker R)) p0010
      p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_lnpwclasspairfnval`. -/
@[expose]
noncomputable def gLnpwclasspairfnval (D : Class) (R : Class) (S : Class)
    (hyp_lnpwclasspairfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwclasspairfnval_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_lnpwclasspairfnval_3 : Nominal.NPrf (.classMem S (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwclasspairfn) (synCop (synCop R D) S))
        (synCop (synCcnv (synClnker R)) S)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwclasspairfn))
  have p0001 :=
    @gFveq1i (synCop (synCop R D) S) (synClnpwclasspairfn)
      (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) p0000
  have p0002 := @gImageswapfn
  have p0003 := @gLnpwkerfnfn
  have p0004 := @gFncovv (synCimage (synCswap)) (synClnpwkerfn) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synClnpwcnvkerfn))
  have p0006 :=
    @gFneq1i (synCvv) (synClnpwcnvkerfn)
      (synCcom (synCimage (synCswap)) (synClnpwkerfn)) p0005
  have p0007 :=
    @gMpbir (synWfn (synClnpwcnvkerfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synClnpwkerfn)) (synCvv)) p0004 p0006
  have p0008 := @gLn1stfn
  have p0009 := @gFncovv (synClnpwcnvkerfn) (synC1st) p0007 p0008
  have p0010 := @gLn2ndfn
  have p0011 := @gOpex R D hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0012 := @gOpex (synCop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0013 :=
    @gFvtxpvv (synCop (synCop R D) S) (synCcom (synClnpwcnvkerfn) (synC1st))
      (synC2nd) p0009 p0010 p0012
  have p0017 :=
    @gPm32i (synWfn (synC1st) (synCvv))
      (.classMem (synCop (synCop R D) S) (synCvv)) p0008 p0012
  have p0018 :=
    @gFvco2 (synCvv) (synCop (synCop R D) S) (synClnpwcnvkerfn) (synC1st)
  have p0019 := Nominal.mp p0017 p0018
  have p0021 := @gOpfv1st (synCop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0022 :=
    @gFveq2i (synCfv (synC1st) (synCop (synCop R D) S)) (synCop R D)
      (synClnpwcnvkerfn) p0021
  have p0023 :=
    @gEqtri (synCfv (synCcom (synClnpwcnvkerfn) (synC1st)) (synCop (synCop R D) S))
      (synCfv (synClnpwcnvkerfn) (synCfv (synC1st) (synCop (synCop R D) S)))
      (synCfv (synClnpwcnvkerfn) (synCop R D)) p0019 p0022
  have p0024 := @gLnpwcnvkerfnval D R hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0025 :=
    @gEqtri (synCfv (synCcom (synClnpwcnvkerfn) (synC1st)) (synCop (synCop R D) S))
      (synCfv (synClnpwcnvkerfn) (synCop R D)) (synCcnv (synClnker R)) p0023 p0024
  have p0027 := @gOpfv2nd (synCop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0028 :=
    @gOpeq12i
      (synCfv (synCcom (synClnpwcnvkerfn) (synC1st)) (synCop (synCop R D) S))
      (synCcnv (synClnker R)) (synCfv (synC2nd) (synCop (synCop R D) S)) S p0025
      p0027
  have p0029 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd))
        (synCop (synCop R D) S))
      (synCop (synCfv (synCcom (synClnpwcnvkerfn) (synC1st)) (synCop (synCop R D) S))
        (synCfv (synC2nd) (synCop (synCop R D) S)))
      (synCop (synCcnv (synClnker R)) S) p0013 p0028
  have p0030 :=
    @gEqtri (synCfv (synClnpwclasspairfn) (synCop (synCop R D) S))
      (synCfv (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd))
        (synCop (synCop R D) S))
      (synCop (synCcnv (synClnker R)) S) p0001 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_lnpwclassfnfn`. -/
@[expose]
noncomputable def gLnpwclassfnfn : Nominal.NPrf (synWfn (synClnpwclassfn) (synCvv)) :=
  by
  have p0000 := @gLnimageopfn
  have p0001 := @gImageswapfn
  have p0002 := @gLnpwkerfnfn
  have p0003 := @gFncovv (synCimage (synCswap)) (synClnpwkerfn) p0001 p0002
  have p0004 := (Nominal.classEqRefl (synClnpwcnvkerfn))
  have p0005 :=
    @gFneq1i (synCvv) (synClnpwcnvkerfn)
      (synCcom (synCimage (synCswap)) (synClnpwkerfn)) p0004
  have p0006 :=
    @gMpbir (synWfn (synClnpwcnvkerfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synClnpwkerfn)) (synCvv)) p0003 p0005
  have p0007 := @gLn1stfn
  have p0008 := @gFncovv (synClnpwcnvkerfn) (synC1st) p0006 p0007
  have p0009 := @gLn2ndfn
  have p0010 :=
    @gPm32i (synWfn (synCcom (synClnpwcnvkerfn) (synC1st)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0008 p0009
  have p0011 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gInidm (synCvv)
  have p0014 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) p0013
  have p0015 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) (synCvv))
      p0012 p0014
  have p0016 := (Nominal.classEqRefl (synClnpwclasspairfn))
  have p0017 :=
    @gFneq1i (synCvv) (synClnpwclasspairfn)
      (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) p0016
  have p0018 :=
    @gMpbir (synWfn (synClnpwclasspairfn) (synCvv))
      (synWfn (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) (synCvv))
      p0015 p0017
  have p0019 := @gFncovv (synClnimageop) (synClnpwclasspairfn) p0000 p0018
  have p0020 := (Nominal.classEqRefl (synClnpwclassfn))
  have p0021 :=
    @gFneq1i (synCvv) (synClnpwclassfn)
      (synCcom (synClnimageop) (synClnpwclasspairfn)) p0020
  have p0022 :=
    @gMpbir (synWfn (synClnpwclassfn) (synCvv))
      (synWfn (synCcom (synClnimageop) (synClnpwclasspairfn)) (synCvv)) p0019 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_lnpwclassfnex`. -/
@[expose]
noncomputable def gLnpwclassfnex :
    Nominal.NPrf (.classMem (synClnpwclassfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwclassfn))
  have p0001 := @gLnimageopex
  have p0002 := (Nominal.classEqRefl (synClnpwclasspairfn))
  have p0003 := (Nominal.classEqRefl (synClnpwcnvkerfn))
  have p0004 := @gSwapex
  have p0005 := @gImageex (synCswap) p0004
  have p0006 := @gLnpwkerfnex
  have p0007 := @gCoex (synCimage (synCswap)) (synClnpwkerfn) p0005 p0006
  have p0008 :=
    @gEqeltri (synClnpwcnvkerfn) (synCcom (synCimage (synCswap)) (synClnpwkerfn))
      (synCvv) p0003 p0007
  have p0009 := @gN1stex
  have p0010 := @gCoex (synClnpwcnvkerfn) (synC1st) p0008 p0009
  have p0011 := @gN2ndex
  have p0012 := @gTxpex (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd) p0010 p0011
  have p0013 :=
    @gEqeltri (synClnpwclasspairfn)
      (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) (synCvv) p0002
      p0012
  have p0014 := @gCoex (synClnimageop) (synClnpwclasspairfn) p0001 p0013
  have p0015 :=
    @gEqeltri (synClnpwclassfn) (synCcom (synClnimageop) (synClnpwclasspairfn))
      (synCvv) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_lnpwclassfnval`. -/
@[expose]
noncomputable def gLnpwclassfnval (D : Class) (R : Class) (S : Class)
    (hyp_lnpwclassfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwclassfnval_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_lnpwclassfnval_3 : Nominal.NPrf (.classMem S (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) S))
        (synCima (synCcnv (synClnker R)) S)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwclassfn))
  have p0001 :=
    @gFveq1i (synCop (synCop R D) S) (synClnpwclassfn)
      (synCcom (synClnimageop) (synClnpwclasspairfn)) p0000
  have p0002 := @gImageswapfn
  have p0003 := @gLnpwkerfnfn
  have p0004 := @gFncovv (synCimage (synCswap)) (synClnpwkerfn) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synClnpwcnvkerfn))
  have p0006 :=
    @gFneq1i (synCvv) (synClnpwcnvkerfn)
      (synCcom (synCimage (synCswap)) (synClnpwkerfn)) p0005
  have p0007 :=
    @gMpbir (synWfn (synClnpwcnvkerfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synClnpwkerfn)) (synCvv)) p0004 p0006
  have p0008 := @gLn1stfn
  have p0009 := @gFncovv (synClnpwcnvkerfn) (synC1st) p0007 p0008
  have p0010 := @gLn2ndfn
  have p0011 :=
    @gPm32i (synWfn (synCcom (synClnpwcnvkerfn) (synC1st)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0009 p0010
  have p0012 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gInidm (synCvv)
  have p0015 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) p0014
  have p0016 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) (synCvv))
      p0013 p0015
  have p0017 := (Nominal.classEqRefl (synClnpwclasspairfn))
  have p0018 :=
    @gFneq1i (synCvv) (synClnpwclasspairfn)
      (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) p0017
  have p0019 :=
    @gMpbir (synWfn (synClnpwclasspairfn) (synCvv))
      (synWfn (synCtxp (synCcom (synClnpwcnvkerfn) (synC1st)) (synC2nd)) (synCvv))
      p0016 p0018
  have p0020 := @gOpex R D hyp_lnpwclassfnval_1 hyp_lnpwclassfnval_2
  have p0021 := @gOpex (synCop R D) S p0020 hyp_lnpwclassfnval_3
  have p0022 :=
    @gPm32i (synWfn (synClnpwclasspairfn) (synCvv))
      (.classMem (synCop (synCop R D) S) (synCvv)) p0019 p0021
  have p0023 :=
    @gFvco2 (synCvv) (synCop (synCop R D) S) (synClnimageop) (synClnpwclasspairfn)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gEqtri (synCfv (synClnpwclassfn) (synCop (synCop R D) S))
      (synCfv (synCcom (synClnimageop) (synClnpwclasspairfn)) (synCop (synCop R D) S))
      (synCfv (synClnimageop) (synCfv (synClnpwclasspairfn) (synCop (synCop R D) S)))
      p0001 p0024
  have p0026 :=
    @gLnpwclasspairfnval D R S hyp_lnpwclassfnval_1 hyp_lnpwclassfnval_2
      hyp_lnpwclassfnval_3
  have p0027 :=
    @gFveq2i (synCfv (synClnpwclasspairfn) (synCop (synCop R D) S))
      (synCop (synCcnv (synClnker R)) S) (synClnimageop) p0026
  have p0028 :=
    @gEqtri (synCfv (synClnpwclassfn) (synCop (synCop R D) S))
      (synCfv (synClnimageop) (synCfv (synClnpwclasspairfn) (synCop (synCop R D) S)))
      (synCfv (synClnimageop) (synCop (synCcnv (synClnker R)) S)) p0025 p0027
  have p0029 := @gLnkerex R hyp_lnpwclassfnval_1
  have p0030 := @gCnvex (synClnker R) p0029
  have p0031 := @gLnimageopval S (synCcnv (synClnker R)) p0030 hyp_lnpwclassfnval_3
  have p0032 :=
    @gEqtri (synCfv (synClnpwclassfn) (synCop (synCop R D) S))
      (synCfv (synClnimageop) (synCop (synCcnv (synClnker R)) S))
      (synCima (synCcnv (synClnker R)) S) p0028 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_lnpwpw1secondfnfn`. -/
@[expose]
noncomputable def gLnpwpw1secondfnfn :
    Nominal.NPrf (synWfn (synClnpwpw1secondfn) (synCvv)) :=
  by
  have p0000 := @gFnfullfun (synCpw1fn)
  have p0001 := @gN2ndex
  have p0002 := @gWppimagefn (synC2nd) p0001
  have p0003 := @gFncovv (synCfullfun (synCpw1fn)) (synCimage (synC2nd)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (synClnpwpw1secondfn))
  have p0005 :=
    @gFneq1i (synCvv) (synClnpwpw1secondfn)
      (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) p0004
  have p0006 :=
    @gMpbir (synWfn (synClnpwpw1secondfn) (synCvv))
      (synWfn (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) (synCvv))
      p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lnpwpw1secondfnex`. -/
@[expose]
noncomputable def gLnpwpw1secondfnex :
    Nominal.NPrf (.classMem (synClnpwpw1secondfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwpw1secondfn))
  have p0001 := @gPw1fnex
  have p0002 := @gFullfunex (synCpw1fn) p0001
  have p0003 := @gN2ndex
  have p0004 := @gImageex (synC2nd) p0003
  have p0005 := @gCoex (synCfullfun (synCpw1fn)) (synCimage (synC2nd)) p0002 p0004
  have p0006 :=
    @gEqeltri (synClnpwpw1secondfn)
      (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lnpwpw1secondfnval`. -/
@[expose]
noncomputable def gLnpwpw1secondfnval (D : Class) (R : Class)
    (hyp_lnpwpw1secondfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwpw1secondfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))) (synCpw1 D)) :=
  by
  have dv_cache_0001 : Disjoint ((synCsn (synCop R D))).fv ((synC2nd)).fv := by
    exact
      (show Disjoint ((synCsn (synCop R D))).fv ((synC2nd)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
          exact (show Disjoint (((synCop R D)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (synClnpwpw1secondfn))
  have p0001 :=
    @gFveq1i (synCsn (synCop R D)) (synClnpwpw1secondfn)
      (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) p0000
  have p0002 := @gN2ndex
  have p0003 := @gWppimagefn (synC2nd) p0002
  have p0004 := @gSnex (synCop R D)
  have p0005 :=
    @gPm32i (synWfn (synCimage (synC2nd)) (synCvv))
      (.classMem (synCsn (synCop R D)) (synCvv)) p0003 p0004
  have p0006 :=
    @gFvco2 (synCvv) (synCsn (synCop R D)) (synCfullfun (synCpw1fn))
      (synCimage (synC2nd))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gEqtri (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D)))
      (synCfv (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd)))
        (synCsn (synCop R D)))
      (synCfv (synCfullfun (synCpw1fn))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop R D))))
      p0001 p0007
  have p0011 := @gWppfvimage (synCsn (synCop R D)) (synC2nd) dv_cache_0001 p0002 p0004
  have p0012 := @gLn2ndfn
  have p0013 := @gOpex R D hyp_lnpwpw1secondfnval_1 hyp_lnpwpw1secondfnval_2
  have p0014 :=
    @gPm32i (synWfn (synC2nd) (synCvv)) (.classMem (synCop R D) (synCvv)) p0012
      p0013
  have p0015 := @gFnsnfv (synCvv) (synCop R D) (synC2nd)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gEqcomi (synCsn (synCfv (synC2nd) (synCop R D)))
      (synCima (synC2nd) (synCsn (synCop R D))) p0016
  have p0018 := @gOpfv2nd R D hyp_lnpwpw1secondfnval_1 hyp_lnpwpw1secondfnval_2
  have p0019 := @gSneqi (synCfv (synC2nd) (synCop R D)) D p0018
  have p0020 :=
    @gEqtri (synCima (synC2nd) (synCsn (synCop R D)))
      (synCsn (synCfv (synC2nd) (synCop R D))) (synCsn D) p0017 p0019
  have p0021 :=
    @gEqtri (synCfv (synCimage (synC2nd)) (synCsn (synCop R D)))
      (synCima (synC2nd) (synCsn (synCop R D))) (synCsn D) p0011 p0020
  have p0022 :=
    @gFveq2i (synCfv (synCimage (synC2nd)) (synCsn (synCop R D))) (synCsn D)
      (synCfullfun (synCpw1fn)) p0021
  have p0023 :=
    @gEqtri (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D)))
      (synCfv (synCfullfun (synCpw1fn))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop R D))))
      (synCfv (synCfullfun (synCpw1fn)) (synCsn D)) p0008 p0022
  have p0024 := @gFvfullfun (synCsn D) (synCpw1fn)
  have p0025 :=
    @gEqtri (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D)))
      (synCfv (synCfullfun (synCpw1fn)) (synCsn D)) (synCfv (synCpw1fn) (synCsn D))
      p0023 p0024
  have p0026 := @gPw1fnval D hyp_lnpwpw1secondfnval_2
  have p0027 :=
    @gEqtri (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D)))
      (synCfv (synCpw1fn) (synCsn D)) (synCpw1 D) p0025 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_lnpwquoinputfnfn`. -/
@[expose]
noncomputable def gLnpwquoinputfnfn :
    Nominal.NPrf (synWfn (synClnpwquoinputfn) (synCvv)) :=
  by
  have p0000 := @gFncross
  have p0001 := @gFnresi (synCvv)
  have p0002 := @gResid (synCid)
  have p0003 := @gFneq1i (synCvv) (synCres (synCid) (synCvv)) (synCid) p0002
  have p0004 :=
    @gMpbi (synWfn (synCres (synCid) (synCvv)) (synCvv))
      (synWfn (synCid) (synCvv)) p0001 p0003
  have p0005 := @gFnfullfun (synCpw1fn)
  have p0006 := @gN2ndex
  have p0007 := @gWppimagefn (synC2nd) p0006
  have p0008 := @gFncovv (synCfullfun (synCpw1fn)) (synCimage (synC2nd)) p0005 p0007
  have p0009 := (Nominal.classEqRefl (synClnpwpw1secondfn))
  have p0010 :=
    @gFneq1i (synCvv) (synClnpwpw1secondfn)
      (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) p0009
  have p0011 :=
    @gMpbir (synWfn (synClnpwpw1secondfn) (synCvv))
      (synWfn (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) (synCvv))
      p0008 p0010
  have p0012 :=
    @gPm32i (synWfn (synCid) (synCvv)) (synWfn (synClnpwpw1secondfn) (synCvv))
      p0004 p0011
  have p0013 := @gFntxp (synCvv) (synCvv) (synCid) (synClnpwpw1secondfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @gInidm (synCvv)
  have p0016 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCid) (synClnpwpw1secondfn)) p0015
  have p0017 :=
    @gMpbi
      (synWfn (synCtxp (synCid) (synClnpwpw1secondfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synClnpwpw1secondfn)) (synCvv)) p0014 p0016
  have p0018 :=
    @gFncovv (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn)) p0000 p0017
  have p0019 := (Nominal.classEqRefl (synClnpwquoinputfn))
  have p0020 :=
    @gFneq1i (synCvv) (synClnpwquoinputfn)
      (synCcom (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn))) p0019
  have p0021 :=
    @gMpbir (synWfn (synClnpwquoinputfn) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn))) (synCvv))
      p0018 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_lnpwquoinputfnex`. -/
@[expose]
noncomputable def gLnpwquoinputfnex :
    Nominal.NPrf (.classMem (synClnpwquoinputfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwquoinputfn))
  have p0001 := @gCrossex
  have p0002 := @gIdex
  have p0003 := (Nominal.classEqRefl (synClnpwpw1secondfn))
  have p0004 := @gPw1fnex
  have p0005 := @gFullfunex (synCpw1fn) p0004
  have p0006 := @gN2ndex
  have p0007 := @gImageex (synC2nd) p0006
  have p0008 := @gCoex (synCfullfun (synCpw1fn)) (synCimage (synC2nd)) p0005 p0007
  have p0009 :=
    @gEqeltri (synClnpwpw1secondfn)
      (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) (synCvv) p0003 p0008
  have p0010 := @gTxpex (synCid) (synClnpwpw1secondfn) p0002 p0009
  have p0011 :=
    @gCoex (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn)) p0001 p0010
  have p0012 :=
    @gEqeltri (synClnpwquoinputfn)
      (synCcom (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn))) (synCvv) p0000
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lnpwquoinputfnval`. -/
@[expose]
noncomputable def gLnpwquoinputfnval (D : Class) (R : Class)
    (hyp_lnpwquoinputfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwquoinputfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
        (synCxp (synCsn (synCop R D)) (synCpw1 D))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwquoinputfn))
  have p0001 :=
    @gFveq1i (synCsn (synCop R D)) (synClnpwquoinputfn)
      (synCcom (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn))) p0000
  have p0002 := @gFnresi (synCvv)
  have p0003 := @gResid (synCid)
  have p0004 := @gFneq1i (synCvv) (synCres (synCid) (synCvv)) (synCid) p0003
  have p0005 :=
    @gMpbi (synWfn (synCres (synCid) (synCvv)) (synCvv))
      (synWfn (synCid) (synCvv)) p0002 p0004
  have p0006 := @gFnfullfun (synCpw1fn)
  have p0007 := @gN2ndex
  have p0008 := @gWppimagefn (synC2nd) p0007
  have p0009 := @gFncovv (synCfullfun (synCpw1fn)) (synCimage (synC2nd)) p0006 p0008
  have p0010 := (Nominal.classEqRefl (synClnpwpw1secondfn))
  have p0011 :=
    @gFneq1i (synCvv) (synClnpwpw1secondfn)
      (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) p0010
  have p0012 :=
    @gMpbir (synWfn (synClnpwpw1secondfn) (synCvv))
      (synWfn (synCcom (synCfullfun (synCpw1fn)) (synCimage (synC2nd))) (synCvv))
      p0009 p0011
  have p0013 :=
    @gPm32i (synWfn (synCid) (synCvv)) (synWfn (synClnpwpw1secondfn) (synCvv))
      p0005 p0012
  have p0014 := @gFntxp (synCvv) (synCvv) (synCid) (synClnpwpw1secondfn)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gInidm (synCvv)
  have p0017 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCid) (synClnpwpw1secondfn)) p0016
  have p0018 :=
    @gMpbi
      (synWfn (synCtxp (synCid) (synClnpwpw1secondfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCid) (synClnpwpw1secondfn)) (synCvv)) p0015 p0017
  have p0019 := @gSnex (synCop R D)
  have p0020 :=
    @gPm32i (synWfn (synCtxp (synCid) (synClnpwpw1secondfn)) (synCvv))
      (.classMem (synCsn (synCop R D)) (synCvv)) p0018 p0019
  have p0021 :=
    @gFvco2 (synCvv) (synCsn (synCop R D)) (synCcross)
      (synCtxp (synCid) (synClnpwpw1secondfn))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 :=
    @gEqtri (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
      (synCfv (synCcom (synCcross) (synCtxp (synCid) (synClnpwpw1secondfn)))
        (synCsn (synCop R D)))
      (synCfv (synCcross)
        (synCfv (synCtxp (synCid) (synClnpwpw1secondfn)) (synCsn (synCop R D))))
      p0001 p0022
  have p0036 :=
    @gFvtxpvv (synCsn (synCop R D)) (synCid) (synClnpwpw1secondfn) p0005 p0012 p0019
  have p0038 := @gFvi (synCsn (synCop R D)) (synCvv)
  have p0039 := Nominal.mp p0019 p0038
  have p0040 := @gLnpwpw1secondfnval D R hyp_lnpwquoinputfnval_1 hyp_lnpwquoinputfnval_2
  have p0041 :=
    @gOpeq12i (synCfv (synCid) (synCsn (synCop R D))) (synCsn (synCop R D))
      (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))) (synCpw1 D) p0039 p0040
  have p0042 :=
    @gEqtri (synCfv (synCtxp (synCid) (synClnpwpw1secondfn)) (synCsn (synCop R D)))
      (synCop (synCfv (synCid) (synCsn (synCop R D)))
        (synCfv (synClnpwpw1secondfn) (synCsn (synCop R D))))
      (synCop (synCsn (synCop R D)) (synCpw1 D)) p0036 p0041
  have p0043 :=
    @gFveq2i
      (synCfv (synCtxp (synCid) (synClnpwpw1secondfn)) (synCsn (synCop R D)))
      (synCop (synCsn (synCop R D)) (synCpw1 D)) (synCcross) p0042
  have p0044 :=
    @gEqtri (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
      (synCfv (synCcross)
        (synCfv (synCtxp (synCid) (synClnpwpw1secondfn)) (synCsn (synCop R D))))
      (synCfv (synCcross) (synCop (synCsn (synCop R D)) (synCpw1 D))) p0023 p0043
  have p0045 :=
    (Nominal.classEqRefl (synCo (synCsn (synCop R D)) (synCcross) (synCpw1 D)))
  have p0046 :=
    @gEqcomi (synCo (synCsn (synCop R D)) (synCcross) (synCpw1 D))
      (synCfv (synCcross) (synCop (synCsn (synCop R D)) (synCpw1 D))) p0045
  have p0048 := @gPw1ex D hyp_lnpwquoinputfnval_2
  have p0049 :=
    @gPm32i (.classMem (synCsn (synCop R D)) (synCvv))
      (.classMem (synCpw1 D) (synCvv)) p0019 p0048
  have p0050 := @gOvcross (synCsn (synCop R D)) (synCpw1 D) (synCvv) (synCvv)
  have p0051 := Nominal.mp p0049 p0050
  have p0052 :=
    @gEqtri (synCfv (synCcross) (synCop (synCsn (synCop R D)) (synCpw1 D)))
      (synCo (synCsn (synCop R D)) (synCcross) (synCpw1 D))
      (synCxp (synCsn (synCop R D)) (synCpw1 D)) p0046 p0051
  have p0053 :=
    @gEqtri (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
      (synCfv (synCcross) (synCop (synCsn (synCop R D)) (synCpw1 D)))
      (synCxp (synCsn (synCop R D)) (synCpw1 D)) p0044 p0052
  exact p0053

/-- Checked nominal proof certificate identified upstream as `g_lnpwquofnfn`. -/
@[expose]
noncomputable def gLnpwquofnfn : Nominal.NPrf (synWfn (synClnpwquofn) (synCvv)) :=
  by
  have p0000 := @gLnpwclassfnex
  have p0001 := @gWppimagefn (synClnpwclassfn) p0000
  have p0002 := @gLnpwquoinputfnfn
  have p0003 :=
    @gFncovv (synCimage (synClnpwclassfn)) (synClnpwquoinputfn) p0001 p0002
  have p0004 := (Nominal.classEqRefl (synClnpwquofn))
  have p0005 :=
    @gFneq1i (synCvv) (synClnpwquofn)
      (synCcom (synCimage (synClnpwclassfn)) (synClnpwquoinputfn)) p0004
  have p0006 :=
    @gMpbir (synWfn (synClnpwquofn) (synCvv))
      (synWfn (synCcom (synCimage (synClnpwclassfn)) (synClnpwquoinputfn)) (synCvv))
      p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lnpwquofnex`. -/
@[expose]
noncomputable def gLnpwquofnex : Nominal.NPrf (.classMem (synClnpwquofn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwquofn))
  have p0001 := @gLnpwclassfnex
  have p0002 := @gImageex (synClnpwclassfn) p0001
  have p0003 := @gLnpwquoinputfnex
  have p0004 := @gCoex (synCimage (synClnpwclassfn)) (synClnpwquoinputfn) p0002 p0003
  have p0005 :=
    @gEqeltri (synClnpwquofn)
      (synCcom (synCimage (synClnpwclassfn)) (synClnpwquoinputfn)) (synCvv) p0000
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_lnpwquofnrawval`. -/
@[expose]
noncomputable def gLnpwquofnrawval (D : Class) (R : Class)
    (hyp_lnpwquofnrawval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwquofnrawval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwquofn) (synCsn (synCop R D)))
        (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwquofn))
  have p0001 :=
    @gFveq1i (synCsn (synCop R D)) (synClnpwquofn)
      (synCcom (synCimage (synClnpwclassfn)) (synClnpwquoinputfn)) p0000
  have p0002 := @gLnpwquoinputfnfn
  have p0003 := @gSnex (synCop R D)
  have p0004 :=
    @gPm32i (synWfn (synClnpwquoinputfn) (synCvv))
      (.classMem (synCsn (synCop R D)) (synCvv)) p0002 p0003
  have p0005 :=
    @gFvco2 (synCvv) (synCsn (synCop R D)) (synCimage (synClnpwclassfn))
      (synClnpwquoinputfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gEqtri (synCfv (synClnpwquofn) (synCsn (synCop R D)))
      (synCfv (synCcom (synCimage (synClnpwclassfn)) (synClnpwquoinputfn))
        (synCsn (synCop R D)))
      (synCfv (synCimage (synClnpwclassfn))
        (synCfv (synClnpwquoinputfn) (synCsn (synCop R D))))
      p0001 p0006
  have p0008 := @gLnpwquoinputfnval D R hyp_lnpwquofnrawval_1 hyp_lnpwquofnrawval_2
  have p0009 :=
    @gFveq2i (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
      (synCxp (synCsn (synCop R D)) (synCpw1 D)) (synCimage (synClnpwclassfn)) p0008
  have p0010 :=
    @gEqtri (synCfv (synClnpwquofn) (synCsn (synCop R D)))
      (synCfv (synCimage (synClnpwclassfn))
        (synCfv (synClnpwquoinputfn) (synCsn (synCop R D))))
      (synCfv (synCimage (synClnpwclassfn)) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      p0007 p0009
  have p0011 := @gLnpwclassfnex
  have p0013 := @gPw1ex D hyp_lnpwquofnrawval_2
  have p0014 := @gXpex (synCsn (synCop R D)) (synCpw1 D) p0003 p0013
  have p0015 :=
    @gFvimagecl (synCxp (synCsn (synCop R D)) (synCpw1 D)) (synClnpwclassfn) p0011
      p0014
  have p0016 :=
    @gEqtri (synCfv (synClnpwquofn) (synCsn (synCop R D)))
      (synCfv (synCimage (synClnpwclassfn)) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))) p0010
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_lnpwclassfnsnval`. -/
@[expose]
noncomputable def gLnpwclassfnsnval (D : Class) (R : Class) (X : Class)
    (hyp_lnpwclassfnsnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwclassfnsnval_2 : Nominal.NPrf (.classMem D (synCvv)))
    (_hyp_lnpwclassfnsnval_3 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn X)))
        (synCec X (synClnker R))) :=
  by
  have p0000 := @gSnex X
  have p0001 :=
    @gLnpwclassfnval D R (synCsn X) hyp_lnpwclassfnsnval_1 hyp_lnpwclassfnsnval_2 p0000
  have p0002 := (Nominal.classEqRefl (synClnker R))
  have p0003 := @gCnveqi (synClnker R) (synCin R (synCcnv R)) p0002
  have p0004 := @gCnvin R (synCcnv R)
  have p0005 := @gCnvcnv R
  have p0006 := @gIneq2i (synCcnv (synCcnv R)) R (synCcnv R) p0005
  have p0007 :=
    @gEqtri (synCcnv (synCin R (synCcnv R)))
      (synCin (synCcnv R) (synCcnv (synCcnv R))) (synCin (synCcnv R) R) p0004 p0006
  have p0008 :=
    @gEqtri (synCcnv (synClnker R)) (synCcnv (synCin R (synCcnv R)))
      (synCin (synCcnv R) R) p0003 p0007
  have p0009 := @gIncom (synCcnv R) R
  have p0010 :=
    @gEqtri (synCcnv (synClnker R)) (synCin (synCcnv R) R) (synCin R (synCcnv R))
      p0008 p0009
  have p0012 := @gEqcomi (synClnker R) (synCin R (synCcnv R)) p0002
  have p0013 :=
    @gEqtri (synCcnv (synClnker R)) (synCin R (synCcnv R)) (synClnker R) p0010 p0012
  have p0014 := @gImaeq1i (synCcnv (synClnker R)) (synClnker R) (synCsn X) p0013
  have p0015 :=
    @gEqtri (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn X)))
      (synCima (synCcnv (synClnker R)) (synCsn X))
      (synCima (synClnker R) (synCsn X)) p0001 p0014
  have p0016 := (Nominal.classEqRefl (synCec X (synClnker R)))
  have p0017 :=
    @gEqcomi (synCec X (synClnker R)) (synCima (synClnker R) (synCsn X)) p0016
  have p0018 :=
    @gEqtri (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn X)))
      (synCima (synClnker R) (synCsn X)) (synCec X (synClnker R)) p0015 p0017
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

/-- Checked nominal proof certificate identified upstream as `g_lnpwquofnrawexact`. -/
@[expose]
noncomputable def gLnpwquofnrawexact (D : Class) (R : Class)
    (hyp_lnpwquofnrawexact_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwquofnrawexact_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
        (synCqs D (synClnker R))) :=
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
  have dv_cache_0002 : z ∉ ((synCxp (synCsn (synCop R D)) (synCpw1 D))).fv :=
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
  have dv_cache_0003 : z ∉ ((synClnpwclassfn)).fv :=
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
  have dv_cache_0004 : z ∉ ((synCsn (synCop R D))).fv :=
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
  have dv_cache_0005 : p ∉ ((synCsn (synCop R D))).fv :=
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
  have dv_cache_0006 : s ∉ ((synCsn (synCop R D))).fv :=
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
  have dv_cache_0007 : z ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0008 : p ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0009 : s ∉ ((synCpw1 D)).fv :=
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
    p ∉ ((Wff.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c))).fv :=
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
    s ∉ ((Wff.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c))).fv :=
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
      ((Wff.classEq (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s))) (.cv c))).fv :=
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
  have dv_cache_0016 : s ∉ ((Wff.classEq (.cv p) (synCop R D))).fv :=
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
  have dv_cache_0017 : p ∉ ((synCop R D)).fv :=
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
      ((synWrex s (synCpw1 D)
          (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s)))
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
      ((Wff.imp (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
          (.classMem (.cv c) (synCqs D (synClnker R))))).fv :=
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
  have dv_cache_0022 : s ∉ ((Wff.classMem (.cv c) (synCqs D (synClnker R)))).fv :=
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
      ((synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))).fv :=
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
  have dv_cache_0024 : c ∉ ((synCqs D (synClnker R))).fv :=
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
  have dv_cache_0026 : x ∉ ((synClnker R)).fv :=
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
      ((Wff.classMem (.cv c) (synCima (synClnpwclassfn)
            (synCxp (synCsn (synCop R D)) (synCpw1 D))))).fv :=
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
  have p0000 := @gLnpwclassfnfn
  have p0001 := @gFnfun (synCvv) (synClnpwclassfn)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gFvelima z (.cv c) (synCxp (synCsn (synCop R D)) (synCpw1 D)) (synClnpwclassfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gMpan (synWfun (synClnpwclassfn))
      (.classMem (.cv c)
        (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))))
      (synWrex z (synCxp (synCsn (synCop R D)) (synCpw1 D))
        (.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c)))
      p0002 p0003
  have p0005 := @gId (.classEq (.cv z) (synCop (.cv p) (.cv s)))
  have p0006 :=
    @gFveq2d (.classEq (.cv z) (synCop (.cv p) (.cv s))) (.cv z)
      (synCop (.cv p) (.cv s)) (synClnpwclassfn) p0005
  have p0007 :=
    @gEqeq1d (.classEq (.cv z) (synCop (.cv p) (.cv s)))
      (synCfv (synClnpwclassfn) (.cv z))
      (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s))) (.cv c) p0006
  have p0008 :=
    @gRexxp (.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c))
      (.classEq (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s))) (.cv c)) z p s
      (synCsn (synCop R D)) (synCpw1 D) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 p0007
  have p0009 := @gOpex R D hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2
  have p0010 := @gId (.classEq (.cv p) (synCop R D))
  have p0011 :=
    @gOpeq1d (.classEq (.cv p) (synCop R D)) (.cv p) (synCop R D) (.cv s) p0010
  have p0012 :=
    @gFveq2d (.classEq (.cv p) (synCop R D)) (synCop (.cv p) (.cv s))
      (synCop (synCop R D) (.cv s)) (synClnpwclassfn) p0011
  have p0013 :=
    @gEqeq1d (.classEq (.cv p) (synCop R D))
      (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s)))
      (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c) p0012
  have p0014 :=
    @gRexbidv (.classEq (.cv p) (synCop R D))
      (.classEq (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s))) (.cv c))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)) s
      (synCpw1 D) dv_cache_0016 p0013
  have p0015 :=
    @gRexsn
      (synWrex s (synCpw1 D)
        (.classEq (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s))) (.cv c)))
      (synWrex s (synCpw1 D)
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      p (synCop R D) dv_cache_0017 dv_cache_0018 p0009 p0014
  have p0016 :=
    @gBitri
      (synWrex z (synCxp (synCsn (synCop R D)) (synCpw1 D))
        (.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c)))
      (synWrex p (synCsn (synCop R D)) (synWrex s (synCpw1 D)
          (.classEq (synCfv (synClnpwclassfn) (synCop (.cv p) (.cv s))) (.cv c))))
      (synWrex s (synCpw1 D)
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      p0008 p0015
  have p0017 := @gElpw1 x (.cv s) D dv_cache_0019 dv_cache_0020
  have p0018 :=
    @gN3simpc (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
  have p0019 :=
    @gSimpr (.classEq (.cv s) (synCsn (.cv x)))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
  have p0020 :=
    @gSyl
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (synWa (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
      p0018 p0019
  have p0021 :=
    @gEqcomd
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c) p0020
  have p0022 :=
    @gN3simpa (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
  have p0023 := @gSimpr (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
  have p0024 :=
    @gSyl
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (synWa (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x))))
      (.classEq (.cv s) (synCsn (.cv x))) p0022 p0023
  have p0025 := @gId (.classEq (.cv s) (synCsn (.cv x)))
  have p0026 :=
    @gOpeq2d (.classEq (.cv s) (synCsn (.cv x))) (.cv s) (synCsn (.cv x)) (synCop R D)
      p0025
  have p0027 :=
    @gFveq2d (.classEq (.cv s) (synCsn (.cv x))) (synCop (synCop R D) (.cv s))
      (synCop (synCop R D) (synCsn (.cv x))) (synClnpwclassfn) p0026
  have p0028 := @gVex x
  have p0029 :=
    @gLnpwclassfnsnval D R (.cv x) hyp_lnpwquofnrawexact_1 hyp_lnpwquofnrawexact_2 p0028
  have p0030 :=
    @gSyl6eq (.classEq (.cv s) (synCsn (.cv x)))
      (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s)))
      (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCec (.cv x) (synClnker R)) p0027 p0029
  have p0031 :=
    @gSyl
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (.classEq (.cv s) (synCsn (.cv x)))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s)))
        (synCec (.cv x) (synClnker R)))
      p0024 p0030
  have p0032 :=
    @gEqcomd
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s)))
      (synCec (.cv x) (synClnker R)) p0031
  have p0033 :=
    @gEqtr4d
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (.cv c) (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s)))
      (synCec (.cv x) (synClnker R)) p0021 p0032
  have p0035 := @gSimpl (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
  have p0036 :=
    @gSyl
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (synWa (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x))))
      (.classMem (.cv x) D) p0022 p0035
  have p0037 := @gLnkerex R hyp_lnpwquofnrawexact_1
  have p0038 := @gEcelqsi D (.cv x) (synClnker R) p0037
  have p0039 :=
    @gSyl
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (.classMem (.cv x) D)
      (.classMem (synCec (.cv x) (synClnker R)) (synCqs D (synClnker R))) p0036 p0038
  have p0040 :=
    @gEqeltrd
      (synW3a (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (.cv c) (synCec (.cv x) (synClnker R)) (synCqs D (synClnker R)) p0033 p0039
  have p0041 :=
    @gN3exp (.classMem (.cv x) D) (.classEq (.cv s) (synCsn (.cv x)))
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
      (.classMem (.cv c) (synCqs D (synClnker R))) p0040
  have p0042 :=
    @gRexlimiv (.classEq (.cv s) (synCsn (.cv x)))
      (.imp (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
        (.classMem (.cv c) (synCqs D (synClnker R))))
      x D dv_cache_0021 p0041
  have p0043 :=
    @gSylbi (.classMem (.cv s) (synCpw1 D))
      (synWrex x D (.classEq (.cv s) (synCsn (.cv x))))
      (.imp (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
        (.classMem (.cv c) (synCqs D (synClnker R))))
      p0017 p0042
  have p0044 :=
    @gRexlimiv
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c))
      (.classMem (.cv c) (synCqs D (synClnker R))) s (synCpw1 D) dv_cache_0022 p0043
  have p0045 :=
    @gSylbi
      (synWrex z (synCxp (synCsn (synCop R D)) (synCpw1 D))
        (.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c)))
      (synWrex s (synCpw1 D)
        (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (.cv s))) (.cv c)))
      (.classMem (.cv c) (synCqs D (synClnker R))) p0016 p0044
  have p0046 :=
    @gSyl
      (.classMem (.cv c)
        (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))))
      (synWrex z (synCxp (synCsn (synCop R D)) (synCpw1 D))
        (.classEq (synCfv (synClnpwclassfn) (.cv z)) (.cv c)))
      (.classMem (.cv c) (synCqs D (synClnker R))) p0004 p0045
  have p0047 :=
    @gSsriv c
      (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (synCqs D (synClnker R)) dv_cache_0023 dv_cache_0024 p0046
  have p0048 := @gEqid (synCqs D (synClnker R))
  have p0049 := @gId (.classEq (synCec (.cv x) (synClnker R)) (.cv c))
  have p0050 :=
    @gEleq1d (.classEq (synCec (.cv x) (synClnker R)) (.cv c))
      (synCec (.cv x) (synClnker R)) (.cv c)
      (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))) p0049
  have p0053 :=
    @gA1i
      (.classEq (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCec (.cv x) (synClnker R)))
      (.classMem (.cv x) D) p0029
  have p0055 := @gSnid (synCop R D) p0009
  have p0056 :=
    @gA1i (.classMem (synCop R D) (synCsn (synCop R D))) (.classMem (.cv x) D) p0055
  have p0057 := @gId (.classMem (.cv x) D)
  have p0058 := @gSnelpw1 (.cv x) D
  have p0059 :=
    @gSylibr (.classMem (.cv x) D) (.classMem (.cv x) D)
      (.classMem (synCsn (.cv x)) (synCpw1 D)) p0057 p0058
  have p0060 :=
    @gJca (.classMem (.cv x) D) (.classMem (synCop R D) (synCsn (synCop R D)))
      (.classMem (synCsn (.cv x)) (synCpw1 D)) p0056 p0059
  have p0061 :=
    @gOpelxp (synCop R D) (synCsn (.cv x)) (synCsn (synCop R D)) (synCpw1 D)
  have p0062 :=
    @gSylibr (.classMem (.cv x) D)
      (synWa (.classMem (synCop R D) (synCsn (synCop R D)))
        (.classMem (synCsn (.cv x)) (synCpw1 D)))
      (.classMem (synCop (synCop R D) (synCsn (.cv x)))
        (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      p0060 p0061
  have p0067 := @gSnex (.cv x)
  have p0068 := @gOpex (synCop R D) (synCsn (.cv x)) p0009 p0067
  have p0070 := @gFndm (synCvv) (synClnpwclassfn)
  have p0071 := Nominal.mp p0000 p0070
  have p0072 :=
    @gEleqtrri (synCop (synCop R D) (synCsn (.cv x))) (synCvv)
      (synCdm (synClnpwclassfn)) p0068 p0071
  have p0073 :=
    @gPm32i (synWfun (synClnpwclassfn))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCdm (synClnpwclassfn)))
      p0002 p0072
  have p0074 :=
    @gFunfvima (synCxp (synCsn (synCop R D)) (synCpw1 D))
      (synCop (synCop R D) (synCsn (.cv x))) (synClnpwclassfn)
  have p0075 := Nominal.mp p0073 p0074
  have p0076 :=
    @gSyl (.classMem (.cv x) D)
      (.classMem (synCop (synCop R D) (synCsn (.cv x)))
        (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (.classMem (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))))
      p0062 p0075
  have p0077 :=
    @gEqeltrrd (.classMem (.cv x) D)
      (synCfv (synClnpwclassfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCec (.cv x) (synClnker R))
      (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))) p0053
      p0076
  have p0078 :=
    @gEctocl
      (.classMem (synCec (.cv x) (synClnker R))
        (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))))
      (.classMem (.cv c)
        (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D))))
      x (.cv c) D (synClnker R) (synCqs D (synClnker R)) dv_cache_0025 dv_cache_0020
      dv_cache_0026 dv_cache_0027 p0048 p0050 p0077
  have p0079 :=
    @gSsriv c (synCqs D (synClnker R))
      (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      dv_cache_0024 dv_cache_0023 p0078
  have p0080 :=
    @gEqssi (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (synCqs D (synClnker R)) p0047 p0079
  exact p0080

/-- Checked nominal proof certificate identified upstream as `g_lnpwquofnval`. -/
@[expose]
noncomputable def gLnpwquofnval (D : Class) (R : Class)
    (hyp_lnpwquofnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwquofnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwquofn) (synCsn (synCop R D)))
        (synCqs D (synClnker R))) :=
  by
  have p0000 := @gLnpwquofnrawval D R hyp_lnpwquofnval_1 hyp_lnpwquofnval_2
  have p0001 := @gLnpwquofnrawexact D R hyp_lnpwquofnval_1 hyp_lnpwquofnval_2
  have p0002 :=
    @gEqtri (synCfv (synClnpwquofn) (synCsn (synCop R D)))
      (synCima (synClnpwclassfn) (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (synCqs D (synClnker R)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_lnpairraisefnfn`. -/
@[expose]
noncomputable def gLnpairraisefnfn :
    Nominal.NPrf (synWfn (synClnpairraisefn) (synCvv)) :=
  by
  have p0000 := @gN1stex
  have p0001 := @gWppimagefn (synC1st) p0000
  have p0002 := @gN2ndex
  have p0003 := @gWppimagefn (synC2nd) p0002
  have p0004 :=
    @gPm32i (synWfn (synCimage (synC1st)) (synCvv))
      (synWfn (synCimage (synC2nd)) (synCvv)) p0001 p0003
  have p0005 :=
    @gFntxp (synCvv) (synCvv) (synCimage (synC1st)) (synCimage (synC2nd))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gInidm (synCvv)
  have p0008 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) p0007
  have p0009 :=
    @gMpbi
      (synWfn (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) (synCvv)) p0006
      p0008
  have p0010 := (Nominal.classEqRefl (synClnpairraisefn))
  have p0011 :=
    @gFneq1i (synCvv) (synClnpairraisefn)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) p0010
  have p0012 :=
    @gMpbir (synWfn (synClnpairraisefn) (synCvv))
      (synWfn (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) (synCvv)) p0009
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lnpairraisefnval`. -/
@[expose]
noncomputable def gLnpairraisefnval (X : Class) (Y : Class)
    (hyp_lnpairraisefnval_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_lnpairraisefnval_2 : Nominal.NPrf (.classMem Y (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpairraisefn) (synCsn (synCop X Y)))
        (synCop (synCsn X) (synCsn Y))) :=
  by
  have dv_cache_0001 : Disjoint ((synCsn (synCop X Y))).fv ((synC1st)).fv := by
    exact
      (show Disjoint ((synCsn (synCop X Y))).fv ((synC1st)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
          exact (show Disjoint (((synCop X Y)).fv) ((∅ : Finset Var)) from (by simp))))
  have dv_cache_0002 : Disjoint ((synCsn (synCop X Y))).fv ((synC2nd)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((synCsn (synCop X Y))).fv ((synC2nd)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
          exact (show Disjoint (((synCop X Y)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (synClnpairraisefn))
  have p0001 :=
    @gFveq1i (synCsn (synCop X Y)) (synClnpairraisefn)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) p0000
  have p0002 := @gEqid (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
  have p0003 := @gN1stex
  have p0004 := @gWppimagefn (synC1st) p0003
  have p0005 := @gSnex (synCop X Y)
  have p0006 :=
    @gPm32i (synWfn (synCimage (synC1st)) (synCvv))
      (.classMem (synCsn (synCop X Y)) (synCvv)) p0004 p0005
  have p0007 :=
    @gFnbrfvb (synCvv) (synCsn (synCop X Y))
      (synCfv (synCimage (synC1st)) (synCsn (synCop X Y))) (synCimage (synC1st))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gMpbi
      (.classEq (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
        (synCfv (synCimage (synC1st)) (synCsn (synCop X Y))))
      (synWbr (synCsn (synCop X Y)) (synCimage (synC1st))
        (synCfv (synCimage (synC1st)) (synCsn (synCop X Y))))
      p0002 p0008
  have p0010 := @gEqid (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y)))
  have p0011 := @gN2ndex
  have p0012 := @gWppimagefn (synC2nd) p0011
  have p0014 :=
    @gPm32i (synWfn (synCimage (synC2nd)) (synCvv))
      (.classMem (synCsn (synCop X Y)) (synCvv)) p0012 p0005
  have p0015 :=
    @gFnbrfvb (synCvv) (synCsn (synCop X Y))
      (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))) (synCimage (synC2nd))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gMpbi
      (.classEq (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y)))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))))
      (synWbr (synCsn (synCop X Y)) (synCimage (synC2nd))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))))
      p0010 p0016
  have p0018 :=
    @gPm32i
      (synWbr (synCsn (synCop X Y)) (synCimage (synC1st))
        (synCfv (synCimage (synC1st)) (synCsn (synCop X Y))))
      (synWbr (synCsn (synCop X Y)) (synCimage (synC2nd))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))))
      p0009 p0017
  have p0019 :=
    @gTrtxp (synCsn (synCop X Y))
      (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
      (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))) (synCimage (synC1st))
      (synCimage (synC2nd))
  have p0020 :=
    @gMpbir
      (synWbr (synCsn (synCop X Y))
        (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
        (synCop (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
          (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y)))))
      (synWa (synWbr (synCsn (synCop X Y)) (synCimage (synC1st))
          (synCfv (synCimage (synC1st)) (synCsn (synCop X Y))))
        (synWbr (synCsn (synCop X Y)) (synCimage (synC2nd))
          (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y)))))
      p0018 p0019
  have p0025 :=
    @gPm32i (synWfn (synCimage (synC1st)) (synCvv))
      (synWfn (synCimage (synC2nd)) (synCvv)) p0004 p0012
  have p0026 :=
    @gFntxp (synCvv) (synCvv) (synCimage (synC1st)) (synCimage (synC2nd))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 := @gInidm (synCvv)
  have p0029 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) p0028
  have p0030 :=
    @gMpbi
      (synWfn (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) (synCvv)) p0027
      p0029
  have p0031 :=
    @gFnfun (synCvv) (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @gFunbrfv (synCsn (synCop X Y))
      (synCop (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))))
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
  have p0034 := Nominal.mp p0032 p0033
  have p0035 := Nominal.mp p0020 p0034
  have p0038 := @gWppfvimage (synCsn (synCop X Y)) (synC1st) dv_cache_0001 p0003 p0005
  have p0039 := @gDfdm4 (synCsn (synCop X Y))
  have p0040 :=
    @gEqcomi (synCdm (synCsn (synCop X Y)))
      (synCima (synC1st) (synCsn (synCop X Y))) p0039
  have p0041 :=
    @gEqtri (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
      (synCima (synC1st) (synCsn (synCop X Y))) (synCdm (synCsn (synCop X Y)))
      p0038 p0040
  have p0042 := @gDmsnop X Y hyp_lnpairraisefnval_2
  have p0043 :=
    @gEqtri (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
      (synCdm (synCsn (synCop X Y))) (synCsn X) p0041 p0042
  have p0046 := @gWppfvimage (synCsn (synCop X Y)) (synC2nd) dv_cache_0002 p0011 p0005
  have p0047 := @gDfrn5 (synCsn (synCop X Y))
  have p0048 :=
    @gEqcomi (synCrn (synCsn (synCop X Y)))
      (synCima (synC2nd) (synCsn (synCop X Y))) p0047
  have p0049 :=
    @gEqtri (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y)))
      (synCima (synC2nd) (synCsn (synCop X Y))) (synCrn (synCsn (synCop X Y)))
      p0046 p0048
  have p0050 := @gRnsnop X Y hyp_lnpairraisefnval_1
  have p0051 :=
    @gEqtri (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y)))
      (synCrn (synCsn (synCop X Y))) (synCsn Y) p0049 p0050
  have p0052 :=
    @gOpeq12i (synCfv (synCimage (synC1st)) (synCsn (synCop X Y))) (synCsn X)
      (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))) (synCsn Y) p0043 p0051
  have p0053 :=
    @gEqtri
      (synCfv (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
        (synCsn (synCop X Y)))
      (synCop (synCfv (synCimage (synC1st)) (synCsn (synCop X Y)))
        (synCfv (synCimage (synC2nd)) (synCsn (synCop X Y))))
      (synCop (synCsn X) (synCsn Y)) p0035 p0052
  have p0054 :=
    @gEqtri (synCfv (synClnpairraisefn) (synCsn (synCop X Y)))
      (synCfv (synCtxp (synCimage (synC1st)) (synCimage (synC2nd)))
        (synCsn (synCop X Y)))
      (synCop (synCsn X) (synCsn Y)) p0001 p0053
  exact p0054

/-- Checked nominal proof certificate identified upstream as `g_lnsifnfn`. -/
@[expose]
noncomputable def gLnsifnfn : Nominal.NPrf (synWfn (synClnsifn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpairraisefn))
  have p0001 := @gN1stex
  have p0002 := @gImageex (synC1st) p0001
  have p0003 := @gN2ndex
  have p0004 := @gImageex (synC2nd) p0003
  have p0005 := @gTxpex (synCimage (synC1st)) (synCimage (synC2nd)) p0002 p0004
  have p0006 :=
    @gEqeltri (synClnpairraisefn)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) (synCvv) p0000 p0005
  have p0007 := @gWppimagefn (synClnpairraisefn) p0006
  have p0008 := @gFnfullfun (synCpw1fn)
  have p0009 :=
    @gFncovv (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)) p0007 p0008
  have p0010 := (Nominal.classEqRefl (synClnsifn))
  have p0011 :=
    @gFneq1i (synCvv) (synClnsifn)
      (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn))) p0010
  have p0012 :=
    @gMpbir (synWfn (synClnsifn) (synCvv))
      (synWfn (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)))
        (synCvv))
      p0009 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lnsifnex`. -/
@[expose]
noncomputable def gLnsifnex : Nominal.NPrf (.classMem (synClnsifn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnsifn))
  have p0001 := (Nominal.classEqRefl (synClnpairraisefn))
  have p0002 := @gN1stex
  have p0003 := @gImageex (synC1st) p0002
  have p0004 := @gN2ndex
  have p0005 := @gImageex (synC2nd) p0004
  have p0006 := @gTxpex (synCimage (synC1st)) (synCimage (synC2nd)) p0003 p0005
  have p0007 :=
    @gEqeltri (synClnpairraisefn)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) (synCvv) p0001 p0006
  have p0008 := @gImageex (synClnpairraisefn) p0007
  have p0009 := @gPw1fnex
  have p0010 := @gFullfunex (synCpw1fn) p0009
  have p0011 :=
    @gCoex (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)) p0008 p0010
  have p0012 :=
    @gEqeltri (synClnsifn)
      (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn))) (synCvv)
      p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_lnsifnrawval`. -/
@[expose]
noncomputable def gLnsifnrawval (R : Class)
    (hyp_lnsifnrawval_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnsifn) (synCsn R))
        (synCima (synClnpairraisefn) (synCpw1 R))) :=
  by
  have dv_cache_0001 : Disjoint ((synCpw1 R)).fv ((synClnpairraisefn)).fv := by
    exact
      (show Disjoint ((synCpw1 R)).fv ((synClnpairraisefn)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn];
          exact (show Disjoint ((R).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (synClnsifn))
  have p0001 :=
    @gFveq1i (synCsn R) (synClnsifn)
      (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn))) p0000
  have p0002 := @gFnfullfun (synCpw1fn)
  have p0003 := @gSnex R
  have p0004 :=
    @gPm32i (synWfn (synCfullfun (synCpw1fn)) (synCvv))
      (.classMem (synCsn R) (synCvv)) p0002 p0003
  have p0005 :=
    @gFvco2 (synCvv) (synCsn R) (synCimage (synClnpairraisefn))
      (synCfullfun (synCpw1fn))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gFvfullfun (synCsn R) (synCpw1fn)
  have p0008 := @gPw1fnval R hyp_lnsifnrawval_1
  have p0009 :=
    @gEqtri (synCfv (synCfullfun (synCpw1fn)) (synCsn R))
      (synCfv (synCpw1fn) (synCsn R)) (synCpw1 R) p0007 p0008
  have p0010 :=
    @gFveq2i (synCfv (synCfullfun (synCpw1fn)) (synCsn R)) (synCpw1 R)
      (synCimage (synClnpairraisefn)) p0009
  have p0011 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)))
        (synCsn R))
      (synCfv (synCimage (synClnpairraisefn))
        (synCfv (synCfullfun (synCpw1fn)) (synCsn R)))
      (synCfv (synCimage (synClnpairraisefn)) (synCpw1 R)) p0006 p0010
  have p0012 := (Nominal.classEqRefl (synClnpairraisefn))
  have p0013 := @gN1stex
  have p0014 := @gImageex (synC1st) p0013
  have p0015 := @gN2ndex
  have p0016 := @gImageex (synC2nd) p0015
  have p0017 := @gTxpex (synCimage (synC1st)) (synCimage (synC2nd)) p0014 p0016
  have p0018 :=
    @gEqeltri (synClnpairraisefn)
      (synCtxp (synCimage (synC1st)) (synCimage (synC2nd))) (synCvv) p0012 p0017
  have p0019 := @gPw1ex R hyp_lnsifnrawval_1
  have p0020 := @gWppfvimage (synCpw1 R) (synClnpairraisefn) dv_cache_0001 p0018 p0019
  have p0021 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)))
        (synCsn R))
      (synCfv (synCimage (synClnpairraisefn)) (synCpw1 R))
      (synCima (synClnpairraisefn) (synCpw1 R)) p0011 p0020
  have p0022 :=
    @gEqtri (synCfv (synClnsifn) (synCsn R))
      (synCfv (synCcom (synCimage (synClnpairraisefn)) (synCfullfun (synCpw1fn)))
        (synCsn R))
      (synCima (synClnpairraisefn) (synCpw1 R)) p0001 p0021
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

/-- Checked nominal proof certificate identified upstream as `g_lnsifnimageexactg`. -/
@[expose]
noncomputable def gLnsifnimageexactg (R : Class) :
    Nominal.NPrf
      (.imp (synWss R (synCxp (synCvv) (synCvv)))
        (.classEq (synCima (synClnpairraisefn) (synCpw1 R)) (synCsi R))) :=
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
  have dv_cache_0002 : s ∉ ((synCpw1 R)).fv :=
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
  have dv_cache_0003 : s ∉ ((synClnpairraisefn)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0009 : y ∉ ((synCvv)).fv :=
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
      ((Wff.imp (.classEq (.cv s) (synCsn (.cv p)))
          (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
            (.classMem (.cv c) (synCsi R))))).fv :=
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
    y ∉ ((synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))).fv :=
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
      ((Wff.imp (.classEq (.cv s) (synCsn (.cv p)))
          (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
            (.classMem (.cv c) (synCsi R))))).fv :=
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
    x ∉ ((synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))).fv :=
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
      ((Wff.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (synCsi R)))).fv :=
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
  have dv_cache_0016 : p ∉ ((synWss R (synCxp (synCvv) (synCvv)))).fv :=
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
  have dv_cache_0017 : s ∉ ((Wff.classMem (.cv c) (synCsi R))).fv :=
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
  have dv_cache_0018 : s ∉ ((synWss R (synCxp (synCvv) (synCvv)))).fv :=
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
  have dv_cache_0019 : c ∉ ((synCima (synClnpairraisefn) (synCpw1 R))).fv :=
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
  have dv_cache_0020 : c ∉ ((synCsi R)).fv :=
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
  have dv_cache_0021 : c ∉ ((synWss R (synCxp (synCvv) (synCvv)))).fv :=
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
    y ∉ ((synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b))).fv :=
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
    x ∉ ((synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b))).fv :=
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
  have dv_cache_0030 : a ∉ ((synCsi R)).fv :=
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
  have dv_cache_0031 : b ∉ ((synCsi R)).fv :=
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
  have dv_cache_0032 : a ∉ ((synCima (synClnpairraisefn) (synCpw1 R))).fv :=
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
  have dv_cache_0033 : b ∉ ((synCima (synClnpairraisefn) (synCpw1 R))).fv :=
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
  have p0000 := @gLnpairraisefnfn
  have p0001 := @gFnfun (synCvv) (synClnpairraisefn)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gFvelima s (.cv c) (synCpw1 R) (synClnpairraisefn) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0004 :=
    @gMpan (synWfun (synClnpairraisefn))
      (.classMem (.cv c) (synCima (synClnpairraisefn) (synCpw1 R)))
      (synWrex s (synCpw1 R) (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      p0002 p0003
  have p0005 :=
    @gA1i
      (.imp (.classMem (.cv c) (synCima (synClnpairraisefn) (synCpw1 R)))
        (synWrex s (synCpw1 R) (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synWss R (synCxp (synCvv) (synCvv))) p0004
  have p0006 := @gElpw1 p (.cv s) R dv_cache_0004 dv_cache_0005
  have p0007 :=
    @gA1i
      (synWb (.classMem (.cv s) (synCpw1 R))
        (synWrex p R (.classEq (.cv s) (synCsn (.cv p)))))
      (synWss R (synCxp (synCvv) (synCvv))) p0006
  have p0008 := @gId (synWss R (synCxp (synCvv) (synCvv)))
  have p0009 :=
    @gSselda (synWss R (synCxp (synCvv) (synCvv))) R (synCxp (synCvv) (synCvv))
      (.cv p) p0008
  have p0010 :=
    @gElxp x y (.cv p) (synCvv) (synCvv) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0011 :=
    @gSylib (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (.classMem (.cv p) (synCxp (synCvv) (synCvv)))
      (synWex x (synWex y (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      p0009 p0010
  have p0012 :=
    @gSimpr (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synW3a (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p)))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
  have p0013 :=
    @gN3simpb
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (.cv s) (synCsn (.cv p)))
      (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
  have p0014 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synW3a (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p)))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      (synWa (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      p0012 p0013
  have p0015 :=
    @gSimpr
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synWa (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)) p0014 p0015
  have p0017 :=
    @gEqcomd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synCfv (synClnpairraisefn) (.cv s)) (.cv c) p0016
  have p0019 :=
    @gN3simpa
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (.cv s) (synCsn (.cv p)))
      (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synW3a (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p)))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      (synWa (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p))))
      p0012 p0019
  have p0021 :=
    @gSimpr
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (.cv s) (synCsn (.cv p)))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synWa (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p))))
      (.classEq (.cv s) (synCsn (.cv p))) p0020 p0021
  have p0026 :=
    @gSimpl
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (.cv s) (synCsn (.cv p)))
  have p0027 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synWa (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p))))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      p0020 p0026
  have p0028 :=
    @gSimpl (.classEq (.cv p) (synCop (.cv x) (.cv y)))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
  have p0029 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (.cv p) (synCop (.cv x) (.cv y))) p0027 p0028
  have p0030 :=
    @gSneqd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.cv p) (synCop (.cv x) (.cv y)) p0029
  have p0031 :=
    @gEqtrd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.cv s) (synCsn (.cv p)) (synCsn (synCop (.cv x) (.cv y))) p0022 p0030
  have p0032 :=
    @gFveq2d
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.cv s) (synCsn (synCop (.cv x) (.cv y))) (synClnpairraisefn) p0031
  have p0033 := @gVex x
  have p0034 := @gVex y
  have p0035 := @gLnpairraisefnval (.cv x) (.cv y) p0033 p0034
  have p0036 :=
    @gA1i
      (.classEq (synCfv (synClnpairraisefn) (synCsn (synCop (.cv x) (.cv y))))
        (synCop (synCsn (.cv x)) (synCsn (.cv y))))
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      p0035
  have p0037 :=
    @gEqtrd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synCfv (synClnpairraisefn) (.cv s))
      (synCfv (synClnpairraisefn) (synCsn (synCop (.cv x) (.cv y))))
      (synCop (synCsn (.cv x)) (synCsn (.cv y))) p0032 p0036
  have p0038 :=
    @gEqtrd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.cv c) (synCfv (synClnpairraisefn) (.cv s))
      (synCop (synCsn (.cv x)) (synCsn (.cv y))) p0017 p0037
  have p0046 :=
    @gSimpl (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synW3a (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p)))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
  have p0047 := @gSimpr (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)
  have p0048 :=
    @gSyl
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (.classMem (.cv p) R) p0046 p0047
  have p0049 :=
    @gEqeltrrd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.cv p) (synCop (.cv x) (.cv y)) R p0029 p0048
  have p0052 := @gOpsnelsi (.cv x) (.cv y) R p0033 p0034
  have p0053 :=
    @gSylibr
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.classMem (synCop (.cv x) (.cv y)) R)
      (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv y))) (synCsi R)) p0049 p0052
  have p0054 :=
    @gEqeltrd
      (synWa (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)) (synW3a
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
          (.classEq (.cv s) (synCsn (.cv p)))
          (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))))
      (.cv c) (synCop (synCsn (.cv x)) (synCsn (.cv y))) (synCsi R) p0038 p0053
  have p0055 :=
    @gEx (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synW3a (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
        (.classEq (.cv s) (synCsn (.cv p)))
        (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      (.classMem (.cv c) (synCsi R)) p0054
  have p0056 :=
    @gN3expd (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq (.cv s) (synCsn (.cv p)))
      (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
      (.classMem (.cv c) (synCsi R)) p0055
  have p0057 :=
    @gExlimdv (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.imp (.classEq (.cv s) (synCsn (.cv p)))
        (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (synCsi R))))
      y dv_cache_0011 dv_cache_0012 p0056
  have p0058 :=
    @gExlimdv (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synWex y (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (.imp (.classEq (.cv s) (synCsn (.cv p)))
        (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (synCsi R))))
      x dv_cache_0013 dv_cache_0014 p0057
  have p0059 :=
    @gMpd (synWa (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R))
      (synWex x (synWex y (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      (.imp (.classEq (.cv s) (synCsn (.cv p)))
        (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (synCsi R))))
      p0011 p0058
  have p0060 :=
    @gEx (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv p) R)
      (.imp (.classEq (.cv s) (synCsn (.cv p)))
        (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
          (.classMem (.cv c) (synCsi R))))
      p0059
  have p0061 :=
    @gRexlimdv (synWss R (synCxp (synCvv) (synCvv)))
      (.classEq (.cv s) (synCsn (.cv p)))
      (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
        (.classMem (.cv c) (synCsi R)))
      p R dv_cache_0015 dv_cache_0016 p0060
  have p0062 :=
    @gSylbid (synWss R (synCxp (synCvv) (synCvv))) (.classMem (.cv s) (synCpw1 R))
      (synWrex p R (.classEq (.cv s) (synCsn (.cv p))))
      (.imp (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
        (.classMem (.cv c) (synCsi R)))
      p0007 p0061
  have p0063 :=
    @gRexlimdv (synWss R (synCxp (synCvv) (synCvv)))
      (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c))
      (.classMem (.cv c) (synCsi R)) s (synCpw1 R) dv_cache_0017 dv_cache_0018 p0062
  have p0064 :=
    @gSyld (synWss R (synCxp (synCvv) (synCvv)))
      (.classMem (.cv c) (synCima (synClnpairraisefn) (synCpw1 R)))
      (synWrex s (synCpw1 R) (.classEq (synCfv (synClnpairraisefn) (.cv s)) (.cv c)))
      (.classMem (.cv c) (synCsi R)) p0005 p0063
  have p0065 :=
    @gSsrdv (synWss R (synCxp (synCvv) (synCvv))) c
      (synCima (synClnpairraisefn) (synCpw1 R)) (synCsi R) dv_cache_0019 dv_cache_0020
      dv_cache_0021 p0064
  have p0066 := @gId (.classMem (synCop (.cv a) (.cv b)) (synCsi R))
  have p0067 := (Nominal.biimpRefl (synWbr (.cv a) (synCsi R) (.cv b)))
  have p0068 :=
    @gSylibr (.classMem (synCop (.cv a) (.cv b)) (synCsi R))
      (.classMem (synCop (.cv a) (.cv b)) (synCsi R))
      (synWbr (.cv a) (synCsi R) (.cv b)) p0066 p0067
  have p0069 :=
    @gBrsi x y (.cv a) (.cv b) R dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0010
  have p0070 :=
    @gN3simpa (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0071 :=
    @gSimpl (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
  have p0072 :=
    @gSyl
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y))))
      (.classEq (.cv a) (synCsn (.cv x))) p0070 p0071
  have p0074 :=
    @gSimpr (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
  have p0075 :=
    @gSyl
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y))))
      (.classEq (.cv b) (synCsn (.cv y))) p0070 p0074
  have p0076 :=
    @gOpeq12d
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (.cv a) (synCsn (.cv x)) (.cv b) (synCsn (.cv y)) p0072 p0075
  have p0080 :=
    @gA1i
      (.classEq (synCfv (synClnpairraisefn) (synCsn (synCop (.cv x) (.cv y))))
        (synCop (synCsn (.cv x)) (synCsn (.cv y))))
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      p0035
  have p0081 :=
    @gEqtr4d
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synCop (.cv a) (.cv b)) (synCop (synCsn (.cv x)) (synCsn (.cv y)))
      (synCfv (synClnpairraisefn) (synCsn (synCop (.cv x) (.cv y)))) p0076 p0080
  have p0082 :=
    @gN3simpb (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0083 := @gSimpr (.classEq (.cv a) (synCsn (.cv x))) (synWbr (.cv x) R (.cv y))
  have p0084 :=
    @gSyl
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (.cv a) (synCsn (.cv x))) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0082 p0083
  have p0085 := (Nominal.biimpRefl (synWbr (.cv x) R (.cv y)))
  have p0086 :=
    @gSylib
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv x) R (.cv y)) (.classMem (synCop (.cv x) (.cv y)) R) p0084 p0085
  have p0087 := @gSnelpw1 (synCop (.cv x) (.cv y)) R
  have p0088 :=
    @gSylibr
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (.classMem (synCop (.cv x) (.cv y)) R)
      (.classMem (synCsn (synCop (.cv x) (.cv y))) (synCpw1 R)) p0086 p0087
  have p0092 := @gSnex (synCop (.cv x) (.cv y))
  have p0094 := @gFndm (synCvv) (synClnpairraisefn)
  have p0095 := Nominal.mp p0000 p0094
  have p0096 :=
    @gEleqtrri (synCsn (synCop (.cv x) (.cv y))) (synCvv)
      (synCdm (synClnpairraisefn)) p0092 p0095
  have p0097 :=
    @gPm32i (synWfun (synClnpairraisefn))
      (.classMem (synCsn (synCop (.cv x) (.cv y))) (synCdm (synClnpairraisefn))) p0002
      p0096
  have p0098 :=
    @gFunfvima (synCpw1 R) (synCsn (synCop (.cv x) (.cv y))) (synClnpairraisefn)
  have p0099 := Nominal.mp p0097 p0098
  have p0100 :=
    @gSyl
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (.classMem (synCsn (synCop (.cv x) (.cv y))) (synCpw1 R))
      (.classMem (synCfv (synClnpairraisefn) (synCsn (synCop (.cv x) (.cv y))))
        (synCima (synClnpairraisefn) (synCpw1 R)))
      p0088 p0099
  have p0101 :=
    @gEqeltrd
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synCop (.cv a) (.cv b))
      (synCfv (synClnpairraisefn) (synCsn (synCop (.cv x) (.cv y))))
      (synCima (synClnpairraisefn) (synCpw1 R)) p0081 p0100
  have p0102 :=
    (Nominal.biimpRefl (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b)))
  have p0103 :=
    @gSylibr
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (.classMem (synCop (.cv a) (.cv b)) (synCima (synClnpairraisefn) (synCpw1 R)))
      (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b)) p0101 p0102
  have p0104 :=
    @gExlimiv
      (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b)) y
      dv_cache_0028 p0103
  have p0105 :=
    @gExlimiv
      (synWex y
        (synW3a (.classEq (.cv a) (synCsn (.cv x))) (.classEq (.cv b) (synCsn (.cv y)))
          (synWbr (.cv x) R (.cv y))))
      (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b)) x
      dv_cache_0029 p0104
  have p0106 :=
    @gSylbi (synWbr (.cv a) (synCsi R) (.cv b))
      (synWex x (synWex y (synW3a (.classEq (.cv a) (synCsn (.cv x)))
            (.classEq (.cv b) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b)) p0069 p0105
  have p0107 :=
    @gSyl (.classMem (synCop (.cv a) (.cv b)) (synCsi R))
      (synWbr (.cv a) (synCsi R) (.cv b))
      (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b)) p0068 p0106
  have p0109 :=
    @gBiimpi (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b))
      (.classMem (synCop (.cv a) (.cv b)) (synCima (synClnpairraisefn) (synCpw1 R)))
      p0102
  have p0110 :=
    @gSyl (.classMem (synCop (.cv a) (.cv b)) (synCsi R))
      (synWbr (.cv a) (synCima (synClnpairraisefn) (synCpw1 R)) (.cv b))
      (.classMem (synCop (.cv a) (.cv b)) (synCima (synClnpairraisefn) (synCpw1 R)))
      p0107 p0109
  have p0111 := Nominal.gen p0110 b
  have p0112 := Nominal.gen p0111 a
  have p0113 :=
    @gSsrel a b (synCsi R) (synCima (synClnpairraisefn) (synCpw1 R)) dv_cache_0030
      dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
  have p0114 :=
    @gMpbir (synWss (synCsi R) (synCima (synClnpairraisefn) (synCpw1 R)))
      (.all a (.all b (.imp (.classMem (synCop (.cv a) (.cv b)) (synCsi R))
            (.classMem (synCop (.cv a) (.cv b))
              (synCima (synClnpairraisefn) (synCpw1 R))))))
      p0112 p0113
  have p0115 :=
    @gA1i (synWss (synCsi R) (synCima (synClnpairraisefn) (synCpw1 R)))
      (synWss R (synCxp (synCvv) (synCvv))) p0114
  have p0116 :=
    @gEqssd (synWss R (synCxp (synCvv) (synCvv)))
      (synCima (synClnpairraisefn) (synCpw1 R)) (synCsi R) p0065 p0115
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

/-- Checked nominal proof certificate identified upstream as `g_lnsifnvalg`. -/
@[expose]
noncomputable def gLnsifnvalg (R : Class)
    (hyp_lnsifnvalg_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.imp (synWss R (synCxp (synCvv) (synCvv)))
        (.classEq (synCfv (synClnsifn) (synCsn R)) (synCsi R))) :=
  by
  have p0000 := @gLnsifnrawval R hyp_lnsifnvalg_1
  have p0001 :=
    @gA1i
      (.classEq (synCfv (synClnsifn) (synCsn R))
        (synCima (synClnpairraisefn) (synCpw1 R)))
      (synWss R (synCxp (synCvv) (synCvv))) p0000
  have p0002 := @gLnsifnimageexactg R
  have p0003 :=
    @gEqtrd (synWss R (synCxp (synCvv) (synCvv))) (synCfv (synClnsifn) (synCsn R))
      (synCima (synClnpairraisefn) (synCpw1 R)) (synCsi R) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_lnpwsirelfnfn`. -/
@[expose]
noncomputable def gLnpwsirelfnfn : Nominal.NPrf (synWfn (synClnpwsirelfn) (synCvv)) :=
  by
  have p0000 := @gLnsifnfn
  have p0001 := @gN1stex
  have p0002 := @gWppimagefn (synC1st) p0001
  have p0003 := @gFncovv (synClnsifn) (synCimage (synC1st)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (synClnpwsirelfn))
  have p0005 :=
    @gFneq1i (synCvv) (synClnpwsirelfn)
      (synCcom (synClnsifn) (synCimage (synC1st))) p0004
  have p0006 :=
    @gMpbir (synWfn (synClnpwsirelfn) (synCvv))
      (synWfn (synCcom (synClnsifn) (synCimage (synC1st))) (synCvv)) p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lnpwsirelfnex`. -/
@[expose]
noncomputable def gLnpwsirelfnex :
    Nominal.NPrf (.classMem (synClnpwsirelfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnpwsirelfn))
  have p0001 := @gLnsifnex
  have p0002 := @gN1stex
  have p0003 := @gImageex (synC1st) p0002
  have p0004 := @gCoex (synClnsifn) (synCimage (synC1st)) p0001 p0003
  have p0005 :=
    @gEqeltri (synClnpwsirelfn) (synCcom (synClnsifn) (synCimage (synC1st)))
      (synCvv) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_lnpwsirelfnrawval`. -/
@[expose]
noncomputable def gLnpwsirelfnrawval (D : Class) (R : Class)
    (_hyp_lnpwsirelfnrawval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwsirelfnrawval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
        (synCfv (synClnsifn) (synCsn R))) :=
  by
  have dv_cache_0001 : Disjoint ((synCsn (synCop R D))).fv ((synC1st)).fv := by
    exact
      (show Disjoint ((synCsn (synCop R D))).fv ((synC1st)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
          exact (show Disjoint (((synCop R D)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 := (Nominal.classEqRefl (synClnpwsirelfn))
  have p0001 :=
    @gFveq1i (synCsn (synCop R D)) (synClnpwsirelfn)
      (synCcom (synClnsifn) (synCimage (synC1st))) p0000
  have p0002 := @gN1stex
  have p0003 := @gWppimagefn (synC1st) p0002
  have p0004 := @gSnex (synCop R D)
  have p0005 :=
    @gPm32i (synWfn (synCimage (synC1st)) (synCvv))
      (.classMem (synCsn (synCop R D)) (synCvv)) p0003 p0004
  have p0006 :=
    @gFvco2 (synCvv) (synCsn (synCop R D)) (synClnsifn) (synCimage (synC1st))
  have p0007 := Nominal.mp p0005 p0006
  have p0010 := @gWppfvimage (synCsn (synCop R D)) (synC1st) dv_cache_0001 p0002 p0004
  have p0011 := @gDfdm4 (synCsn (synCop R D))
  have p0012 :=
    @gEqcomi (synCdm (synCsn (synCop R D)))
      (synCima (synC1st) (synCsn (synCop R D))) p0011
  have p0013 :=
    @gEqtri (synCfv (synCimage (synC1st)) (synCsn (synCop R D)))
      (synCima (synC1st) (synCsn (synCop R D))) (synCdm (synCsn (synCop R D)))
      p0010 p0012
  have p0014 := @gDmsnop R D hyp_lnpwsirelfnrawval_2
  have p0015 :=
    @gEqtri (synCfv (synCimage (synC1st)) (synCsn (synCop R D)))
      (synCdm (synCsn (synCop R D))) (synCsn R) p0013 p0014
  have p0016 :=
    @gFveq2i (synCfv (synCimage (synC1st)) (synCsn (synCop R D))) (synCsn R)
      (synClnsifn) p0015
  have p0017 :=
    @gEqtri
      (synCfv (synCcom (synClnsifn) (synCimage (synC1st))) (synCsn (synCop R D)))
      (synCfv (synClnsifn) (synCfv (synCimage (synC1st)) (synCsn (synCop R D))))
      (synCfv (synClnsifn) (synCsn R)) p0007 p0016
  have p0018 :=
    @gEqtri (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
      (synCfv (synCcom (synClnsifn) (synCimage (synC1st))) (synCsn (synCop R D)))
      (synCfv (synClnsifn) (synCsn R)) p0001 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_lnpwsirelfnvalg`. -/
@[expose]
noncomputable def gLnpwsirelfnvalg (D : Class) (R : Class)
    (hyp_lnpwsirelfnvalg_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnpwsirelfnvalg_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWss R (synCxp (synCvv) (synCvv)))
        (.classEq (synCfv (synClnpwsirelfn) (synCsn (synCop R D))) (synCsi R))) :=
  by
  have p0000 := @gLnpwsirelfnrawval D R hyp_lnpwsirelfnvalg_1 hyp_lnpwsirelfnvalg_2
  have p0001 :=
    @gA1i
      (.classEq (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
        (synCfv (synClnsifn) (synCsn R)))
      (synWss R (synCxp (synCvv) (synCvv))) p0000
  have p0002 := @gLnsifnvalg R hyp_lnpwsirelfnvalg_1
  have p0003 :=
    @gEqtrd (synWss R (synCxp (synCvv) (synCvv)))
      (synCfv (synClnpwsirelfn) (synCsn (synCop R D)))
      (synCfv (synClnsifn) (synCsn R)) (synCsi R) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pw1subuniss`. -/
@[expose]
noncomputable def gPw1subuniss (x : Var) (A : Class) :
    Nominal.NPrf (.imp (synWss (.cv x) (synCpw1 A)) (synWss (synCuni (.cv x)) A)) :=
  by
  have p0000 := @gUniss (.cv x) (synCpw1 A)
  have p0001 := @gUnipw1 A
  have p0002 := @gSseq2i (synCuni (synCpw1 A)) A (synCuni (.cv x)) p0001
  have p0003 :=
    @gBiimpi (synWss (synCuni (.cv x)) (synCuni (synCpw1 A)))
      (synWss (synCuni (.cv x)) A) p0002
  have p0004 :=
    @gSyl (synWss (.cv x) (synCpw1 A))
      (synWss (synCuni (.cv x)) (synCuni (synCpw1 A))) (synWss (synCuni (.cv x)) A)
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pw1subunine`. -/
@[expose]
noncomputable def gPw1subunine (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (synWne (synCuni (.cv x)) (synC0))) :=
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
  have dv_cache_0002 : q ∉ ((synWne (synCuni (.cv x)) (synC0))).fv :=
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
    q ∉ ((synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))).fv :=
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
  have p0000 := @gSimpr (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0))
  have p0001 := @gN0 q (.cv x) dv_cache_0001
  have p0002 :=
    @gBiimpi (synWne (.cv x) (synC0)) (synWex q (.classMem (.cv q) (.cv x))) p0001
  have p0003 :=
    @gSyl (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
      (synWne (.cv x) (synC0)) (synWex q (.classMem (.cv q) (.cv x))) p0000 p0002
  have p0004 := @gVex q
  have p0005 := @gUniex (.cv q) p0004
  have p0006 := @gSnid (synCuni (.cv q)) p0005
  have p0007 :=
    @gA1i (.classMem (synCuni (.cv q)) (synCsn (synCuni (.cv q))))
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      p0006
  have p0008 :=
    @gSimpl (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
      (.classMem (.cv q) (.cv x))
  have p0009 := @gSimpl (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0))
  have p0010 :=
    @gSyl
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCpw1 A)) p0008 p0009
  have p0011 :=
    @gSimpr (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
      (.classMem (.cv q) (.cv x))
  have p0012 :=
    @gSseldd
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (.cv x) (synCpw1 A) (.cv q) p0010 p0011
  have p0013 := @gHnwpw1argcl A q
  have p0014 :=
    @gSyl
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (.cv q) (synCpw1 A))
      (synWa (.classMem (synCuni (.cv q)) A) (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0012 p0013
  have p0015 :=
    @gSimprd
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (synCuni (.cv q)) A) (.classEq (.cv q) (synCsn (synCuni (.cv q))))
      p0014
  have p0016 :=
    @gEleqtrrd
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (synCuni (.cv q)) (synCsn (synCuni (.cv q))) (.cv q) p0007 p0015
  have p0018 :=
    @gJca
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (synCuni (.cv q)) (.cv q)) (.classMem (.cv q) (.cv x)) p0016 p0011
  have p0019 := @gElunii (synCuni (.cv q)) (.cv q) (.cv x)
  have p0020 :=
    @gSyl
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (synWa (.classMem (synCuni (.cv q)) (.cv q)) (.classMem (.cv q) (.cv x)))
      (.classMem (synCuni (.cv q)) (synCuni (.cv x))) p0018 p0019
  have p0021 := @gNe0i (synCuni (.cv x)) (synCuni (.cv q))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
        (.classMem (.cv q) (.cv x)))
      (.classMem (synCuni (.cv q)) (synCuni (.cv x)))
      (synWne (synCuni (.cv x)) (synC0)) p0020 p0021
  have p0023 :=
    @gExlimddv (synWa (synWss (.cv x) (synCpw1 A)) (synWne (.cv x) (synC0)))
      (.classMem (.cv q) (.cv x)) (synWne (synCuni (.cv x)) (synC0)) q dv_cache_0002
      dv_cache_0003 p0003 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_wppreachopfn`. -/
@[expose]
noncomputable def gWppreachopfn (F : Class)
    (hyp_wppreachopfn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfn (synCimage (synCcnv F)) (synCvv)) :=
  by
  have p0000 := @gCnvex F hyp_wppreachopfn_1
  have p0001 := @gWppimagefn (synCcnv F) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wppreachupperex`. -/
@[expose]
noncomputable def gWppreachupperex (C : Class) :
    Nominal.NPrf (.classMem (synCima (synClec) (synCsn C)) (synCvv)) :=
  by
  have p0000 := @gLecex
  have p0001 := @gSnex C
  have p0002 := @gImaex (synClec) (synCsn C) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wppreach0`. -/
@[expose]
noncomputable def gWppreach0 (C : Class) (F : Class) (dv_C_F : Disjoint C.fv F.fv)
    (hyp_wppreachorbitfn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synC0c)) (synCima (synClec) (synCsn C))) :=
  by
  have dv_cache_0001 :
    Disjoint ((synCimage (synCcnv F))).fv ((synCima (synClec) (synCsn C))).fv := by
    exact
      (show Disjoint ((synCimage (synCcnv F))).fv ((synCima (synClec) (synCsn C))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show Disjoint (((synCcnv F)).fv) ((((synClec)).fv) ∪ (((synCsn C)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (((synCcnv F)).fv) (((synClec)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((synClec)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec];
                            exact
                              (show Disjoint ((F).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint (((synCcnv F)).fv) (((synCsn C)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((synCsn C)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                            exact
                              (show Disjoint (F).fv (C).fv from
                                (by exact dv_C_F.symm))))))⟩))))
  have p0000 := @gCnvex F hyp_wppreachorbitfn_1
  have p0001 := @gWppimagefn (synCcnv F) p0000
  have p0002 := @gFnfun (synCvv) (synCimage (synCcnv F))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @gImageex (synCcnv F) p0000
  have p0006 := @gElfuns (synCimage (synCcnv F)) p0005
  have p0007 :=
    @gMpbir (.classMem (synCimage (synCcnv F)) (synCfuns))
      (synWfun (synCimage (synCcnv F))) p0003 p0006
  have p0008 := @gLecex
  have p0009 := @gSnex C
  have p0010 := @gImaex (synClec) (synCsn C) p0008 p0009
  have p0013 := @gFndm (synCvv) (synCimage (synCcnv F))
  have p0014 := Nominal.mp p0001 p0013
  have p0015 :=
    @gEleqtrri (synCima (synClec) (synCsn C)) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0010 p0014
  have p0016 := @gSsv (synCrn (synCimage (synCcnv F)))
  have p0021 :=
    @gSseqtr4i (synCrn (synCimage (synCcnv F))) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0016 p0014
  have p0022 :=
    @gN3pm32i (.classMem (synCimage (synCcnv F)) (synCfuns))
      (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
      (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F))))
      p0007 p0015 p0021
  have p0023 :=
    @gWpporbit0 (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)) dv_cache_0001
  have p0024 := Nominal.mp p0022 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_elwppcand`. -/
@[expose]
noncomputable def gElwppcand (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppcand F C))
        (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) C))
          (.classMem D (synCwppreach F C)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcand F C))
  have p0001 :=
    @gEleq2i (synCwppcand F C)
      (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
        (synCwppreach F C))
      D p0000
  have p0002 :=
    @gElin D
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synCwppreach F C)
  have p0003 :=
    @gElin D (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))
  have p0004 := @gEliniseg (synClec) C D
  have p0005 :=
    @gAnbi2i (.classMem D (synCima (synCcnv (synClec)) (synCsn C)))
      (synWbr D (synClec) C) (.classMem D (synChwcards (synCvv))) p0004
  have p0006 :=
    @gBitri
      (.classMem D
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synWa (.classMem D (synChwcards (synCvv)))
        (.classMem D (synCima (synCcnv (synClec)) (synCsn C))))
      (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) C)) p0003 p0005
  have p0007 :=
    @gAnbi1i
      (.classMem D
        (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
      (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) C))
      (.classMem D (synCwppreach F C)) p0006
  have p0008 :=
    @gBitri
      (.classMem D (synCin
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
          (synCwppreach F C)))
      (synWa (.classMem D
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C))))
        (.classMem D (synCwppreach F C)))
      (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) C))
        (.classMem D (synCwppreach F C)))
      p0002 p0007
  have p0009 :=
    @gBitri (.classMem D (synCwppcand F C))
      (.classMem D (synCin
          (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
          (synCwppreach F C)))
      (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) C))
        (.classMem D (synCwppreach F C)))
      p0001 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hwcnwendv`. -/
@[expose]
noncomputable def gHwcnwendv (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv ((synCfv (synC1st) (.cv u))).fv := by
    exact
      (show Disjoint (A).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((synC1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (A).fv from (by exact dv_A_u)))))),
                  (show Disjoint ((A).fv) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 := @gHwcnpair u A
  have p0001 := @gHwcnraw u A
  have p0002 :=
    @gEqeltrrd (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (synChwcodes A)
      p0000 p0001
  have p0003 := @gFvex (.cv u) (synC1st)
  have p0004 := @gFvex (.cv u) (synC2nd)
  have p0005 :=
    @gElhwcodes A (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) dv_cache_0001
      p0003 p0004
  have p0006 :=
    @gBiimpi
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      p0005
  have p0007 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      p0002 p0006
  have p0008 :=
    @gSimpl (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) A)
  have p0009 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0007
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hwbaseswev`. -/
@[expose]
noncomputable def gHwbaseswev (r : Var) (d : Var) (dv_d_r : d ≠ r) :
    Nominal.NPrf
      (synWb (.classMem (.cv d) (synChwbases (synCvv)))
        (synWex r (synWbr (.cv r) (synCwe) (.cv d)))) :=
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
  have dv_cache_0001 : Disjoint ((synCvv)).fv ((Class.cv d)).fv := by
    exact
      (show Disjoint ((synCvv)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact (show Disjoint ((∅ : Finset Var)) (({ d } : Finset Var)) from (by simp))))
  have dv_cache_0002 : u ∉ ((synCvv)).fv :=
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
  have dv_cache_0004 : r ∉ ((synCfv (synC1st) (.cv u))).fv :=
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
    r ∉ ((synWbr (synCfv (synC1st) (.cv u)) (synCwe) (.cv d))).fv :=
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
  have dv_cache_0006 : u ∉ ((synWex r (synWbr (.cv r) (synCwe) (.cv d)))).fv :=
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
    Disjoint ((synCvv)).fv ((synCin (.cv r) (synCxp (.cv d) (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((synCvv)).fv ((synCin (.cv r) (synCxp (.cv d) (.cv d)))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
          exact
            (show
              Disjoint ((∅ : Finset Var))
                ((((Class.cv r)).fv) ∪ (((synCxp (.cv d) (.cv d))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((∅ : Finset Var)) (((Class.cv r)).fv) from (by simp)),
                  (show Disjoint ((∅ : Finset Var)) (((synCxp (.cv d) (.cv d))).fv) from
                    (by simp))⟩))))
  have dv_cache_0008 :
    u ∉ ((synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))).fv :=
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
  have dv_cache_0009 : u ∉ ((synChwcn (synCvv))).fv :=
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
      ((Wff.classEq (.cv d) (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))).fv :=
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
  have dv_cache_0011 : r ∉ ((Wff.classMem (.cv d) (synChwbases (synCvv)))).fv :=
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
  have p0000 := @gElhwbases u (synCvv) (.cv d) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gBiimpi (.classMem (.cv d) (synChwbases (synCvv)))
      (synWrex u (synChwcn (synCvv)) (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      p0000
  have p0002 := @gHwcnwendv u (synCvv) dv_cache_0002
  have p0003 :=
    @gAdantr (.classMem (.cv u) (synChwcn (synCvv)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (.classEq (.cv d) (synCfv (synC2nd) (.cv u))) p0002
  have p0004 :=
    @gSimpr (.classMem (.cv u) (synChwcn (synCvv)))
      (.classEq (.cv d) (synCfv (synC2nd) (.cv u)))
  have p0005 :=
    @gEqcomd
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      (.cv d) (synCfv (synC2nd) (.cv u)) p0004
  have p0006 :=
    @gBreq2d
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (.cv u)) (.cv d) (synCfv (synC1st) (.cv u)) (synCwe) p0005
  have p0007 :=
    @gMpbid
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (.cv d)) p0003 p0006
  have p0008 := @gFvex (.cv u) (synC1st)
  have p0009 := @gId (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
  have p0010 :=
    @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
      (synCfv (synC1st) (.cv u)) (.cv d) (synCwe) p0009
  have p0011 :=
    @gSpcev (synWbr (.cv r) (synCwe) (.cv d))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (.cv d)) r
      (synCfv (synC1st) (.cv u)) dv_cache_0004 dv_cache_0005 p0008 p0010
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (.cv d))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d))) p0007 p0011
  have p0013 :=
    @gEx (.classMem (.cv u) (synChwcn (synCvv)))
      (.classEq (.cv d) (synCfv (synC2nd) (.cv u)))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d))) p0012
  have p0014 :=
    @gRexlimiv (.classEq (.cv d) (synCfv (synC2nd) (.cv u)))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d))) u (synChwcn (synCvv))
      dv_cache_0006 p0013
  have p0015 :=
    @gSyl (.classMem (.cv d) (synChwbases (synCvv)))
      (synWrex u (synChwcn (synCvv)) (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d))) p0001 p0014
  have p0016 := @gId (synWbr (.cv r) (synCwe) (.cv d))
  have p0017 := @gSsid (.cv d)
  have p0018 := @gA1i (synWss (.cv d) (.cv d)) (synWbr (.cv r) (synCwe) (.cv d)) p0017
  have p0019 := @gBrex (.cv r) (.cv d) (synCwe)
  have p0020 := @gSimpr (.classMem (.cv r) (synCvv)) (.classMem (.cv d) (synCvv))
  have p0021 :=
    @gSyl (synWbr (.cv r) (synCwe) (.cv d))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv d) (synCvv)))
      (.classMem (.cv d) (synCvv)) p0019 p0020
  have p0022 :=
    @gWerestrndv (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (.cv d) (.cv r) p0016 p0018
      p0021
  have p0023 := @gSsv (.cv d)
  have p0024 :=
    @gA1i (synWss (.cv d) (synCvv)) (synWbr (.cv r) (synCwe) (.cv d)) p0023
  have p0025 :=
    @gJca (synWbr (.cv r) (synCwe) (.cv d))
      (synWbr (synCin (.cv r) (synCxp (.cv d) (.cv d))) (synCwe) (.cv d))
      (synWss (.cv d) (synCvv)) p0022 p0024
  have p0026 := @gVex r
  have p0027 := @gVex d
  have p0029 := @gXpex (.cv d) (.cv d) p0027 p0027
  have p0030 := @gInex (.cv r) (synCxp (.cv d) (.cv d)) p0026 p0029
  have p0032 :=
    @gElhwcodes (synCvv) (.cv d) (synCin (.cv r) (synCxp (.cv d) (.cv d)))
      dv_cache_0007 p0030 p0027
  have p0033 :=
    @gBiimpri
      (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
        (synChwcodes (synCvv)))
      (synWa (synWbr (synCin (.cv r) (synCxp (.cv d) (.cv d))) (synCwe) (.cv d))
        (synWss (.cv d) (synCvv)))
      p0032
  have p0034 :=
    @gSyl (synWbr (.cv r) (synCwe) (.cv d))
      (synWa (synWbr (synCin (.cv r) (synCxp (.cv d) (.cv d))) (synCwe) (.cv d))
        (synWss (.cv d) (synCvv)))
      (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
        (synChwcodes (synCvv)))
      p0025 p0033
  have p0035 := @gInss2 (.cv r) (synCxp (.cv d) (.cv d))
  have p0042 := @gOpfv1st (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d) p0030 p0027
  have p0049 := @gOpfv2nd (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d) p0030 p0027
  have p0057 :=
    @gXpeq12i
      (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (.cv d)
      (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (.cv d) p0049 p0049
  have p0058 :=
    @gSseq12i
      (synCfv (synC1st) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (synCin (.cv r) (synCxp (.cv d) (.cv d)))
      (synCxp
        (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
        (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))
      (synCxp (.cv d) (.cv d)) p0042 p0057
  have p0059 :=
    @gMpbir
      (synWss
        (synCfv (synC1st) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))) (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))))
      (synWss (synCin (.cv r) (synCxp (.cv d) (.cv d))) (synCxp (.cv d) (.cv d)))
      p0035 p0058
  have p0060 :=
    @gA1i
      (synWss
        (synCfv (synC1st) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))) (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))))
      (synWbr (.cv r) (synCwe) (.cv d)) p0059
  have p0061 :=
    @gJca (synWbr (.cv r) (synCwe) (.cv d))
      (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
        (synChwcodes (synCvv)))
      (synWss
        (synCfv (synC1st) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))) (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))))
      p0034 p0060
  have p0068 := @gOpex (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d) p0030 p0027
  have p0069 :=
    @gElhwcncl (synCvv) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
  have p0070 := Nominal.mp p0068 p0069
  have p0071 :=
    @gBiimpri
      (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
        (synChwcn (synCvv)))
      (synWa (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
          (synChwcodes (synCvv))) (synWss (synCfv (synC1st)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))) (synCxp
            (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
            (synCfv (synC2nd)
              (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))))
      p0070
  have p0072 :=
    @gSyl (synWbr (.cv r) (synCwe) (.cv d))
      (synWa (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
          (synChwcodes (synCvv))) (synWss (synCfv (synC1st)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))) (synCxp
            (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
            (synCfv (synC2nd)
              (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))))
      (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
        (synChwcn (synCvv)))
      p0061 p0071
  have p0080 :=
    @gEqcomi
      (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (.cv d) p0049
  have p0081 :=
    @gA1i
      (.classEq (.cv d) (synCfv (synC2nd)
          (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))
      (synWbr (.cv r) (synCwe) (.cv d)) p0080
  have p0082 :=
    @gJca (synWbr (.cv r) (synCwe) (.cv d))
      (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
        (synChwcn (synCvv)))
      (.classEq (.cv d) (synCfv (synC2nd)
          (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))
      p0072 p0081
  have p0083 :=
    @gId (.classEq (.cv u) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
  have p0084 :=
    @gFveq2d
      (.classEq (.cv u) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (.cv u) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)) (synC2nd)
      p0083
  have p0085 :=
    @gEqeq2d
      (.classEq (.cv u) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))
      (.cv d) p0084
  have p0086 :=
    @gRspcev (.classEq (.cv d) (synCfv (synC2nd) (.cv u)))
      (.classEq (.cv d) (synCfv (synC2nd)
          (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))))
      u (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
      (synChwcn (synCvv)) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0085
  have p0087 :=
    @gSyl (synWbr (.cv r) (synCwe) (.cv d))
      (synWa (.classMem (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d))
          (synChwcn (synCvv))) (.classEq (.cv d) (synCfv (synC2nd)
            (synCop (synCin (.cv r) (synCxp (.cv d) (.cv d))) (.cv d)))))
      (synWrex u (synChwcn (synCvv)) (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      p0082 p0086
  have p0089 :=
    @gBiimpri (.classMem (.cv d) (synChwbases (synCvv)))
      (synWrex u (synChwcn (synCvv)) (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      p0000
  have p0090 :=
    @gSyl (synWbr (.cv r) (synCwe) (.cv d))
      (synWrex u (synChwcn (synCvv)) (.classEq (.cv d) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv d) (synChwbases (synCvv))) p0087 p0089
  have p0091 :=
    @gExlimiv (synWbr (.cv r) (synCwe) (.cv d))
      (.classMem (.cv d) (synChwbases (synCvv))) r dv_cache_0011 p0090
  have p0092 :=
    @gImpbii (.classMem (.cv d) (synChwbases (synCvv)))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d))) p0015 p0091
  exact p0092

/-- Checked nominal proof certificate identified upstream as `g_elhwcardswev`. -/
@[expose]
noncomputable def gElhwcardswev (k : Var) (s : Var) (d : Var) (dv_d_k : d ≠ k)
    (dv_d_s : d ≠ s) (dv_k_s : k ≠ s) :
    Nominal.NPrf
      (synWb (.classMem (.cv k) (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d))
              (.classEq (.cv k) (synCnc (.cv d))))))) :=
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
  have dv_cache_0001 : Disjoint ((synCvv)).fv ((Class.cv k)).fv := by
    exact
      (show Disjoint ((synCvv)).fv ((Class.cv k)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact (show Disjoint ((∅ : Finset Var)) (({ k } : Finset Var)) from (by simp))))
  have dv_cache_0002 : r ∉ ((synCvv)).fv :=
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
  have dv_cache_0005 : s ∉ ((Wff.classEq (.cv k) (synCnc (.cv r)))).fv :=
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
      ((synWex s (synWa (synWbr (.cv s) (synCwe) (.cv r))
            (.classEq (.cv k) (synCnc (.cv r)))))).fv :=
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
      ((synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
              (.classEq (.cv k) (synCnc (.cv d))))))).fv :=
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
  have dv_cache_0011 : r ∉ ((synWbr (.cv s) (synCwe) (.cv d))).fv :=
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
  have dv_cache_0014 : r ∉ ((synChwbases (synCvv))).fv :=
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
  have dv_cache_0015 : r ∉ ((Wff.classEq (.cv k) (synCnc (.cv d)))).fv :=
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
  have dv_cache_0016 : d ∉ ((Wff.classMem (.cv k) (synChwcards (synCvv)))).fv :=
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
  have dv_cache_0017 : s ∉ ((Wff.classMem (.cv k) (synChwcards (synCvv)))).fv :=
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
  have p0000 := @gVex k
  have p0001 :=
    @gElhwcards (synCvv) (.cv k) r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 :=
    @gBiimpi (.classMem (.cv k) (synChwcards (synCvv)))
      (synWrex r (synChwbases (synCvv)) (.classEq (.cv k) (synCnc (.cv r)))) p0001
  have p0003 := @gHwbaseswev s r dv_cache_0004
  have p0004 :=
    @gBiimpi (.classMem (.cv r) (synChwbases (synCvv)))
      (synWex s (synWbr (.cv s) (synCwe) (.cv r))) p0003
  have p0005 :=
    @gAdantr (.classMem (.cv r) (synChwbases (synCvv)))
      (synWex s (synWbr (.cv s) (synCwe) (.cv r))) (.classEq (.cv k) (synCnc (.cv r)))
      p0004
  have p0006 :=
    Nominal.ax1 (.classEq (.cv k) (synCnc (.cv r))) (synWbr (.cv s) (synCwe) (.cv r))
  have p0007 :=
    @gAlrimiv (.classEq (.cv k) (synCnc (.cv r)))
      (.imp (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r)))) s
      dv_cache_0005 p0006
  have p0008 :=
    @gExintrbi (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r))) s
  have p0009 :=
    @gSyl (.classEq (.cv k) (synCnc (.cv r)))
      (.all s (.imp (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r)))))
      (synWb (synWex s (synWbr (.cv s) (synCwe) (.cv r))) (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r))))))
      p0007 p0008
  have p0010 :=
    @gAdantl (.classEq (.cv k) (synCnc (.cv r)))
      (synWb (synWex s (synWbr (.cv s) (synCwe) (.cv r))) (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r))))))
      (.classMem (.cv r) (synChwbases (synCvv))) p0009
  have p0011 :=
    @gMpbid
      (synWa (.classMem (.cv r) (synChwbases (synCvv))) (.classEq (.cv k) (synCnc (.cv r))))
      (synWex s (synWbr (.cv s) (synCwe) (.cv r)))
      (synWex s
        (synWa (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r)))))
      p0005 p0010
  have p0012 := @gVex r
  have p0013 := @gId (.classEq (.cv d) (.cv r))
  have p0014 :=
    @gBreq2d (.classEq (.cv d) (.cv r)) (.cv d) (.cv r) (.cv s) (synCwe) p0013
  have p0016 := @gNceqd (.classEq (.cv d) (.cv r)) (.cv d) (.cv r) p0013
  have p0017 :=
    @gEqeq2d (.classEq (.cv d) (.cv r)) (synCnc (.cv d)) (synCnc (.cv r)) (.cv k) p0016
  have p0018 :=
    @gAnbi12d (.classEq (.cv d) (.cv r)) (synWbr (.cv s) (synCwe) (.cv d))
      (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv d)))
      (.classEq (.cv k) (synCnc (.cv r))) p0014 p0017
  have p0019 :=
    @gExbidv (.classEq (.cv d) (.cv r))
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (synWa (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r)))) s
      dv_cache_0006 p0018
  have p0020 :=
    @gSpcev
      (synWex s
        (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))))
      (synWex s
        (synWa (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r)))))
      d (.cv r) dv_cache_0007 dv_cache_0008 p0012 p0019
  have p0021 :=
    @gSyl
      (synWa (.classMem (.cv r) (synChwbases (synCvv))) (.classEq (.cv k) (synCnc (.cv r))))
      (synWex s
        (synWa (synWbr (.cv s) (synCwe) (.cv r)) (.classEq (.cv k) (synCnc (.cv r)))))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
      p0011 p0020
  have p0022 :=
    @gEx (.classMem (.cv r) (synChwbases (synCvv)))
      (.classEq (.cv k) (synCnc (.cv r)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
      p0021
  have p0023 :=
    @gRexlimiv (.classEq (.cv k) (synCnc (.cv r)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
      r (synChwbases (synCvv)) dv_cache_0009 p0022
  have p0024 :=
    @gSyl (.classMem (.cv k) (synChwcards (synCvv)))
      (synWrex r (synChwbases (synCvv)) (.classEq (.cv k) (synCnc (.cv r))))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
      p0002 p0023
  have p0025 :=
    @gSimpl (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))
  have p0026 := @gVex s
  have p0027 := @gId (.classEq (.cv r) (.cv s))
  have p0028 :=
    @gBreq1d (.classEq (.cv r) (.cv s)) (.cv r) (.cv s) (.cv d) (synCwe) p0027
  have p0029 :=
    @gSpcev (synWbr (.cv r) (synCwe) (.cv d)) (synWbr (.cv s) (synCwe) (.cv d)) r
      (.cv s) dv_cache_0010 dv_cache_0011 p0026 p0028
  have p0030 := @gHwbaseswev r d dv_cache_0012
  have p0031 :=
    @gBiimpri (.classMem (.cv d) (synChwbases (synCvv)))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d))) p0030
  have p0032 :=
    @gSyl (synWbr (.cv s) (synCwe) (.cv d))
      (synWex r (synWbr (.cv r) (synCwe) (.cv d)))
      (.classMem (.cv d) (synChwbases (synCvv))) p0029 p0031
  have p0033 :=
    @gSyl
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (synWbr (.cv s) (synCwe) (.cv d)) (.classMem (.cv d) (synChwbases (synCvv)))
      p0025 p0032
  have p0034 :=
    @gSimpr (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))
  have p0035 :=
    @gJca
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (.classMem (.cv d) (synChwbases (synCvv))) (.classEq (.cv k) (synCnc (.cv d)))
      p0033 p0034
  have p0036 := @gId (.classEq (.cv r) (.cv d))
  have p0037 := @gNceqd (.classEq (.cv r) (.cv d)) (.cv r) (.cv d) p0036
  have p0038 :=
    @gEqeq2d (.classEq (.cv r) (.cv d)) (synCnc (.cv r)) (synCnc (.cv d)) (.cv k) p0037
  have p0039 :=
    @gRspcev (.classEq (.cv k) (synCnc (.cv r))) (.classEq (.cv k) (synCnc (.cv d))) r
      (.cv d) (synChwbases (synCvv)) dv_cache_0013 dv_cache_0014 dv_cache_0015 p0038
  have p0040 :=
    @gSyl
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (synWa (.classMem (.cv d) (synChwbases (synCvv))) (.classEq (.cv k) (synCnc (.cv d))))
      (synWrex r (synChwbases (synCvv)) (.classEq (.cv k) (synCnc (.cv r)))) p0035
      p0039
  have p0043 :=
    @gBiimpri (.classMem (.cv k) (synChwcards (synCvv)))
      (synWrex r (synChwbases (synCvv)) (.classEq (.cv k) (synCnc (.cv r)))) p0001
  have p0044 :=
    @gSyl
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (synWrex r (synChwbases (synCvv)) (.classEq (.cv k) (synCnc (.cv r))))
      (.classMem (.cv k) (synChwcards (synCvv))) p0040 p0043
  have p0045 :=
    @gExlimivv
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (.classMem (.cv k) (synChwcards (synCvv))) d s dv_cache_0016 dv_cache_0017 p0044
  have p0046 :=
    @gImpbii (.classMem (.cv k) (synChwcards (synCvv)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
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

/-- Checked nominal proof certificate identified upstream as `g_hwcardslecanti`. -/
@[expose]
noncomputable def gHwcardslecanti (k : Var) (m : Var) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (.classMem (.cv m) (synChwcards (synCvv)))) (.imp
          (synWa (synWbr (.cv k) (synClec) (.cv m)) (synWbr (.cv m) (synClec) (.cv k)))
          (.classEq (.cv k) (.cv m)))) :=
  by
  have p0000 :=
    @gSimpl (.classMem (.cv k) (synChwcards (synCvv)))
      (.classMem (.cv m) (synChwcards (synCvv)))
  have p0001 := @gHwcardssnc (synCvv)
  have p0002 := @gSsel (synChwcards (synCvv)) (synCncs) (.cv k)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gSyl
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (.classMem (.cv m) (synChwcards (synCvv))))
      (.classMem (.cv k) (synChwcards (synCvv))) (.classMem (.cv k) (synCncs)) p0000
      p0003
  have p0005 :=
    @gSimpr (.classMem (.cv k) (synChwcards (synCvv)))
      (.classMem (.cv m) (synChwcards (synCvv)))
  have p0007 := @gSsel (synChwcards (synCvv)) (synCncs) (.cv m)
  have p0008 := Nominal.mp p0001 p0007
  have p0009 :=
    @gSyl
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (.classMem (.cv m) (synChwcards (synCvv))))
      (.classMem (.cv m) (synChwcards (synCvv))) (.classMem (.cv m) (synCncs)) p0005
      p0008
  have p0010 :=
    @gJca
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (.classMem (.cv m) (synChwcards (synCvv))))
      (.classMem (.cv k) (synCncs)) (.classMem (.cv m) (synCncs)) p0004 p0009
  have p0011 := @gSbth (.cv k) (.cv m)
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv k) (synChwcards (synCvv)))
        (.classMem (.cv m) (synChwcards (synCvv))))
      (synWa (.classMem (.cv k) (synCncs)) (.classMem (.cv m) (synCncs)))
      (.imp (synWa (synWbr (.cv k) (synClec) (.cv m)) (synWbr (.cv m) (synClec) (.cv k)))
        (.classEq (.cv k) (.cv m)))
      p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_wpporbitfnndv`. -/
@[expose]
noncomputable def gWpporbitfnndv (F : Class) (I : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWfn (synCfrec F I) (synCnnc))) :=
  by
  have p0000 := @gEqid (synCfrec F I)
  have p0001 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0002 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0003 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0004 :=
    @gFnfrec
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wpporbit0ndv`. -/
@[expose]
noncomputable def gWpporbit0ndv (F : Class) (I : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (.classEq (synCfv (synCfrec F I) (synC0c)) I)) :=
  by
  have p0000 := @gEqid (synCfrec F I)
  have p0001 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0002 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0003 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0004 :=
    @gFrec0
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wpporbitsucndv`. -/
@[expose]
noncomputable def gWpporbitsucndv (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.classEq (synCfv (synCfrec F I) (synCplc N (synC1c)))
          (synCfv F (synCfv (synCfrec F I) N)))) :=
  by
  have p0000 := @gEqid (synCfrec F I)
  have p0001 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0002 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0003 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem F (synCfuns)) p0001 p0002
  have p0005 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0006 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem I (synCdm F)) p0001 p0005
  have p0008 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0009 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWss (synCrn F) (synCdm F)) p0001 p0008
  have p0010 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0011 :=
    @gFrecsuc
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synCfrec F I) F I N p0000 p0003 p0006 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_lnwpwccore`. -/
@[expose]
noncomputable def gLnwpwccore (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv)
    (hyp_lnwpwccore_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_lnwpwccore_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnwpwccore_3 : Nominal.NPrf (.classMem (synCop R A) (synClnpwc A))) :
    Nominal.NPrf
      (synWa (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
          (synWbr R (synCconnex) A)) (synWss R (synCxp A A))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @gEllnpwcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnwpwccore_2 hyp_lnwpwccore_1
  have p0001 :=
    @gMpbi (.classMem (synCop R A) (synClnpwc A))
      (synWa (.classMem (synCop R A) (synClntpc A))
        (synWbr (synCdif R (synCcnv R)) (synCfound) A))
      hyp_lnwpwccore_3 p0000
  have p0002 :=
    @gSimpl (.classMem (synCop R A) (synClntpc A))
      (synWbr (synCdif R (synCcnv R)) (synCfound) A)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gEllntpcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnwpwccore_1 hyp_lnwpwccore_2
      hyp_lnwpwccore_1
  have p0005 :=
    @gMpbi (.classMem (synCop R A) (synClntpc A))
      (synWa (synWa (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
            (synWbr R (synCconnex) A)) (synWss R (synCxp A A))) (.classEq A A))
      p0003 p0004
  have p0006 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
          (synWbr R (synCconnex) A)) (synWss R (synCxp A A)))
      (.classEq A A)
  have p0007 := Nominal.mp p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_lnworigqordwe`. -/
@[expose]
noncomputable def gLnworigqordwe (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv)
    (hyp_lnworigqordwe_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_lnworigqordwe_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_lnworigqordwe_3 : Nominal.NPrf (.classMem (synCop R A) (synClnpwc A))) :
    Nominal.NPrf (synWbr (synClnqord R A) (synCwe) (synClnquo R A)) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @gPm32i (.classMem R (synCvv)) (.classMem A (synCvv)) hyp_lnworigqordwe_2
      hyp_lnworigqordwe_1
  have p0001 :=
    @gLnwpwccore A R dv_cache_0001 hyp_lnworigqordwe_1 hyp_lnworigqordwe_2
      hyp_lnworigqordwe_3
  have p0002 :=
    @gPm32i (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
          (synWbr R (synCconnex) A)) (synWss R (synCxp A A)))
      p0000 p0001
  have p0003 :=
    @gEllnpwcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnworigqordwe_2
      hyp_lnworigqordwe_1
  have p0004 :=
    @gBiimpi (.classMem (synCop R A) (synClnpwc A))
      (synWa (.classMem (synCop R A) (synClntpc A))
        (synWbr (synCdif R (synCcnv R)) (synCfound) A))
      p0003
  have p0005 := Nominal.mp hyp_lnworigqordwe_3 p0004
  have p0006 :=
    @gSimpr (.classMem (synCop R A) (synClntpc A))
      (synWbr (synCdif R (synCcnv R)) (synCfound) A)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i
      (synWa (synWa (.classMem R (synCvv)) (.classMem A (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) A) (synWbr R (synCtrans) A))
            (synWbr R (synCconnex) A)) (synWss R (synCxp A A))))
      (synWbr (synCdif R (synCcnv R)) (synCfound) A) p0002 p0007
  have p0009 := @gLnqordwe A R dv_cache_0001
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wppreachsucndv`. -/
@[expose]
noncomputable def gWppreachsucndv (C : Class) (F : Class) (N : Class)
    (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv)
    (dv_F_N : Disjoint F.fv N.fv)
    (hyp_wppreachsucndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (.classEq
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCplc N (synC1c))) (synCima (synCcnv F) (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N)))) :=
  by
  have dv_cache_0001 :
    Disjoint ((synCimage (synCcnv F))).fv ((synCima (synClec) (synCsn C))).fv := by
    exact
      (show Disjoint ((synCimage (synCcnv F))).fv ((synCima (synClec) (synCsn C))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show Disjoint (((synCcnv F)).fv) ((((synClec)).fv) ∪ (((synCsn C)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (((synCcnv F)).fv) (((synClec)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((synClec)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec];
                            exact
                              (show Disjoint ((F).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint (((synCcnv F)).fv) (((synCsn C)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                      exact
                        (show Disjoint ((F).fv) (((synCsn C)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                            exact
                              (show Disjoint (F).fv (C).fv from
                                (by exact dv_C_F.symm))))))⟩))))
  have dv_cache_0002 : Disjoint ((synCimage (synCcnv F))).fv (N).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((synCimage (synCcnv F))).fv (N).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage];
          exact
            (show Disjoint (((synCcnv F)).fv) ((N).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv];
                exact (show Disjoint (F).fv (N).fv from (by exact dv_F_N))))))
  have dv_cache_0003 : Disjoint ((synCima (synClec) (synCsn C))).fv (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((synCima (synClec) (synCsn C))).fv (N).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show Disjoint ((((synClec)).fv) ∪ (((synCsn C)).fv)) ((N).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((synClec)).fv) ((N).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec];
                      exact (show Disjoint ((∅ : Finset Var)) ((N).fv) from (by simp)))),
                  (show Disjoint (((synCsn C)).fv) ((N).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
                      exact (show Disjoint (C).fv (N).fv from (by exact dv_C_N))))⟩))))
  have p0000 := @gWppreachopfn F hyp_wppreachsucndv_1
  have p0001 := @gFnfun (synCvv) (synCimage (synCcnv F))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gCnvex F hyp_wppreachsucndv_1
  have p0004 := @gImageex (synCcnv F) p0003
  have p0005 := @gElfuns (synCimage (synCcnv F)) p0004
  have p0006 :=
    @gMpbir (.classMem (synCimage (synCcnv F)) (synCfuns))
      (synWfun (synCimage (synCcnv F))) p0002 p0005
  have p0007 := @gWppreachupperex C
  have p0009 := @gFndm (synCvv) (synCimage (synCcnv F))
  have p0010 := Nominal.mp p0000 p0009
  have p0011 :=
    @gEleqtrri (synCima (synClec) (synCsn C)) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0007 p0010
  have p0012 := @gSsv (synCrn (synCimage (synCcnv F)))
  have p0016 :=
    @gSseqtr4i (synCrn (synCimage (synCcnv F))) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0012 p0010
  have p0017 :=
    @gN3pm32i (.classMem (synCimage (synCcnv F)) (synCfuns))
      (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
      (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F))))
      p0006 p0011 p0016
  have p0018 :=
    @gA1i
      (synW3a (.classMem (synCimage (synCcnv F)) (synCfuns))
        (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
        (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F)))))
      (.classMem N (synCnnc)) p0017
  have p0019 := @gId (.classMem N (synCnnc))
  have p0020 :=
    @gJca (.classMem N (synCnnc))
      (synW3a (.classMem (synCimage (synCcnv F)) (synCfuns))
        (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
        (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F)))))
      (.classMem N (synCnnc)) p0018 p0019
  have p0021 :=
    @gWpporbitsuc (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)) N
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0022 :=
    @gSyl (.classMem N (synCnnc))
      (synWa (synW3a (.classMem (synCimage (synCcnv F)) (synCfuns))
          (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
          (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F)))))
        (.classMem N (synCnnc)))
      (.classEq (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCplc N (synC1c))) (synCfv (synCimage (synCcnv F))
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N)))
      p0020 p0021
  have p0024 :=
    @gFvex N (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0025 :=
    @gFvimagecl
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N)
      (synCcnv F) p0003 p0024
  have p0026 :=
    @gA1i
      (.classEq (synCfv (synCimage (synCcnv F))
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N))
        (synCima (synCcnv F)
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N)))
      (.classMem N (synCnnc)) p0025
  have p0027 :=
    @gEqtrd (.classMem N (synCnnc))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCplc N (synC1c)))
      (synCfv (synCimage (synCcnv F))
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N))
      (synCima (synCcnv F)
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) N))
      p0022 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_wpppredfamex`. -/
@[expose]
noncomputable def gWpppredfamex (C : Class) (F : Class)
    (hyp_wpppredfamex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpppredfam F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppredfam F C))
  have p0001 :=
    @gEqid (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0002 := @gCnvex F hyp_wpppredfamex_1
  have p0003 := @gImageex (synCcnv F) p0002
  have p0004 :=
    @gFrecex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)) p0001 p0003
  have p0005 := @gTcfnex
  have p0006 :=
    @gCoex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCtcfn) p0004 p0005
  have p0007 :=
    @gCnvex
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
      p0006
  have p0008 :=
    @gImageex
      (synCcnv
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))
      p0007
  have p0009 := @gSsetex
  have p0010 := @gImageex (synCsset) p0009
  have p0011 :=
    @gCoex
      (synCimage (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      (synCimage (synCsset)) p0008 p0010
  have p0012 :=
    @gEqeltri (synCwpppredfam F C)
      (synCcom (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCimage (synCsset)))
      (synCvv) p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_wppimagefun`. -/
@[expose]
noncomputable def gWppimagefun (R : Class) : Nominal.NPrf (synWfun (synCimage R)) :=
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
  have dv_cache_0001 : x ∉ ((synCimage R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCimage R)).fv :=
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
  have dv_cache_0003 : z ∉ ((synCimage R)).fv :=
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
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 := @gBrimage (.cv x) (.cv y) R p0000 p0001
  have p0004 := @gVex z
  have p0005 := @gBrimage (.cv x) (.cv z) R p0000 p0004
  have p0006 :=
    @gAnbi12i (synWbr (.cv x) (synCimage R) (.cv y))
      (.classEq (.cv y) (synCima R (.cv x))) (synWbr (.cv x) (synCimage R) (.cv z))
      (.classEq (.cv z) (synCima R (.cv x))) p0002 p0005
  have p0007 := @gEqtr3 (.cv y) (.cv z) (synCima R (.cv x))
  have p0008 :=
    @gSylbi
      (synWa (synWbr (.cv x) (synCimage R) (.cv y)) (synWbr (.cv x) (synCimage R) (.cv z)))
      (synWa (.classEq (.cv y) (synCima R (.cv x))) (.classEq (.cv z) (synCima R (.cv x))))
      (.classEq (.cv y) (.cv z)) p0006 p0007
  have p0009 := Nominal.gen p0008 z
  have p0010 := Nominal.gen p0009 y
  have p0011 := Nominal.gen p0010 x
  have p0012 :=
    @gDffun2 x y z (synCimage R) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0013_e01_recanon :
    Nominal.NPrf
      (synWb (synWfun (synCimage R)) (.all x (.all y (.all z (.imp
                (synWa (synWbr (.cv x) (synCimage R) (.cv y))
                  (synWbr (.cv x) (synCimage R) (.cv z))) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWfun synWss synCin synCcompl synCnin synWnan synWa
          synCcom synCopab synWex synCcnv synCid synCimage
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
    @gMpbir (synWfun (synCimage R))
      (.all x (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCimage R) (.cv y))
                (synWbr (.cv x) (synCimage R) (.cv z))) (.classEq (.cv y) (.cv z))))))
      p0011 p0013_e01_recanon
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wppimagefv`. -/
@[expose]
noncomputable def gWppimagefv (B : Class) (G : Class)
    (hyp_wppimagefv_1 : Nominal.NPrf (.classMem G (synCvv)))
    (hyp_wppimagefv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCimage G) B) (synCima G B)) :=
  by
  have p0000 := @gEqid (synCima G B)
  have p0001 := @gImaex G B hyp_wppimagefv_1 hyp_wppimagefv_2
  have p0002 := @gBrimage B (synCima G B) G hyp_wppimagefv_2 p0001
  have p0003 :=
    @gMpbir (synWbr B (synCimage G) (synCima G B))
      (.classEq (synCima G B) (synCima G B)) p0000 p0002
  have p0004 := @gWppimagefun G
  have p0005 := @gFunbrfv B (synCima G B) (synCimage G)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := Nominal.mp p0003 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppreachorbitfnndv`. -/
@[expose]
noncomputable def gWppreachorbitfnndv (C : Class) (F : Class)
    (hyp_wppreachorbitfnndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (synWfn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCnnc)) :=
  by
  have p0000 := @gCnvex F hyp_wppreachorbitfnndv_1
  have p0001 := @gWppimagefn (synCcnv F) p0000
  have p0002 := @gFnfun (synCvv) (synCimage (synCcnv F))
  have p0003 := Nominal.mp p0001 p0002
  have p0005 := @gImageex (synCcnv F) p0000
  have p0006 := @gElfuns (synCimage (synCcnv F)) p0005
  have p0007 :=
    @gMpbir (.classMem (synCimage (synCcnv F)) (synCfuns))
      (synWfun (synCimage (synCcnv F))) p0003 p0006
  have p0008 := @gLecex
  have p0009 := @gSnex C
  have p0010 := @gImaex (synClec) (synCsn C) p0008 p0009
  have p0013 := @gFndm (synCvv) (synCimage (synCcnv F))
  have p0014 := Nominal.mp p0001 p0013
  have p0015 :=
    @gEleqtrri (synCima (synClec) (synCsn C)) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0010 p0014
  have p0016 := @gSsv (synCrn (synCimage (synCcnv F)))
  have p0021 :=
    @gSseqtr4i (synCrn (synCimage (synCcnv F))) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0016 p0014
  have p0022 :=
    @gN3pm32i (.classMem (synCimage (synCcnv F)) (synCfuns))
      (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
      (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F))))
      p0007 p0015 p0021
  have p0023 :=
    @gWpporbitfnndv (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))
  have p0024 := Nominal.mp p0022 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_wpppredfamfv`. -/
@[expose]
noncomputable def gWpppredfamfv (C : Class) (D : Class) (F : Class)
    (hyp_wpppredfamfv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpppredfam F C) (synCsn (synCsn D))) (synCima (synCcnv
            (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (synCima (synCsset) (synCsn (synCsn D))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppredfam F C))
  have p0001 :=
    @gFveq1i (synCsn (synCsn D)) (synCwpppredfam F C)
      (synCcom (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCimage (synCsset)))
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
    @gFvco (synCsn (synCsn D))
      (synCimage (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      (synCimage (synCsset))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gEqtri (synCfv (synCwpppredfam F C) (synCsn (synCsn D)))
      (synCfv (synCcom (synCimage (synCcnv (synCcom
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtcfn)))) (synCimage (synCsset))) (synCsn (synCsn D)))
      (synCfv (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCfv (synCimage (synCsset)) (synCsn (synCsn D))))
      p0001 p0014
  have p0018 := @gWppimagefv (synCsn (synCsn D)) (synCsset) p0005 p0004
  have p0019 :=
    @gFveq2i (synCfv (synCimage (synCsset)) (synCsn (synCsn D)))
      (synCima (synCsset) (synCsn (synCsn D)))
      (synCimage (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      p0018
  have p0020 :=
    @gEqtri (synCfv (synCwpppredfam F C) (synCsn (synCsn D)))
      (synCfv (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCfv (synCimage (synCsset)) (synCsn (synCsn D))))
      (synCfv (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCima (synCsset) (synCsn (synCsn D))))
      p0015 p0019
  have p0021 :=
    @gEqid (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0022 := @gCnvex F hyp_wpppredfamfv_1
  have p0023 := @gImageex (synCcnv F) p0022
  have p0024 :=
    @gFrecex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)) p0021 p0023
  have p0025 := @gTcfnex
  have p0026 :=
    @gCoex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCtcfn) p0024 p0025
  have p0027 :=
    @gCnvex
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
      p0026
  have p0031 :=
    @gWppimagefv (synCima (synCsset) (synCsn (synCsn D)))
      (synCcnv
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))
      p0027 p0007
  have p0032 :=
    @gEqtri (synCfv (synCwpppredfam F C) (synCsn (synCsn D)))
      (synCfv (synCimage (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (synCima (synCsset) (synCsn (synCsn D))))
      (synCima (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))) (synCima (synCsset) (synCsn (synCsn D))))
      p0020 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_elwpppredfam`. -/
@[expose]
noncomputable def gElwpppredfam (C : Class) (D : Class) (F : Class) (q : Var)
    (hyp_elwpppredfam_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_elwpppredfam_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv q))
          (synCfv (synCwpppredfam F C) (synCsn (synCsn D)))) (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv q))))) :=
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
  have dv_cache_0005 :
    y ∉
      ((synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q)))).fv :=
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
      ((Wff.classMem D (synCfv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)) (synCsn (.cv q))))).fv :=
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
  have p0000 := @gWpppredfamfv C D F hyp_elwpppredfam_1
  have p0001 :=
    @gEleq2i (synCfv (synCwpppredfam F C) (synCsn (synCsn D)))
      (synCima (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))) (synCima (synCsset) (synCsn (synCsn D))))
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
  have p0007 := @gBrssetsn D (.cv z) hyp_elwpppredfam_2 p0006
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
      (synCcnv
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))
      p0014
  have p0016 :=
    @gEleq2i
      (synCima (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))) (synCima (synCsset) (synCsn (synCsn D))))
      (synCima (synCcnv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))) (.cab y (.classMem D (.cv y))))
      (synCsn (.cv q)) p0015
  have p0017 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCfv (synCwpppredfam F C) (synCsn (synCsn D))))
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (synCima (synCsset) (synCsn (synCsn D)))))
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (.cab y (.classMem D (.cv y)))))
      p0001 p0016
  have p0018 := @gWppreachorbitfnndv C F hyp_elwpppredfam_1
  have p0019 :=
    @gFnfun (synCnnc)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @gFntcfn
  have p0022 := @gFnfun (synC1c) (synCtcfn)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 :=
    @gPm32i
      (synWfun (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      (synWfun (synCtcfn)) p0020 p0023
  have p0025 :=
    @gFunco (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCtcfn)
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gFunfn
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
  have p0028 :=
    @gMpbi
      (synWfun
        (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))
      (synWfn (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)) (synCdm (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      p0026 p0027
  have p0029 :=
    @gElpreima
      (synCdm (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)))
      (synCsn (.cv q)) (.cab y (.classMem D (.cv y)))
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @gFvex (synCsn (.cv q))
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
  have p0032 :=
    @gId
      (.classEq (.cv y) (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))))
  have p0033 :=
    @gEleq2d
      (.classEq (.cv y) (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))))
      (.cv y)
      (synCfv (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)) (synCsn (.cv q)))
      D p0032
  have p0034 :=
    @gElab (.classMem D (.cv y))
      (.classMem D (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))))
      y
      (synCfv (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)) (synCsn (.cv q)))
      dv_cache_0005 dv_cache_0006 p0031 p0033
  have p0035 :=
    @gElfvdm D (synCsn (.cv q))
      (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtcfn))
  have p0036 :=
    @gSylbi
      (.classMem (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))) (.cab y (.classMem D (.cv y))))
      (.classMem D (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))))
      (.classMem (synCsn (.cv q)) (synCdm (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      p0034 p0035
  have p0037 :=
    @gPm471ri
      (.classMem (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))) (.cab y (.classMem D (.cv y))))
      (.classMem (synCsn (.cv q)) (synCdm (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtcfn))))
      p0036
  have p0038 :=
    @gBicomi
      (.classMem (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))) (.cab y (.classMem D (.cv y))))
      (synWa (.classMem (synCsn (.cv q)) (synCdm (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (.classMem (synCfv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)) (synCsn (.cv q))) (.cab y (.classMem D (.cv y)))))
      p0037
  have p0039 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (.cab y (.classMem D (.cv y)))))
      (synWa (.classMem (synCsn (.cv q)) (synCdm (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)))) (.classMem (synCfv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn)) (synCsn (.cv q))) (.cab y (.classMem D (.cv y)))))
      (.classMem (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))) (.cab y (.classMem D (.cv y))))
      p0030 p0038
  have p0044 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (.cab y (.classMem D (.cv y)))))
      (.classMem (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))) (.cab y (.classMem D (.cv y))))
      (.classMem D (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))))
      p0039 p0034
  have p0046 := @gVex q
  have p0047 := @gSnel1c (.cv q) p0046
  have p0048 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (.classMem (synCsn (.cv q)) (synC1c))
      p0021 p0047
  have p0049 :=
    @gFvco2 (synC1c) (synCsn (.cv q))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn)
  have p0050 := Nominal.mp p0048 p0049
  have p0052 := @gTcfnfv (.cv q) p0046
  have p0053 :=
    @gFveq2i (synCfv (synCtcfn) (synCsn (.cv q))) (synCtc (.cv q))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) p0052
  have p0054 :=
    @gEqtri
      (synCfv (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)) (synCsn (.cv q)))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCfv (synCtcfn) (synCsn (.cv q))))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (.cv q)))
      p0050 p0053
  have p0055 :=
    @gEleq2i
      (synCfv (synCcom (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtcfn)) (synCsn (.cv q)))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc (.cv q)))
      D p0054
  have p0056 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (.cab y (.classMem D (.cv y)))))
      (.classMem D (synCfv (synCcom
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) (synCtcfn))
          (synCsn (.cv q))))
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv q))))
      p0044 p0055
  have p0057 :=
    @gBitri
      (.classMem (synCsn (.cv q)) (synCfv (synCwpppredfam F C) (synCsn (synCsn D))))
      (.classMem (synCsn (.cv q)) (synCima (synCcnv (synCcom
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtcfn))) (.cab y (.classMem D (.cv y)))))
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv q))))
      p0017 p0056
  exact p0057

/-- Checked nominal proof certificate identified upstream as `g_wpppostcompex`. -/
@[expose]
noncomputable def gWpppostcompex (F : Class)
    (_hyp_wpppostcompex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpppostcomp F) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppostcomp F))
  have p0001 := @gComposeex
  have p0002 := @gVvex
  have p0003 := @gSnex F
  have p0004 := @gXpex (synCvv) (synCsn F) p0002 p0003
  have p0005 := @gIdex
  have p0006 := @gTxpex (synCxp (synCvv) (synCsn F)) (synCid) p0004 p0005
  have p0007 :=
    @gCoex (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) p0001
      p0006
  have p0008 :=
    @gEqeltri (synCwpppostcomp F)
      (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)))
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wppupperpreopex`. -/
@[expose]
noncomputable def gWppupperpreopex (C : Class) :
    Nominal.NPrf (.classMem (synCwppupperpreop C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppupperpreop C))
  have p0001 := @gLnimageopex
  have p0002 := @gSwapex
  have p0003 := @gImageex (synCswap) p0002
  have p0004 := @gVvex
  have p0005 := @gSnex (synCima (synClec) (synCsn C))
  have p0006 := @gXpex (synCvv) (synCsn (synCima (synClec) (synCsn C))) p0004 p0005
  have p0007 :=
    @gTxpex (synCimage (synCswap))
      (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))) p0003 p0006
  have p0008 :=
    @gCoex (synClnimageop)
      (synCtxp (synCimage (synCswap))
        (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C)))))
      p0001 p0007
  have p0009 :=
    @gEqeltri (synCwppupperpreop C)
      (synCcom (synClnimageop) (synCtxp (synCimage (synCswap))
          (synCxp (synCvv) (synCsn (synCima (synClec) (synCsn C))))))
      (synCvv) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wpppowlayerseqex`. -/
@[expose]
noncomputable def gWpppowlayerseqex (C : Class) (F : Class)
    (hyp_wpppowlayerseqex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpppowlayerseq F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowlayerseq F C))
  have p0001 := @gWppupperpreopex C
  have p0002 := @gEqid (synCfrec (synCwpppostcomp F) (synCid))
  have p0003 := @gWpppostcompex F hyp_wpppowlayerseqex_1
  have p0004 :=
    @gFrecex (synCfrec (synCwpppostcomp F) (synCid)) (synCwpppostcomp F) (synCid)
      p0002 p0003
  have p0005 := @gTcfnex
  have p0006 := @gCoex (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn) p0004 p0005
  have p0007 :=
    @gCoex (synCwppupperpreop C)
      (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)) p0001 p0006
  have p0008 :=
    @gEqeltri (synCwpppowlayerseq F C)
      (synCcom (synCwppupperpreop C)
        (synCcom (synCfrec (synCwpppostcomp F) (synCid)) (synCtcfn)))
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wpphitfamex`. -/
@[expose]
noncomputable def gWpphitfamex (C : Class) (F : Class)
    (hyp_wpphitfamex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpphitfam F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphitfam F C))
  have p0001 := @gWpppowlayerseqex C F hyp_wpphitfamex_1
  have p0002 := @gCnvex (synCwpppowlayerseq F C) p0001
  have p0003 := @gImageex (synCcnv (synCwpppowlayerseq F C)) p0002
  have p0004 := @gSsetex
  have p0005 := @gImageex (synCsset) p0004
  have p0006 :=
    @gCoex (synCimage (synCcnv (synCwpppowlayerseq F C))) (synCimage (synCsset))
      p0003 p0005
  have p0007 :=
    @gEqeltri (synCwpphitfam F C)
      (synCcom (synCimage (synCcnv (synCwpppowlayerseq F C))) (synCimage (synCsset)))
      (synCvv) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wpppostcompfn`. -/
@[expose]
noncomputable def gWpppostcompfn (F : Class)
    (hyp_wpppostcompfn_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (synWfn (synCwpppostcomp F) (synCvv)) :=
  by
  have p0000 := @gComposefn
  have p0001 := @gFnconstg (synCvv) F (synCvv)
  have p0002 := Nominal.mp hyp_wpppostcompfn_1 p0001
  have p0003 := @gF1ovi
  have p0004 := @gF1ofn (synCvv) (synCvv) (synCid)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i (synWfn (synCxp (synCvv) (synCsn F)) (synCvv))
      (synWfn (synCid) (synCvv)) p0002 p0005
  have p0007 := @gFntxp (synCvv) (synCvv) (synCxp (synCvv) (synCsn F)) (synCid)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gInidm (synCvv)
  have p0010 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) p0009
  have p0011 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) (synCvv)) p0008 p0010
  have p0012 :=
    @gFncovv (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)) p0000
      p0011
  have p0013 := (Nominal.classEqRefl (synCwpppostcomp F))
  have p0014 :=
    @gFneq1i (synCvv) (synCwpppostcomp F)
      (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid))) p0013
  have p0015 :=
    @gMpbir (synWfn (synCwpppostcomp F) (synCvv))
      (synWfn (synCcom (synCcompose) (synCtxp (synCxp (synCvv) (synCsn F)) (synCid)))
        (synCvv))
      p0012 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
