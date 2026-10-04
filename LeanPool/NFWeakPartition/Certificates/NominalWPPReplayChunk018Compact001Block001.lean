/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block022

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk018Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpowershiftndv`. -/
@[expose]
noncomputable def gCfbhncardpowershiftndv (A : Class)
    (hyp_cfbhncardpowershiftndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw1 A))) (synCtc (synChncard (synCpw A)))) :=
  by
  have p0000 := @gPwex A hyp_cfbhncardpowershiftndv_1
  have p0001 := @gHncardtcshiftndv (synCpw A) p0000
  have p0003 := @gPw1ex (synCpw A) p0000
  have p0004 := @gPw1ex A hyp_cfbhncardpowershiftndv_1
  have p0005 := @gPwex (synCpw1 A) p0004
  have p0006 := @gNcpwpw1 A hyp_cfbhncardpowershiftndv_1
  have p0007 :=
    @gEqcomi (synCnc (synCpw (synCpw1 A))) (synCnc (synCpw1 (synCpw A))) p0006
  have p0008 :=
    @gHncardnceqndv (synCpw1 (synCpw A)) (synCpw (synCpw1 A)) p0003 p0005 p0007
  have p0009 :=
    @gEqtri (synCtc (synChncard (synCpw A))) (synChncard (synCpw1 (synCpw A)))
      (synChncard (synCpw (synCpw1 A))) p0001 p0008
  have p0010 :=
    @gEqcomi (synCtc (synChncard (synCpw A))) (synChncard (synCpw (synCpw1 A)))
      p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_cfbtceqi`. -/
@[expose]
noncomputable def gCfbtceqi (A : Class) (B : Class)
    (hyp_cfbtceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCtc A) (synCtc B)) :=
  by
  have p0000 := @gTceq A B
  have p0001 := Nominal.mp hyp_cfbtceqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpw1ceqndv`. -/
@[expose]
noncomputable def gCfbhncardpw1ceqndv :
    Nominal.NPrf (.classEq (synChncard (synCpw (synC1c))) (synChncard (synC1c))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPwex (synC1c) p0000
  have p0003 := @gNcpw1c
  have p0004 := @gHncardnceqndv (synCpw (synC1c)) (synC1c) p0001 p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16stepndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synChncard (synCpw
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0004
  have p0006 :=
    @gCfbhncardpowershiftndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw15stepndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw15stepndv :
    Nominal.NPrf
      (.classEq (synChncard
          (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCtc
          (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  have p0005 :=
    @gCfbhncardpowershiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw14stepndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw14stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gCfbhncardpowershiftndv (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw13stepndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw13stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gCfbhncardpowershiftndv (synCpw1 (synCpw1 (synC1c))) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw12stepndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw12stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))
        (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gCfbhncardpowershiftndv (synCpw1 (synC1c)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw11stepndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw11stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw1 (synC1c))))
        (synCtc (synChncard (synCpw (synC1c))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gCfbhncardpowershiftndv (synC1c) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16to4ndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16to4ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synChncard
              (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw16stepndv
  have p0001 := @gCfbhncardpwpw15stepndv
  have p0002 :=
    @gTceq
      (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gEqtri
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synChncard
          (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw14step2tndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw14step2tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synChncard
              (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCtc
          (synCtc (synCtc
              (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw14stepndv
  have p0001 :=
    @gCfbtceqi
      (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0000
  have p0002 :=
    @gCfbtceqi
      (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw13step3tndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw13step3tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc
            (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw13stepndv
  have p0001 :=
    @gCfbtceqi (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))) p0000
  have p0002 :=
    @gCfbtceqi
      (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c))))))) p0001
  have p0003 :=
    @gCfbtceqi
      (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c))))))))
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw12step4tndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw12step4tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc
            (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw12stepndv
  have p0001 :=
    @gCfbtceqi (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))
      (synCtc (synChncard (synCpw (synCpw1 (synC1c))))) p0000
  have p0002 :=
    @gCfbtceqi (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))) p0001
  have p0003 :=
    @gCfbtceqi
      (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))))
      (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c))))))) p0002
  have p0004 :=
    @gCfbtceqi
      (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c))))))))
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw11step5tndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw11step5tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc
            (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw11stepndv
  have p0001 :=
    @gCfbtceqi (synChncard (synCpw (synCpw1 (synC1c))))
      (synCtc (synChncard (synCpw (synC1c)))) p0000
  have p0002 :=
    @gCfbtceqi (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))
      (synCtc (synCtc (synChncard (synCpw (synC1c))))) p0001
  have p0003 :=
    @gCfbtceqi (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c))))))
      (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c)))))) p0002
  have p0004 :=
    @gCfbtceqi (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))))
      (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c))))))) p0003
  have p0005 :=
    @gCfbtceqi
      (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c))))))))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16to3ndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16to3ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw16to4ndv
  have p0001 := @gCfbhncardpwpw14step2tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16to2ndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16to2ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw16to3ndv
  have p0001 := @gCfbhncardpwpw13step3tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16to1ndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16to1ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw16to2ndv
  have p0001 := @gCfbhncardpwpw12step4tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synChncard (synCpw (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16to0ndv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16to0ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c)))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw16to1ndv
  have p0001 := @gCfbhncardpwpw11step5tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c)))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardtc3forwardndv`. -/
@[expose]
noncomputable def gCfbhncardtc3forwardndv (A : Class)
    (hyp_cfbhncardtc3forwardndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synCtc (synChncard A))))
        (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord A)))))) :=
  by
  have p0000 := @gHncardtc2 A hyp_cfbhncardtc3forwardndv_1
  have p0001 :=
    @gCfbtceqi (synCtc (synCtc (synChncard A)))
      (synCnc (synCpw1 (synCpw1 (synChnord A)))) p0000
  have p0002 := @gHnordex A hyp_cfbhncardtc3forwardndv_1
  have p0003 := @gPw1ex (synChnord A) p0002
  have p0004 := @gPw1ex (synCpw1 (synChnord A)) p0003
  have p0005 := @gTcnc (synCpw1 (synCpw1 (synChnord A))) p0004
  have p0006 :=
    @gEqtri (synCtc (synCtc (synCtc (synChncard A))))
      (synCtc (synCnc (synCpw1 (synCpw1 (synChnord A)))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord A))))) p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardtc3ndv`. -/
@[expose]
noncomputable def gCfbhncardtc3ndv (A : Class)
    (hyp_cfbhncardtc3ndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord A)))))
        (synCtc (synCtc (synCtc (synChncard A))))) :=
  by
  have p0000 := @gCfbhncardtc3forwardndv A hyp_cfbhncardtc3ndv_1
  have p0001 :=
    @gEqcomi (synCtc (synCtc (synCtc (synChncard A))))
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord A))))) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpw1ceq6tndv`. -/
@[expose]
noncomputable def gCfbhncardpw1ceq6tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c))))))))) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) :=
  by
  have p0000 := @gCfbhncardpw1ceqndv
  have p0001 :=
    @gCfbtceqi (synChncard (synCpw (synC1c))) (synChncard (synC1c)) p0000
  have p0002 :=
    @gCfbtceqi (synCtc (synChncard (synCpw (synC1c))))
      (synCtc (synChncard (synC1c))) p0001
  have p0003 :=
    @gCfbtceqi (synCtc (synCtc (synChncard (synCpw (synC1c)))))
      (synCtc (synCtc (synChncard (synC1c)))) p0002
  have p0004 :=
    @gCfbtceqi (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c))))))
      (synCtc (synCtc (synCtc (synChncard (synC1c))))) p0003
  have p0005 :=
    @gCfbtceqi (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c)))))))
      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))) p0004
  have p0006 :=
    @gCfbtceqi
      (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpwpw16basendv`. -/
@[expose]
noncomputable def gCfbhncardpwpw16basendv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) :=
  by
  have p0000 := @gCfbhncardpwpw16to0ndv
  have p0001 := @gCfbhncardpw1ceq6tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw (synC1c)))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbsourceledgerndv`. -/
@[expose]
noncomputable def gCfbsourceledgerndv :
    Nominal.NPrf
      (.classEq (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) (synCtc
          (synCtc (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0004
  have p0006 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0005
  have p0007 :=
    @gPwex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0006
  have p0008 :=
    @gCfbhncardtc3ndv
      (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0007
  have p0009 := @gCfbhncardpwpw16basendv
  have p0010 :=
    @gCfbtceqi
      (synChncard (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      p0009
  have p0011 :=
    @gCfbtceqi
      (synCtc (synChncard (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      p0010
  have p0012 :=
    @gCfbtceqi
      (synCtc (synCtc (synChncard (synCpw (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      p0011
  have p0013 :=
    @gEqtri
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      p0008 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpw2enpw1shiftndv`. -/
@[expose]
noncomputable def gCfbhncardpw2enpw1shiftndv (Y : Class) (Z : Class)
    (hyp_cfbhncardpw2enpw1shiftndv_1 : Nominal.NPrf (.classMem Z (synCvv)))
    (hyp_cfbhncardpw2enpw1shiftndv_2 : Nominal.NPrf (.classMem Y (synCvv)))
    (hyp_cfbhncardpw2enpw1shiftndv_3 : Nominal.NPrf (synWbr Z (synCen) (synCpw1 Y))) :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw Z)))
        (synCtc (synChncard (synCpw (synCpw Y))))) :=
  by
  have p0000 := @gPwex Z hyp_cfbhncardpw2enpw1shiftndv_1
  have p0001 := @gPwex (synCpw Z) p0000
  have p0002 := @gPwex Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0003 := @gPwex (synCpw Y) p0002
  have p0004 := @gPw1ex (synCpw (synCpw Y)) p0003
  have p0005 := @gEnpw Z (synCpw1 Y)
  have p0006 := Nominal.mp hyp_cfbhncardpw2enpw1shiftndv_3 p0005
  have p0007 := @gEnpw1pw Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0008 := @gEnsymi (synCpw1 (synCpw Y)) (synCpw (synCpw1 Y))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gPm32i (synWbr (synCpw Z) (synCen) (synCpw (synCpw1 Y)))
      (synWbr (synCpw (synCpw1 Y)) (synCen) (synCpw1 (synCpw Y))) p0006 p0009
  have p0011 := @gEntr (synCpw Z) (synCpw (synCpw1 Y)) (synCpw1 (synCpw Y))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gEnpw (synCpw Z) (synCpw1 (synCpw Y))
  have p0014 := Nominal.mp p0012 p0013
  have p0016 := @gEnpw1pw (synCpw Y) p0002
  have p0017 :=
    @gEnsymi (synCpw1 (synCpw (synCpw Y))) (synCpw (synCpw1 (synCpw Y)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gPm32i (synWbr (synCpw (synCpw Z)) (synCen) (synCpw (synCpw1 (synCpw Y))))
      (synWbr (synCpw (synCpw1 (synCpw Y))) (synCen) (synCpw1 (synCpw (synCpw Y))))
      p0014 p0018
  have p0020 :=
    @gEntr (synCpw (synCpw Z)) (synCpw (synCpw1 (synCpw Y)))
      (synCpw1 (synCpw (synCpw Y)))
  have p0021 := Nominal.mp p0019 p0020
  have p0024 := @gEqnc (synCpw (synCpw Z)) (synCpw1 (synCpw (synCpw Y))) p0001
  have p0025 :=
    @gMpbir
      (.classEq (synCnc (synCpw (synCpw Z))) (synCnc (synCpw1 (synCpw (synCpw Y)))))
      (synWbr (synCpw (synCpw Z)) (synCen) (synCpw1 (synCpw (synCpw Y)))) p0021
      p0024
  have p0026 :=
    @gHncardnceqndv (synCpw (synCpw Z)) (synCpw1 (synCpw (synCpw Y))) p0001 p0004
      p0025
  have p0029 := @gHncardtcshiftndv (synCpw (synCpw Y)) p0003
  have p0030 :=
    @gEqcomi (synCtc (synChncard (synCpw (synCpw Y))))
      (synChncard (synCpw1 (synCpw (synCpw Y)))) p0029
  have p0031 :=
    @gEqtri (synChncard (synCpw (synCpw Z)))
      (synChncard (synCpw1 (synCpw (synCpw Y))))
      (synCtc (synChncard (synCpw (synCpw Y)))) p0026 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_cfbtccli`. -/
@[expose]
noncomputable def gCfbtccli (A : Class)
    (hyp_cfbtccli_1 : Nominal.NPrf (.classMem A (synCncs))) :
    Nominal.NPrf (.classMem (synCtc A) (synCncs)) :=
  by
  have p0000 := @gTccl A
  have p0001 := Nominal.mp hyp_cfbtccli_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbtargetqbaseexndv`. -/
@[expose]
noncomputable def gCfbtargetqbaseexndv :
    Nominal.NPrf
      (.classMem (synCpw (synCpw (synChnord (synCpw1 (synC1c))))) (synCvv)) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gHnordex (synCpw1 (synC1c)) p0001
  have p0003 := @gPwex (synChnord (synCpw1 (synC1c))) p0002
  have p0004 := @gPwex (synCpw (synChnord (synCpw1 (synC1c)))) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbtargetqncndv`. -/
@[expose]
noncomputable def gCfbtargetqncndv :
    Nominal.NPrf
      (.classMem (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))
        (synCncs)) :=
  by
  have p0000 := @gCfbtargetqbaseexndv
  have p0001 := @gHncardnc (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbt6hncard1ncndv`. -/
@[expose]
noncomputable def gCfbt6hncard1ncndv :
    Nominal.NPrf
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synCncs)) :=
  by
  have p0000 := @gHncardnc1ndv
  have p0001 := @gCfbtccli (synChncard (synC1c)) p0000
  have p0002 := @gCfbtccli (synCtc (synChncard (synC1c))) p0001
  have p0003 := @gCfbtccli (synCtc (synCtc (synChncard (synC1c)))) p0002
  have p0004 := @gCfbtccli (synCtc (synCtc (synCtc (synChncard (synC1c))))) p0003
  have p0005 :=
    @gCfbtccli (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))) p0004
  have p0006 :=
    @gCfbtccli (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbt2targetqncndv`. -/
@[expose]
noncomputable def gCfbt2targetqncndv :
    Nominal.NPrf
      (.classMem (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
        (synCncs)) :=
  by
  have p0000 := @gCfbtargetqncndv
  have p0001 :=
    @gCfbtccli (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))) p0000
  have p0002 :=
    @gCfbtccli
      (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockcancel3ndv`. -/
@[expose]
noncomputable def gCfbfixedblockcancel3ndv :
    Nominal.NPrf
      (.imp (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard
                      (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))) (synWbr
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCtc (synCtc
              (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbt6hncard1ncndv
  have p0001 := @gCfbt2targetqncndv
  have p0002 :=
    @gTc3lecan
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockouterhartogsndv`. -/
@[expose]
noncomputable def gCfbfixedblockouterhartogsndv (R : Class)
    (hyp_cfbfixedblockouterhartogsndv_1 : Nominal.NPrf (synWbr R (synCwe)
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :
    Nominal.NPrf
      (synWbr (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) :=
  by
  have p0000 := @gHncardsuccshiftedndv R hyp_cfbfixedblockouterhartogsndv_1
  have p0001 := @gWppconcrete6fntc7hncard1valndv
  have p0002 :=
    @gBreqtrri
      (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      (synChncard (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synClec) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockpointimpndv`. -/
@[expose]
noncomputable def gCfbfixedblockpointimpndv (R : Class)
    (hyp_cfbfixedblockpointimpndv_1 : Nominal.NPrf (synWbr R (synCwe)
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :
    Nominal.NPrf
      (.imp (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCtc (synCtc
              (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))) (synWbr
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbfixedblockouterhartogsndv R hyp_cfbfixedblockpointimpndv_1
  have p0001 := @gCfbt6hncard1ncndv
  have p0002 := @gCfbt2targetqncndv
  have p0003 := @gWppconcrete6tcvalncndv
  have p0004 :=
    @gLectr
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
  have p0005 :=
    @gMp3an
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synCncs))
      (.classMem (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
        (synCncs))
      (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synCncs))
      (.imp (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCtc (synCtc
                (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))) (synWbr
            (synCtc (synCtc
                (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) (synClec)
            (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))
        (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))
      p0001 p0002 p0003 p0004
  have p0006 :=
    @gMpan2
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbhnordpw1shiftensymndv`. -/
@[expose]
noncomputable def gCfbhnordpw1shiftensymndv (A : Class)
    (hyp_cfbhnordpw1shiftensymndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWbr (synChnord (synCpw1 A)) (synCen) (synCpw1 (synChnord A))) :=
  by
  have p0000 := @gHnordpw1shiftenndv A hyp_cfbhnordpw1shiftensymndv_1
  have p0001 := @gEnsym (synCpw1 (synChnord A)) (synChnord (synCpw1 A))
  have p0002 :=
    @gMpbi (synWbr (synCpw1 (synChnord A)) (synCen) (synChnord (synCpw1 A)))
      (synWbr (synChnord (synCpw1 A)) (synCen) (synCpw1 (synChnord A))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbhncardpw2hnordpw1shiftndv`. -/
@[expose]
noncomputable def gCfbhncardpw2hnordpw1shiftndv (A : Class)
    (hyp_cfbhncardpw2hnordpw1shiftndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1 A)))))
        (synCtc (synChncard (synCpw (synCpw (synChnord A)))))) :=
  by
  have p0000 := @gPw1ex A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0001 := @gHnordex (synCpw1 A) p0000
  have p0002 := @gHnordex A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0003 := @gCfbhnordpw1shiftensymndv A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0004 :=
    @gCfbhncardpw2enpw1shiftndv (synChnord A) (synChnord (synCpw1 A)) p0001 p0002
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget6stepndv`. -/
@[expose]
noncomputable def gCfbtarget6stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synChncard (synCpw (synCpw (synChnord (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0004
  have p0006 :=
    @gCfbhncardpw2hnordpw1shiftndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget5stepndv`. -/
@[expose]
noncomputable def gCfbtarget5stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) (synCtc
          (synChncard (synCpw (synCpw
                (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  have p0005 :=
    @gCfbhncardpw2hnordpw1shiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget4stepndv`. -/
@[expose]
noncomputable def gCfbtarget4stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw
            (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
        (synCtc (synChncard (synCpw
              (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 :=
    @gCfbhncardpw2hnordpw1shiftndv (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget3stepndv`. -/
@[expose]
noncomputable def gCfbtarget3stepndv :
    Nominal.NPrf
      (.classEq (synChncard
          (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCtc
          (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c))))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gCfbhncardpw2hnordpw1shiftndv (synCpw1 (synCpw1 (synC1c))) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget2stepndv`. -/
@[expose]
noncomputable def gCfbtarget2stepndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))
        (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gCfbhncardpw2hnordpw1shiftndv (synCpw1 (synC1c)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget5step1tndv`. -/
@[expose]
noncomputable def gCfbtarget5step1tndv :
    Nominal.NPrf
      (.classEq (synCtc (synChncard (synCpw (synCpw (synChnord
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget5stepndv
  have p0001 :=
    @gCfbtceqi
      (synChncard (synCpw (synCpw (synChnord
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synCtc (synChncard (synCpw (synCpw
              (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget4step2tndv`. -/
@[expose]
noncomputable def gCfbtarget4step2tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synChncard (synCpw (synCpw
                  (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (synCtc (synCtc (synCtc (synChncard (synCpw (synCpw
                    (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget4stepndv
  have p0001 :=
    @gCfbtceqi
      (synChncard (synCpw
          (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synChncard
          (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0000
  have p0002 :=
    @gCfbtceqi
      (synCtc (synChncard (synCpw (synCpw
              (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synCtc (synCtc (synChncard
            (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget3step3tndv`. -/
@[expose]
noncomputable def gCfbtarget3step3tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synCtc (synChncard (synCpw
                  (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (synCtc (synCtc (synCtc (synCtc (synChncard (synCpw
                    (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget3stepndv
  have p0001 :=
    @gCfbtceqi
      (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c))))))))
      p0000
  have p0002 :=
    @gCfbtceqi
      (synCtc (synChncard
          (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))))
      p0001
  have p0003 :=
    @gCfbtceqi
      (synCtc (synCtc (synChncard
            (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synCtc (synCtc (synCtc (synChncard
              (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c))))))))))
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget2step4tndv`. -/
@[expose]
noncomputable def gCfbtarget2step4tndv :
    Nominal.NPrf
      (.classEq (synCtc (synCtc (synCtc (synCtc (synChncard
                  (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synChncard
                    (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget2stepndv
  have p0001 :=
    @gCfbtceqi
      (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))
      (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))) p0000
  have p0002 :=
    @gCfbtceqi
      (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c))))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      p0001
  have p0003 :=
    @gCfbtceqi
      (synCtc (synCtc
          (synChncard (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))
      p0002
  have p0004 :=
    @gCfbtceqi
      (synCtc (synCtc (synCtc (synChncard
              (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c))))))))))
      (synCtc (synCtc (synCtc (synCtc
              (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))))
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget6to4ndv`. -/
@[expose]
noncomputable def gCfbtarget6to4ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget6stepndv
  have p0001 := @gCfbtarget5step1tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synChncard (synCpw (synCpw (synChnord
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw
                (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget6to3ndv`. -/
@[expose]
noncomputable def gCfbtarget6to3ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synCtc (synCtc (synChncard (synCpw (synCpw
                    (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget6to4ndv
  have p0001 := @gCfbtarget4step2tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synChncard (synCpw (synCpw
                (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc (synChncard (synCpw
                (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbtarget6to2ndv`. -/
@[expose]
noncomputable def gCfbtarget6to2ndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synCtc (synCtc (synCtc (synChncard (synCpw
                    (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget6to3ndv
  have p0001 := @gCfbtarget3step3tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc (synChncard (synCpw
                (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc (synCtc (synChncard
                (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbtargethncardledgerndv`. -/
@[expose]
noncomputable def gCfbtargethncardledgerndv :
    Nominal.NPrf
      (.classEq (synChncard (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synChncard
                    (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbtarget6to2ndv
  have p0001 := @gCfbtarget2step4tndv
  have p0002 :=
    @gEqtri
      (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc (synCtc (synChncard
                (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc
                (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbtargetledgerndv`. -/
@[expose]
noncomputable def gCfbtargetledgerndv :
    Nominal.NPrf
      (.classEq (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard
                    (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))) :=
  by
  have p0000 :=
    (Nominal.classEqRefl (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
  have p0001 :=
    @gEqcomi
      (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      p0000
  have p0002 := @gCfbtargethncardledgerndv
  have p0003 :=
    @gEqtri
      (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synChncard (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc
                (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockledgercmpndv`. -/
@[expose]
noncomputable def gCfbfixedblockledgercmpndv :
    Nominal.NPrf
      (synWb (synWbr (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
          (synClec) (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) (synWbr
          (synCtc (synCtc (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard
                      (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))))))) :=
  by
  have p0000 := @gCfbsourceledgerndv
  have p0001 := @gCfbtargetledgerndv
  have p0002 :=
    @gBreq12i
      (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc
                (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))))
      (synClec) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockledgercmpdndv`. -/
@[expose]
noncomputable def gCfbfixedblockledgercmpdndv
    (hyp_cfbfixedblockledgercmpdndv_1 : Nominal.NPrf (.imp (synWwpp) (synWbr (synCnc
              (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
            (synClec) (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard
                      (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))))))) :=
  by
  have p0000 := @gCfbfixedblockledgercmpndv
  have p0001 :=
    @gSylib (synWwpp)
      (synWbr (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) (synClec)
        (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard
                    (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))))))
      hyp_cfbfixedblockledgercmpdndv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockcancelleddndv`. -/
@[expose]
noncomputable def gCfbfixedblockcancelleddndv
    (hyp_cfbfixedblockcancelleddndv_1 : Nominal.NPrf (.imp (synWwpp) (synWbr (synCnc
              (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
            (synClec) (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCtc (synCtc
              (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))) :=
  by
  have p0000 := @gCfbfixedblockledgercmpdndv hyp_cfbfixedblockcancelleddndv_1
  have p0001 := @gCfbfixedblockcancel3ndv
  have p0002 :=
    @gSyl (synWwpp)
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard
                    (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as
`g_cfbfixedblockf6pointfromnclendv`.
-/
@[expose]
noncomputable def gCfbfixedblockf6pointfromnclendv (R : Class)
    (hyp_cfbfixedblockf6pointfromnclendv_1 : Nominal.NPrf (.imp (synWwpp) (synWbr (synCnc
              (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
            (synClec) (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))))
    (hyp_cfbfixedblockf6pointfromnclendv_2 : Nominal.NPrf (synWbr R (synCwe)
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbfixedblockcancelleddndv hyp_cfbfixedblockf6pointfromnclendv_1
  have p0001 := @gCfbfixedblockpointimpndv R hyp_cfbfixedblockf6pointfromnclendv_2
  have p0002 :=
    @gSyl (synWwpp)
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cfbpw16oneexndv`. -/
@[expose]
noncomputable def gCfbpw16oneexndv :
    Nominal.NPrf
      (.classMem (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCvv)) :=
  by
  have p0000 := @gN1cex
  have p0001 := @gPw1ex (synC1c) p0000
  have p0002 := @gPw1ex (synCpw1 (synC1c)) p0001
  have p0003 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0004
  have p0006 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblocksourceexndv`. -/
@[expose]
noncomputable def gCfbfixedblocksourceexndv :
    Nominal.NPrf
      (.classMem (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (synCvv)) :=
  by
  have p0000 := @gCfbpw16oneexndv
  have p0001 :=
    @gPwex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0000
  have p0002 :=
    @gHnordex
      (synCpw (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0001
  have p0003 :=
    @gPw1ex
      (synChnord (synCpw
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0002
  have p0004 :=
    @gPw1ex
      (synCpw1 (synChnord (synCpw
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0003
  have p0005 :=
    @gPw1ex
      (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblocktargetexndv`. -/
@[expose]
noncomputable def gCfbfixedblocktargetexndv :
    Nominal.NPrf
      (.classMem (synChnord (synCpw (synCpw (synChnord (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (synCvv)) :=
  by
  have p0000 := @gCfbpw16oneexndv
  have p0001 :=
    @gHnordex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0000
  have p0002 :=
    @gPwex
      (synChnord (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0001
  have p0003 :=
    @gPwex
      (synCpw (synChnord
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0002
  have p0004 :=
    @gHnordex
      (synCpw (synCpw (synChnord
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cfbnclefrominjimpndv`. -/
@[expose]
noncomputable def gCfbnclefrominjimpndv (A : Class) (B : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv)
    (hyp_cfbnclefrominjimpndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_cfbnclefrominjimpndv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWex f (synWf1 (.cv f) A B)) (synWbr (synCnc A) (synClec) (synCnc B))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_f, not_false_eq_true])
  have p0000 :=
    @gNclenc A B f dv_cache_0001 dv_cache_0002 hyp_cfbnclefrominjimpndv_1
      hyp_cfbnclefrominjimpndv_2
  have p0001 :=
    @gBiimpri (synWbr (synCnc A) (synClec) (synCnc B))
      (synWex f (synWf1 (.cv f) A B)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblocknclefrominjndv`. -/
@[expose]
noncomputable def gCfbfixedblocknclefrominjndv (f : Var)
    (hyp_cfbfixedblocknclefrominjndv_1 : Nominal.NPrf (.imp (synWwpp) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw
                      (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
          (synClec) (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))) :=
  by
  have dv_cache_0001 :
    f ∉
      ((synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 :
    f ∉
      ((synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @gCfbfixedblocksourceexndv
  have p0001 := @gCfbfixedblocktargetexndv
  have p0002 :=
    @gCfbnclefrominjimpndv
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synChnord (synCpw (synCpw (synChnord (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      f dv_cache_0001 dv_cache_0002 p0000 p0001
  have p0003 :=
    @gSyl (synWwpp)
      (synWex f (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synWbr (synCnc (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1 (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) (synClec)
        (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
      hyp_cfbfixedblocknclefrominjndv_1 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockf6pointfrominjndv`. -/
@[expose]
noncomputable def gCfbfixedblockf6pointfrominjndv (R : Class) (f : Var)
    (hyp_cfbfixedblockf6pointfrominjndv_1 : Nominal.NPrf (.imp (synWwpp) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))))
    (hyp_cfbfixedblockf6pointfrominjndv_2 : Nominal.NPrf (synWbr R (synCwe)
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))) :=
  by
  have p0000 := @gCfbfixedblocknclefrominjndv f hyp_cfbfixedblockf6pointfrominjndv_1
  have p0001 :=
    @gCfbfixedblockf6pointfromnclendv R p0000 hyp_cfbfixedblockf6pointfrominjndv_2
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk018Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as
`g_cfbfixedblockf6pointfrominjnowendv`.
-/
@[expose]
noncomputable def gCfbfixedblockf6pointfrominjnowendv (f : Var)
    (hyp_cfbfixedblockf6pointfrominjnowendv_1 : Nominal.NPrf (.imp (synWwpp) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))) :=
  by
  have dv_cache_0001 :
    Disjoint ((synCpw (synCpw (synChnord (synCpw1 (synC1c)))))).fv
      ((synChncodecmpset (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))).fv :=
    by
    exact
      (show Disjoint ((synCpw (synCpw (synChnord (synCpw1 (synC1c)))))).fv
          ((synChncodecmpset (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset];
          exact
            (show
              Disjoint (((synCpw (synChnord (synCpw1 (synC1c))))).fv)
                (((synCpw (synCpw (synChnord (synCpw1 (synC1c)))))).fv)
              from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
                exact
                  (show
                    Disjoint (((synChnord (synCpw1 (synC1c)))).fv)
                      (((synCpw (synCpw (synChnord (synCpw1 (synC1c)))))).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord];
                      exact
                        (show
                          Disjoint (((synCpw1 (synC1c))).fv)
                            (((synCpw (synCpw (synChnord (synCpw1 (synC1c)))))).fv)
                          from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                            exact
                              (show
                                Disjoint (((synC1c)).fv)
                                  (((synCpw
                                      (synCpw (synChnord (synCpw1 (synC1c)))))).fv)
                                from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
                                  exact
                                    (show
                                      Disjoint ((∅ : Finset Var))
                                        (((synCpw
                                            (synCpw
                                              (synChnord (synCpw1 (synC1c)))))).fv)
                                      from (by simp))))))))))))
  have p0000 := @gCfbtargetqbaseexndv
  have p0002 := @gHncodecmpsetexg (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))
  have p0003 := Nominal.mp p0000 p0002
  have p0005 := @gHncodecmplnpwcndv (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))
  have p0006 := Nominal.mp p0000 p0005
  have p0008 := @gHncodecmplnkerndv (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))
  have p0009 := Nominal.mp p0000 p0008
  have p0010 :=
    @gHnordwefromcmp (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))
      (synChncodecmpset (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))
      dv_cache_0001 p0000 p0003 p0006 p0009
  have p0011 :=
    @gCfbfixedblockf6pointfrominjndv
      (synClnqord (synChncodecmpset (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))
        (synChwcn (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
      f hyp_cfbfixedblockf6pointfrominjnowendv_1 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblocknotwppfrominjndv`. -/
@[expose]
noncomputable def gCfbfixedblocknotwppfrominjndv (f : Var)
    (hyp_cfbfixedblocknotwppfrominjndv_1 : Nominal.NPrf (.imp (synWwpp) (synWex f
            (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synChnord (synCpw (synCpw (synChnord (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))))) :
    Nominal.NPrf (.neg (synWwpp)) :=
  by
  have p0000 :=
    @gCfbfixedblockf6pointfrominjnowendv f hyp_cfbfixedblocknotwppfrominjndv_1
  have p0001 := @gWppconcrete6notwppfrompointndv p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cfbthresholdnn2lencndv`. -/
@[expose]
noncomputable def gCfbthresholdnn2lencndv (X : Class)
    (hyp_cfbthresholdnn2lencndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbthresholdnn2lencndv_2 :
      Nominal.NPrf (synWbr (synCnc (synCnnc)) (synClec) (synCnc X))) :
    Nominal.NPrf
      (synWbr (synCnc (synCnnc)) (synClec) (synCnc (synCpw1 (synCpw1 X)))) :=
  by
  have p0000 := @gNncex
  have p0001 := @gNcelncsi (synCnnc) p0000
  have p0002 := @gNcelncsi X hyp_cfbthresholdnn2lencndv_1
  have p0003 :=
    @gPm32i (.classMem (synCnc (synCnnc)) (synCncs))
      (.classMem (synCnc X) (synCncs)) p0001 p0002
  have p0004 := @gTlecg (synCnc (synCnnc)) (synCnc X)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gMpbi (synWbr (synCnc (synCnnc)) (synClec) (synCnc X))
      (synWbr (synCtc (synCnc (synCnnc))) (synClec) (synCtc (synCnc X)))
      hyp_cfbthresholdnn2lencndv_2 p0005
  have p0009 := @gTccl (synCnc (synCnnc))
  have p0010 := Nominal.mp p0001 p0009
  have p0012 := @gTccl (synCnc X)
  have p0013 := Nominal.mp p0002 p0012
  have p0014 :=
    @gPm32i (.classMem (synCtc (synCnc (synCnnc))) (synCncs))
      (.classMem (synCtc (synCnc X)) (synCncs)) p0010 p0013
  have p0015 := @gTlecg (synCtc (synCnc (synCnnc))) (synCtc (synCnc X))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gMpbi (synWbr (synCtc (synCnc (synCnnc))) (synClec) (synCtc (synCnc X)))
      (synWbr (synCtc (synCtc (synCnc (synCnnc)))) (synClec)
        (synCtc (synCtc (synCnc X))))
      p0006 p0016
  have p0019 := @gTc2nc (synCnnc) p0000
  have p0020 := @gTcnnf1o
  have p0021 := @gTcfnex
  have p0023 := @gPw1ex (synCnnc) p0000
  have p0024 := @gResex (synCtcfn) (synCpw1 (synCnnc)) p0021 p0023
  have p0025 :=
    @gF1oen (synCpw1 (synCnnc)) (synCnnc) (synCres (synCtcfn) (synCpw1 (synCnnc)))
      p0024
  have p0026 := Nominal.mp p0020 p0025
  have p0027 := @gEnpw1 (synCpw1 (synCnnc)) (synCnnc)
  have p0028 :=
    @gMpbi (synWbr (synCpw1 (synCnnc)) (synCen) (synCnnc))
      (synWbr (synCpw1 (synCpw1 (synCnnc))) (synCen) (synCpw1 (synCnnc))) p0026
      p0027
  have p0036 :=
    @gPm32i (synWbr (synCpw1 (synCpw1 (synCnnc))) (synCen) (synCpw1 (synCnnc)))
      (synWbr (synCpw1 (synCnnc)) (synCen) (synCnnc)) p0028 p0026
  have p0037 := @gEntr (synCpw1 (synCpw1 (synCnnc))) (synCpw1 (synCnnc)) (synCnnc)
  have p0038 := Nominal.mp p0036 p0037
  have p0041 := @gPw1ex (synCpw1 (synCnnc)) p0023
  have p0042 := @gEqnc (synCpw1 (synCpw1 (synCnnc))) (synCnnc) p0041
  have p0043 :=
    @gMpbir (.classEq (synCnc (synCpw1 (synCpw1 (synCnnc)))) (synCnc (synCnnc)))
      (synWbr (synCpw1 (synCpw1 (synCnnc))) (synCen) (synCnnc)) p0038 p0042
  have p0044 :=
    @gEqtri (synCtc (synCtc (synCnc (synCnnc))))
      (synCnc (synCpw1 (synCpw1 (synCnnc)))) (synCnc (synCnnc)) p0019 p0043
  have p0045 := @gTc2nc X hyp_cfbthresholdnn2lencndv_1
  have p0046 :=
    @gBreq12i (synCtc (synCtc (synCnc (synCnnc)))) (synCnc (synCnnc))
      (synCtc (synCtc (synCnc X))) (synCnc (synCpw1 (synCpw1 X))) (synClec) p0044
      p0045
  have p0047 :=
    @gMpbi
      (synWbr (synCtc (synCtc (synCnc (synCnnc)))) (synClec)
        (synCtc (synCtc (synCnc X))))
      (synWbr (synCnc (synCnnc)) (synClec) (synCnc (synCpw1 (synCpw1 X)))) p0017
      p0046
  exact p0047

/-- Checked nominal proof certificate identified upstream as `g_cfbliteralunivhncardboundndv`. -/
@[expose]
noncomputable def gCfbliteralunivhncardboundndv :
    Nominal.NPrf
      (synWbr (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
        (synClec) (synChncard (synCpw1 (synCpw1 (synCvv))))) :=
  by
  have p0000 := @gVvex
  have p0001 := @gPw1ex (synCvv) p0000
  have p0002 := @gPw1ex (synCpw1 (synCvv)) p0001
  have p0003 := @gNcelncsi (synCpw1 (synCpw1 (synCvv))) p0002
  have p0004 := @gNncex
  have p0005 := @gNcelncsi (synCnnc) p0004
  have p0010 :=
    @gN3pm32i (.classMem (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCncs))
      (.classMem (synCnc (synCnnc)) (synCncs))
      (.classMem (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCncs)) p0003 p0005 p0003
  have p0012 := @gSsv (synCnnc)
  have p0015 := @gNclec (synCnnc) (synCvv) p0004 p0000
  have p0016 := Nominal.mp p0012 p0015
  have p0017 := @gCfbthresholdnn2lencndv (synCvv) p0000 p0016
  have p0018 :=
    @gPm32i
      (synW3a (.classMem (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCncs))
        (.classMem (synCnc (synCnnc)) (synCncs))
        (.classMem (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCncs)))
      (synWbr (synCnc (synCnnc)) (synClec) (synCnc (synCpw1 (synCpw1 (synCvv)))))
      p0010 p0017
  have p0019 :=
    @gLemuc2 (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCnc (synCnnc))
      (synCnc (synCpw1 (synCpw1 (synCvv))))
  have p0020 := Nominal.mp p0018 p0019
  have p0022 := @gWppqkrelliteralnceqndv (synCvv) p0000
  have p0023 := @gXpvv
  have p0024 := @gPw1eq (synCxp (synCvv) (synCvv)) (synCvv)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gPw1eq (synCpw1 (synCxp (synCvv) (synCvv))) (synCpw1 (synCvv))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @gXpeq1i (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv))))
      (synCpw1 (synCpw1 (synCvv))) (synCnnc) p0027
  have p0029 :=
    @gNceqi (synCxp (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))) (synCnnc))
      (synCxp (synCpw1 (synCpw1 (synCvv))) (synCnnc)) p0028
  have p0030 :=
    @gEqtri (synCnc (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
      (synCnc (synCxp (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))) (synCnnc)))
      (synCnc (synCxp (synCpw1 (synCpw1 (synCvv))) (synCnnc))) p0022 p0029
  have p0035 := @gMucnc (synCpw1 (synCpw1 (synCvv))) (synCnnc) p0002 p0004
  have p0036 :=
    @gEqcomi
      (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc) (synCnc (synCnnc)))
      (synCnc (synCxp (synCpw1 (synCpw1 (synCvv))) (synCnnc))) p0035
  have p0037 :=
    @gEqtri (synCnc (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
      (synCnc (synCxp (synCpw1 (synCpw1 (synCvv))) (synCnnc)))
      (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc) (synCnc (synCnnc)))
      p0030 p0036
  have p0044 :=
    @gMucnc (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))) p0002 p0002
  have p0047 := @gPw1xpshiftenndv (synCvv) (synCvv) p0000 p0000
  have p0048 :=
    @gEnpw1 (synCpw1 (synCxp (synCvv) (synCvv)))
      (synCxp (synCpw1 (synCvv)) (synCpw1 (synCvv)))
  have p0049 :=
    @gMpbi
      (synWbr (synCpw1 (synCxp (synCvv) (synCvv))) (synCen)
        (synCxp (synCpw1 (synCvv)) (synCpw1 (synCvv))))
      (synWbr (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))) (synCen)
        (synCpw1 (synCxp (synCpw1 (synCvv)) (synCpw1 (synCvv)))))
      p0047 p0048
  have p0054 := @gPw1xpshiftenndv (synCpw1 (synCvv)) (synCpw1 (synCvv)) p0001 p0001
  have p0055 :=
    @gPm32i
      (synWbr (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))) (synCen)
        (synCpw1 (synCxp (synCpw1 (synCvv)) (synCpw1 (synCvv)))))
      (synWbr (synCpw1 (synCxp (synCpw1 (synCvv)) (synCpw1 (synCvv)))) (synCen)
        (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))))
      p0049 p0054
  have p0056 :=
    @gEntr (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv))))
      (synCpw1 (synCxp (synCpw1 (synCvv)) (synCpw1 (synCvv))))
      (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
  have p0057 := Nominal.mp p0055 p0056
  have p0058 :=
    @gEnsym (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv))))
      (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
  have p0059 :=
    @gMpbi
      (synWbr (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))) (synCen)
        (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))))
      (synWbr (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCen) (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))))
      p0057 p0058
  have p0065 :=
    @gBreq2i (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv))))
      (synCpw1 (synCpw1 (synCvv)))
      (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))) (synCen)
      p0027
  have p0066 :=
    @gMpbi
      (synWbr (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCen) (synCpw1 (synCpw1 (synCxp (synCvv) (synCvv)))))
      (synWbr (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCen) (synCpw1 (synCpw1 (synCvv))))
      p0059 p0065
  have p0073 :=
    @gXpex (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))) p0002 p0002
  have p0074 :=
    @gEqnc (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
      (synCpw1 (synCpw1 (synCvv))) p0073
  have p0075 :=
    @gMpbir
      (.classEq (synCnc
          (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))))
        (synCnc (synCpw1 (synCpw1 (synCvv)))))
      (synWbr (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCen) (synCpw1 (synCpw1 (synCvv))))
      p0066 p0074
  have p0076 :=
    @gEqtri
      (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc)
        (synCnc (synCpw1 (synCpw1 (synCvv)))))
      (synCnc (synCxp (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))))
      (synCnc (synCpw1 (synCpw1 (synCvv)))) p0044 p0075
  have p0077 :=
    @gEqcomi
      (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc)
        (synCnc (synCpw1 (synCpw1 (synCvv)))))
      (synCnc (synCpw1 (synCpw1 (synCvv)))) p0076
  have p0078 :=
    @gBreq12i (synCnc (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
      (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc) (synCnc (synCnnc)))
      (synCnc (synCpw1 (synCpw1 (synCvv))))
      (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc)
        (synCnc (synCpw1 (synCpw1 (synCvv)))))
      (synClec) p0037 p0077
  have p0079 :=
    @gMpbir
      (synWbr (synCnc (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))) (synClec)
        (synCnc (synCpw1 (synCpw1 (synCvv)))))
      (synWbr
        (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc) (synCnc (synCnnc)))
        (synClec) (synCo (synCnc (synCpw1 (synCpw1 (synCvv)))) (synCmuc)
          (synCnc (synCpw1 (synCpw1 (synCvv))))))
      p0020 p0078
  have p0082 := @gXpkex (synCvv) (synCvv) p0000 p0000
  have p0084 := @gXpex (synCxpk (synCvv) (synCvv)) (synCnnc) p0082 p0004
  have p0088 :=
    @gHncardnclecndv (synCpw1 (synCpw1 (synCvv)))
      (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)) p0084 p0002
  have p0089 := Nominal.mp p0079 p0088
  exact p0089


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk018Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbliteralp17hncardboundndv`. -/
@[expose]
noncomputable def gCfbliteralp17hncardboundndv :
    Nominal.NPrf
      (synWbr (synChncard (synCxp (synCxpk (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
            (synCnnc))) (synClec) (synCtc (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))) :=
  by
  have p0000 := @gCfbliteralunivhncardboundndv
  have p0001 := @gVvex
  have p0003 := @gXpkex (synCvv) (synCvv) p0001 p0001
  have p0004 := @gNncex
  have p0005 := @gXpex (synCxpk (synCvv) (synCvv)) (synCnnc) p0003 p0004
  have p0006 := @gHncardnc (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))
  have p0007 := Nominal.mp p0005 p0006
  have p0009 := @gPw1ex (synCvv) p0001
  have p0010 := @gPw1ex (synCpw1 (synCvv)) p0009
  have p0011 := @gHncardnc (synCpw1 (synCpw1 (synCvv)))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gPm32i
      (.classMem (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))) (synCncs))
      (.classMem (synChncard (synCpw1 (synCpw1 (synCvv)))) (synCncs)) p0007 p0012
  have p0014 :=
    @gTlecg (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
      (synChncard (synCpw1 (synCpw1 (synCvv))))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gMpbi
      (synWbr (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
        (synClec) (synChncard (synCpw1 (synCpw1 (synCvv)))))
      (synWbr (synCtc (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))))
        (synClec) (synCtc (synChncard (synCpw1 (synCpw1 (synCvv))))))
      p0000 p0015
  have p0022 :=
    @gHncardtcshiftndv (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)) p0005
  have p0028 := @gPw1ex (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)) p0005
  have p0033 := @gXpkex (synCpw1 (synCvv)) (synCpw1 (synCvv)) p0009 p0009
  have p0035 :=
    @gXpex (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc) p0033 p0004
  have p0037 := @gWpplitshiftenndv (synCvv) p0001
  have p0044 :=
    @gEqnc (synCpw1 (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)) p0028
  have p0045 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))))
        (synCnc (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))))
      (synWbr (synCpw1 (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))) (synCen)
        (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
      p0037 p0044
  have p0046 :=
    @gHncardnceqndv (synCpw1 (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)) p0028
      p0035 p0045
  have p0047 :=
    @gEqtri (synCtc (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))))
      (synChncard (synCpw1 (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
      p0022 p0046
  have p0051 := @gHncardtcshiftndv (synCpw1 (synCpw1 (synCvv))) p0010
  have p0052 :=
    @gBreq12i (synCtc (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCvv)))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synClec) p0047 p0051
  have p0053 :=
    @gMpbi
      (synWbr (synCtc (synChncard (synCxp (synCxpk (synCvv) (synCvv)) (synCnnc))))
        (synClec) (synCtc (synChncard (synCpw1 (synCpw1 (synCvv))))))
      (synWbr (synChncard
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
        (synClec) (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0016 p0052
  have p0061 :=
    @gHncardnc (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))
  have p0062 := Nominal.mp p0035 p0061
  have p0066 := @gPw1ex (synCpw1 (synCpw1 (synCvv))) p0010
  have p0067 := @gHncardnc (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0068 := Nominal.mp p0066 p0067
  have p0069 :=
    @gPm32i
      (.classMem (synChncard
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))) (synCncs))
      (.classMem (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCncs))
      p0062 p0068
  have p0070 :=
    @gTlecg
      (synChncard (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @gMpbi
      (synWbr (synChncard
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
        (synClec) (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWbr (synCtc (synChncard
            (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))))
        (synClec) (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      p0053 p0071
  have p0080 :=
    @gHncardtcshiftndv
      (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)) p0035
  have p0088 :=
    @gPw1ex (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))
      p0035
  have p0095 :=
    @gXpkex (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))) p0010 p0010
  have p0097 :=
    @gXpex (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
      (synCnnc) p0095 p0004
  have p0100 := @gWpplitshiftenndv (synCpw1 (synCvv)) p0009
  have p0109 :=
    @gEqnc
      (synCpw1 (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCnnc))
      p0088
  have p0110 :=
    @gMpbir
      (.classEq (synCnc (synCpw1
            (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))) (synCnc
          (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc))))
      (synWbr (synCpw1
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))) (synCen)
        (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
          (synCnnc)))
      p0100 p0109
  have p0111 :=
    @gHncardnceqndv
      (synCpw1 (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCnnc))
      p0088 p0097 p0110
  have p0112 :=
    @gEqtri
      (synCtc (synChncard
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))))
      (synChncard (synCpw1
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))))
      (synChncard (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
          (synCnnc)))
      p0080 p0111
  have p0117 := @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCvv)))) p0066
  have p0118 :=
    @gBreq12i
      (synCtc (synChncard
          (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))))
      (synChncard (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
          (synCnnc)))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synClec) p0112
      p0117
  have p0119 :=
    @gMpbi
      (synWbr (synCtc (synChncard
            (synCxp (synCxpk (synCpw1 (synCvv)) (synCpw1 (synCvv))) (synCnnc))))
        (synClec) (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      (synWbr (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc)))
        (synClec) (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      p0072 p0118
  have p0129 :=
    @gHncardnc
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCnnc))
  have p0130 := Nominal.mp p0097 p0129
  have p0135 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCvv)))) p0066
  have p0136 := @gHncardnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
  have p0137 := Nominal.mp p0135 p0136
  have p0138 :=
    @gPm32i
      (.classMem (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc))) (synCncs))
      (.classMem (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCncs))
      p0130 p0137
  have p0139 :=
    @gTlecg
      (synChncard (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
          (synCnnc)))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
  have p0140 := Nominal.mp p0138 p0139
  have p0141 :=
    @gMpbi
      (synWbr (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc)))
        (synClec) (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
              (synCnnc)))) (synClec)
        (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0119 p0140
  have p0151 :=
    @gHncardtcshiftndv
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCnnc))
      p0097
  have p0161 :=
    @gPw1ex
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
        (synCnnc))
      p0097
  have p0170 :=
    @gXpkex (synCpw1 (synCpw1 (synCpw1 (synCvv))))
      (synCpw1 (synCpw1 (synCpw1 (synCvv)))) p0066 p0066
  have p0172 :=
    @gXpex
      (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
        (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCnnc) p0170 p0004
  have p0176 := @gWpplitshiftenndv (synCpw1 (synCpw1 (synCvv))) p0010
  have p0187 :=
    @gEqnc
      (synCpw1 (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
          (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
          (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))
      p0161
  have p0188 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
              (synCnnc)))) (synCnc (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))))
      (synWbr (synCpw1 (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc))) (synCen) (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
            (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))
      p0176 p0187
  have p0189 :=
    @gHncardnceqndv
      (synCpw1 (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
          (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
          (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))
      p0161 p0172 p0188
  have p0190 :=
    @gEqtri
      (synCtc (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc))))
      (synChncard (synCpw1 (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
            (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))
      p0151 p0189
  have p0196 :=
    @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) p0135
  have p0197 :=
    @gBreq12i
      (synCtc (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
            (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
            (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      (synClec) p0190 p0196
  have p0198 :=
    @gMpbi
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv))))
              (synCnnc)))) (synClec)
        (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synWbr (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))) (synClec)
        (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0141 p0197
  have p0210 :=
    @gHncardnc
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
          (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))
  have p0211 := Nominal.mp p0172 p0210
  have p0217 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) p0135
  have p0218 :=
    @gHncardnc (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
  have p0219 := Nominal.mp p0217 p0218
  have p0220 :=
    @gPm32i
      (.classMem (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))) (synCncs))
      (.classMem (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
        (synCncs))
      p0211 p0219
  have p0221 :=
    @gTlecg
      (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
            (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
  have p0222 := Nominal.mp p0220 p0221
  have p0223 :=
    @gMpbi
      (synWbr (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))) (synClec)
        (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
                (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))) (synClec) (synCtc
          (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      p0198 p0222
  have p0235 :=
    @gHncardtcshiftndv
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
          (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))
      p0172
  have p0247 :=
    @gPw1ex
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
          (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))
      p0172
  have p0258 :=
    @gXpkex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) p0135 p0135
  have p0260 :=
    @gXpex
      (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synCnnc) p0258 p0004
  have p0265 := @gWpplitshiftenndv (synCpw1 (synCpw1 (synCpw1 (synCvv)))) p0066
  have p0278 :=
    @gEqnc
      (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
            (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))
      p0247
  have p0279 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
                (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))) (synCnc (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))))
      (synWbr (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))) (synCen) (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))
      p0265 p0278
  have p0280 :=
    @gHncardnceqndv
      (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
            (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))
      p0247 p0260 p0279
  have p0281 :=
    @gEqtri
      (synCtc (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))))
      (synChncard (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))
      p0235 p0280
  have p0288 :=
    @gHncardtcshiftndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0217
  have p0289 :=
    @gBreq12i
      (synCtc (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
              (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))
      (synCtc (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synClec) p0281 p0288
  have p0290 :=
    @gMpbi
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCvv))))
                (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCnnc)))) (synClec) (synCtc
          (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synWbr (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))) (synClec)
        (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      p0223 p0289
  have p0304 :=
    @gHncardnc
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))
  have p0305 := Nominal.mp p0260 p0304
  have p0312 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) p0217
  have p0313 :=
    @gHncardnc
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
  have p0314 := Nominal.mp p0312 p0313
  have p0315 :=
    @gPm32i
      (.classMem (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))) (synCncs))
      (.classMem (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
        (synCncs))
      p0305 p0314
  have p0316 :=
    @gTlecg
      (synChncard (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
  have p0317 := Nominal.mp p0315 p0316
  have p0318 :=
    @gMpbi
      (synWbr (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))) (synClec)
        (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))) (synClec)
        (synCtc (synChncard
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
      p0290 p0317
  have p0332 :=
    @gHncardtcshiftndv
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))
      p0260
  have p0346 :=
    @gPw1ex
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))
      p0260
  have p0359 :=
    @gXpkex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) p0217 p0217
  have p0361 :=
    @gXpex
      (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      (synCnnc) p0359 p0004
  have p0367 :=
    @gWpplitshiftenndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) p0135
  have p0382 :=
    @gEqnc
      (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))
      p0346
  have p0383 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))) (synCnc
          (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
      (synWbr (synCpw1 (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))) (synCen)
        (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
      p0367 p0382
  have p0384 :=
    @gHncardnceqndv
      (synCpw1 (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))
      p0346 p0361 p0383
  have p0385 :=
    @gEqtri
      (synCtc (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))))
      (synChncard (synCpw1 (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))))
      (synChncard (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
      p0332 p0384
  have p0393 :=
    @gHncardtcshiftndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) p0312
  have p0394 :=
    @gBreq12i
      (synCtc (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc))))
      (synChncard (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
      (synCtc (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synChncard (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synClec) p0385 p0393
  have p0395 :=
    @gMpbi
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) (synCnnc)))) (synClec)
        (synCtc (synChncard
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
      (synWbr (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
        (synClec) (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
      p0318 p0394
  have p0411 :=
    @gHncardnc
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))
  have p0412 := Nominal.mp p0361 p0411
  have p0420 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      p0312
  have p0421 :=
    @gHncardnc
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
  have p0422 := Nominal.mp p0420 p0421
  have p0423 :=
    @gPm32i
      (.classMem (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
        (synCncs))
      (.classMem (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
        (synCncs))
      p0412 p0422
  have p0424 :=
    @gTlecg
      (synChncard (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
      (synChncard (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
  have p0425 := Nominal.mp p0423 p0424
  have p0426 :=
    @gMpbi
      (synWbr (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
        (synClec) (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
        (synClec) (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      p0395 p0425
  have p0442 :=
    @gHncardtcshiftndv
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))
      p0361
  have p0458 :=
    @gPw1ex
      (synCxp (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))
      p0361
  have p0473 :=
    @gXpkex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) p0312
      p0312
  have p0475 :=
    @gXpex
      (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synCnnc) p0473 p0004
  have p0482 :=
    @gWpplitshiftenndv (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0217
  have p0499 :=
    @gEqnc
      (synCpw1 (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
        (synCnnc))
      p0458
  have p0500 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
        (synCnc (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))))
      (synWbr (synCpw1 (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
        (synCen) (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCnnc)))
      p0482 p0499
  have p0501 :=
    @gHncardnceqndv
      (synCpw1 (synCxp
          (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc)))
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
        (synCnnc))
      p0458 p0475 p0500
  have p0502 :=
    @gEqtri
      (synCtc (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
      (synChncard (synCpw1 (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
      (synChncard (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCnnc)))
      p0442 p0501
  have p0503 :=
    @gBreq1i
      (synCtc (synChncard (synCxp
            (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
      (synChncard (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCnnc)))
      (synCtc (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
      (synClec) p0502
  have p0504 :=
    @gMpbi
      (synWbr (synCtc (synChncard (synCxp
              (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCnnc))))
        (synClec) (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      (synWbr (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))) (synClec) (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      p0426 p0503
  have p0522 :=
    @gHncardnc
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
        (synCnnc))
  have p0523 := Nominal.mp p0475 p0522
  have p0534 :=
    @gTccl
      (synChncard (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
  have p0535 := Nominal.mp p0422 p0534
  have p0536 :=
    @gPm32i
      (.classMem (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))) (synCncs))
      (.classMem (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))) (synCncs))
      p0523 p0535
  have p0537 :=
    @gTlecg
      (synChncard (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCnnc)))
      (synCtc (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
  have p0538 := Nominal.mp p0536 p0537
  have p0539 :=
    @gMpbi
      (synWbr (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))) (synClec) (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      (synWbr (synCtc (synChncard (synCxp (synCxpk (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
              (synCnnc)))) (synClec) (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))))
      p0504 p0538
  have p0557 :=
    @gHncardtcshiftndv
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
        (synCnnc))
      p0475
  have p0575 :=
    @gPw1ex
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
        (synCnnc))
      p0475
  have p0592 :=
    @gXpkex
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0420 p0420
  have p0594 :=
    @gXpex
      (synCxpk (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synCnnc) p0592 p0004
  have p0602 :=
    @gWpplitshiftenndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) p0312
  have p0621 :=
    @gEqnc
      (synCpw1 (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCnnc)))
      (synCxp (synCxpk (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
        (synCnnc))
      p0575
  have p0622 :=
    @gMpbir
      (.classEq (synCnc (synCpw1 (synCxp (synCxpk (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
              (synCnnc)))) (synCnc (synCxp (synCxpk (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
            (synCnnc))))
      (synWbr (synCpw1 (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))) (synCen) (synCxp (synCxpk (synCpw1
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))) (synCnnc)))
      p0602 p0621
  have p0623 :=
    @gHncardnceqndv
      (synCpw1 (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCnnc)))
      (synCxp (synCxpk (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
        (synCnnc))
      p0575 p0594 p0622
  have p0624 :=
    @gEqtri
      (synCtc (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))))
      (synChncard (synCpw1 (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))) (synCnnc)))
      p0557 p0623
  have p0625 :=
    @gBreq1i
      (synCtc (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCnnc))))
      (synChncard (synCxp (synCxpk (synCpw1
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))) (synCnnc)))
      (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      (synClec) p0624
  have p0626 :=
    @gMpbi
      (synWbr (synCtc (synChncard (synCxp (synCxpk (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))) (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
              (synCnnc)))) (synClec) (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))))
      (synWbr (synChncard (synCxp (synCxpk (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
            (synCnnc))) (synClec) (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))))
      p0539 p0625
  exact p0626


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk018Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbliteralp16onehncardboundndv`. -/
@[expose]
noncomputable def gCfbliteralp16onehncardboundndv :
    Nominal.NPrf
      (synWbr (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCnnc))) (synClec) (synCtc (synCtc (synChncard (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))) :=
  by
  have p0000 := @gCfbliteralp17hncardboundndv
  have p0001 := @gN1cex
  have p0002 := @gPw1ex (synC1c) p0001
  have p0003 := @gPw1ex (synCpw1 (synC1c)) p0002
  have p0004 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0004
  have p0006 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0005
  have p0007 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0006
  have p0015 :=
    @gXpkex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0007
      p0007
  have p0016 := @gNncex
  have p0017 :=
    @gXpex
      (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCnnc) p0015 p0016
  have p0018 := @gVvex
  have p0019 := @gPw1ex (synCvv) p0018
  have p0020 := @gPw1ex (synCpw1 (synCvv)) p0019
  have p0021 := @gPw1ex (synCpw1 (synCpw1 (synCvv))) p0020
  have p0022 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCvv)))) p0021
  have p0023 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) p0022
  have p0024 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))) p0023
  have p0025 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
      p0024
  have p0034 :=
    @gXpkex
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0025 p0025
  have p0036 :=
    @gXpex
      (synCxpk (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synCnnc) p0034 p0016
  have p0037 := @gDf1c2
  have p0038 := @gPw1eq (synC1c) (synCpw1 (synCvv))
  have p0039 := Nominal.mp p0037 p0038
  have p0040 := @gPw1eq (synCpw1 (synC1c)) (synCpw1 (synCpw1 (synCvv)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @gPw1eq (synCpw1 (synCpw1 (synC1c))) (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @gPw1eq (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
  have p0045 := Nominal.mp p0043 p0044
  have p0046 :=
    @gPw1eq (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @gPw1eq (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @gXpkeq12i
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0049 p0049
  have p0064 :=
    @gXpeq1i
      (synCxpk (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCxpk (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
      (synCnnc) p0063
  have p0065 :=
    @gNceqi
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCnnc))
      (synCxp (synCxpk (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
        (synCnnc))
      p0064
  have p0066 :=
    @gHncardnceqndv
      (synCxp (synCxpk
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCnnc))
      (synCxp (synCxpk (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
          (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
        (synCnnc))
      p0017 p0036 p0065
  have p0067 :=
    @gEqcomi
      (synChncard (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCnnc)))
      (synChncard (synCxp (synCxpk (synCpw1
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))) (synCnnc)))
      p0066
  have p0096 :=
    @gNceqi (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0049
  have p0097 :=
    @gHncardnceqndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
      p0007 p0025 p0096
  have p0098 :=
    @gTceq
      (synChncard (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synChncard (synCpw1
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
  have p0099 := Nominal.mp p0097 p0098
  have p0100 :=
    @gTceq
      (synCtc (synChncard
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCtc (synChncard (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))
  have p0101 := Nominal.mp p0099 p0100
  have p0102 :=
    @gEqcomi
      (synCtc (synCtc (synChncard
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      p0101
  have p0103 :=
    @gBreq12i
      (synChncard (synCxp (synCxpk (synCpw1
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))
            (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))) (synCnnc)))
      (synChncard (synCxp (synCxpk
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCnnc)))
      (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))))
      (synCtc (synCtc (synChncard
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synClec) p0067 p0102
  have p0104 :=
    @gMpbi
      (synWbr (synChncard (synCxp (synCxpk (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))) (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))))))
            (synCnnc))) (synClec) (synCtc (synCtc (synChncard (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))))))))
      (synWbr (synChncard (synCxp (synCxpk
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCnnc))) (synClec) (synCtc (synCtc (synChncard (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0000 p0103
  exact p0104

/-- Checked nominal proof certificate identified upstream as `g_cfbfixedblockhnqgraphexndv`. -/
@[expose]
noncomputable def gCfbfixedblockhnqgraphexndv (X : Class)
    (hyp_cfbfixedblockhnqgraphexndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.classMem (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))) (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))) (synCvv)) :=
  by
  have p0000 := @gHnordex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0001 := @gPwex (synChnord X) p0000
  have p0002 := @gPwex (synCpw (synChnord X)) p0001
  have p0003 := @gPwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0004 := @gPw1ex (synCpw X) p0003
  have p0005 := @gPw1ex (synCpw1 (synCpw X)) p0004
  have p0006 := @gPw1ex (synCpw1 (synCpw1 (synCpw X))) p0005
  have p0010 :=
    @gUnex (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
      (synCpw (synCpw (synChnord X))) p0006 p0002
  have p0011 :=
    @gPm32i (.classMem (synCpw (synCpw (synChnord X))) (synCvv))
      (.classMem (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))) (synCvv))
      p0002 p0010
  have p0012 :=
    @gHnqincexg
      (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) (synCpw (synCpw (synChnord X))))
      (synCpw (synCpw (synChnord X)))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gCnvex
      (synChnqinc (synCpw (synCpw (synChnord X)))
        (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))))
      p0013
  have p0027 :=
    @gPm32i (.classMem (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) (synCvv))
      (.classMem (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))) (synCvv))
      p0006 p0010
  have p0028 :=
    @gHnqincexg
      (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X)))) (synCpw (synCpw (synChnord X))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
  have p0029 := Nominal.mp p0027 p0028
  have p0033 := @gHnsiquomapexgndv (synCpw1 (synCpw1 (synCpw X)))
  have p0034 := Nominal.mp p0005 p0033
  have p0037 := @gHnsiquomapexgndv (synCpw1 (synCpw X))
  have p0038 := Nominal.mp p0004 p0037
  have p0039 := @gSiex (synChnsiquomap (synCpw1 (synCpw X))) p0038
  have p0041 := @gHnsiquomapexgndv (synCpw X)
  have p0042 := Nominal.mp p0003 p0041
  have p0043 := @gSiex (synChnsiquomap (synCpw X)) p0042
  have p0044 := @gSiex (synCsi (synChnsiquomap (synCpw X))) p0043
  have p0045 :=
    @gCoex (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
      (synCsi (synCsi (synChnsiquomap (synCpw X)))) p0039 p0044
  have p0046 :=
    @gCoex (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
      (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
        (synCsi (synCsi (synChnsiquomap (synCpw X)))))
      p0034 p0045
  have p0047 :=
    @gCoex
      (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
        (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCpw (synCpw (synChnord X)))))
      (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
        (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
          (synCsi (synCsi (synChnsiquomap (synCpw X))))))
      p0029 p0046
  have p0048 :=
    @gCoex
      (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X))))))
      (synCcom (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
          (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCpw (synCpw (synChnord X)))))
        (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
          (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
            (synCsi (synCsi (synChnsiquomap (synCpw X)))))))
      p0014 p0047
  have p0050 := @gHnordex (synCpw X) p0003
  have p0051 := @gPw1ex (synChnord (synCpw X)) p0050
  have p0052 := @gPw1ex (synCpw1 (synChnord (synCpw X))) p0051
  have p0053 := @gPw1ex (synCpw1 (synCpw1 (synChnord (synCpw X)))) p0052
  have p0054 :=
    @gResex
      (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))) (synCcom
          (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
            (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCpw (synCpw (synChnord X)))))
          (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
            (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
              (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
      (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))) p0048 p0053
  exact p0054

/-- Checked nominal proof certificate identified upstream as `g_cfbwppfixedblockhnqinjexndv`. -/
@[expose]
noncomputable def gCfbwppfixedblockhnqinjexndv (f : Var) (X : Class) (dv_X_f : f ∉ X.fv)
    (hyp_cfbwppfixedblockhnqinjexndv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_cfbwppfixedblockhnqinjexndv_2 : Nominal.NPrf
        (synWbr (synChncard (synCxp (synCxpk X X) (synCnnc))) (synClec)
          (synCtc (synCtc (synChncard X))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWex f
          (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
            (synChnord (synCpw (synCpw (synChnord X))))))) :=
  by
  have dv_cache_0001 :
    f ∉
      ((synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))) (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, dv_X_f,
          or_false, not_false_eq_true])
  have dv_cache_0002 :
    f ∉
      ((synWf1 (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))) (synCcom
                (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                    (synCpw (synCpw (synChnord X)))))
                (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                  (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                    (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
            (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
          (synChnord (synCpw (synCpw (synChnord X)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, dv_X_f,
          or_false, not_false_eq_true])
  have p0000 :=
    @gCfbwppfixedblockhnqgraphinjndv X hyp_cfbwppfixedblockhnqinjexndv_1
      hyp_cfbwppfixedblockhnqinjexndv_2
  have p0001 := @gCfbfixedblockhnqgraphexndv X hyp_cfbwppfixedblockhnqinjexndv_1
  have p0002 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
      (synChnord (synCpw (synCpw (synChnord X)))) (.cv f)
      (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))) (synCcom
            (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
  have p0003 :=
    @gSpcegv
      (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synChnord (synCpw (synCpw (synChnord X)))))
      (synWf1 (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))) (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synChnord (synCpw (synCpw (synChnord X)))))
      f
      (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))) (synCcom
            (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
              (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCpw (synCpw (synChnord X)))))
            (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
              (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
      (synCvv) dv_cache_0001 dv_cache_0002 p0002
  have p0004 := Nominal.mp p0001 p0003
  have p0005 :=
    @gSyl (synWwpp)
      (synWf1 (synCres (synCcom (synCcnv (synChnqinc (synCpw (synCpw (synChnord X)))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))) (synCcom
              (synChnqinc (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                (synCun (synCpw1 (synCpw1 (synCpw1 (synCpw X))))
                  (synCpw (synCpw (synChnord X)))))
              (synCcom (synChnsiquomap (synCpw1 (synCpw1 (synCpw X))))
                (synCcom (synCsi (synChnsiquomap (synCpw1 (synCpw X))))
                  (synCsi (synCsi (synChnsiquomap (synCpw X))))))))
          (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X))))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
        (synChnord (synCpw (synCpw (synChnord X)))))
      (synWex f (synWf1 (.cv f) (synCpw1 (synCpw1 (synCpw1 (synChnord (synCpw X)))))
          (synChnord (synCpw (synCpw (synChnord X))))))
      p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppfiniteblocknotwppndv`. -/
@[expose]
noncomputable def gWppfiniteblocknotwppndv : Nominal.NPrf (.neg (synWwpp)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  have dv_cache_0001 :
    f ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @gCfbpw16oneexndv
  have p0001 := @gCfbliteralp16onehncardboundndv
  have p0002 :=
    @gCfbwppfixedblockhnqinjexndv f
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      dv_cache_0001 p0000 p0001
  have p0003 := @gCfbfixedblocknotwppfrominjndv f p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end
