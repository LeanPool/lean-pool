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

@[expose]
noncomputable def g_cfbhncardpowershiftndv (A : Class)
    (hyp_cfbhncardpowershiftndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw1 A))) (syn_ctc (syn_chncard (syn_cpw A)))) :=
  by
  have p0000 := @g_pwex A hyp_cfbhncardpowershiftndv_1
  have p0001 := @g_hncardtcshiftndv (syn_cpw A) p0000
  have p0003 := @g_pw1ex (syn_cpw A) p0000
  have p0004 := @g_pw1ex A hyp_cfbhncardpowershiftndv_1
  have p0005 := @g_pwex (syn_cpw1 A) p0004
  have p0006 := @g_ncpwpw1 A hyp_cfbhncardpowershiftndv_1
  have p0007 :=
    @g_eqcomi (syn_cnc (syn_cpw (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw A))) p0006
  have p0008 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A)) p0003 p0005 p0007
  have p0009 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cpw A))) (syn_chncard (syn_cpw1 (syn_cpw A)))
      (syn_chncard (syn_cpw (syn_cpw1 A))) p0001 p0008
  have p0010 :=
    @g_eqcomi (syn_ctc (syn_chncard (syn_cpw A))) (syn_chncard (syn_cpw (syn_cpw1 A)))
      p0009
  exact p0010

@[expose]
noncomputable def g_cfbtceqi (A : Class) (B : Class)
    (hyp_cfbtceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_ctc A) (syn_ctc B)) :=
  by
  have p0000 := @g_tceq A B
  have p0001 := Nominal.mp hyp_cfbtceqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_cfbhncardpw1ceqndv :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_c1c))) (syn_chncard (syn_c1c))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pwex (syn_c1c) p0000
  have p0003 := @g_ncpw1c
  have p0004 := @g_hncardnceqndv (syn_cpw (syn_c1c)) (syn_c1c) p0001 p0000 p0003
  exact p0004

@[expose]
noncomputable def g_cfbhncardpwpw16stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_chncard (syn_cpw
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_cfbhncardpowershiftndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  exact p0006

@[expose]
noncomputable def g_cfbhncardpwpw15stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard
          (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  exact p0005

@[expose]
noncomputable def g_cfbhncardpwpw14stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  exact p0004

@[expose]
noncomputable def g_cfbhncardpwpw13stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  exact p0003

@[expose]
noncomputable def g_cfbhncardpwpw12stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_cfbhncardpowershiftndv (syn_cpw1 (syn_c1c)) p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardpwpw11stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))
        (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_cfbhncardpowershiftndv (syn_c1c) p0000
  exact p0001

@[expose]
noncomputable def g_cfbhncardpwpw16to4ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_chncard
              (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw16stepndv
  have p0001 := @g_cfbhncardpwpw15stepndv
  have p0002 :=
    @g_tceq
      (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqtri
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_chncard
          (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_cfbhncardpwpw14step2tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_chncard
              (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc
          (syn_ctc (syn_ctc
              (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw14stepndv
  have p0001 :=
    @g_cfbtceqi
      (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0000
  have p0002 :=
    @g_cfbtceqi
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardpwpw13step3tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc
            (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw13stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0000
  have p0002 :=
    @g_cfbtceqi
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0001
  have p0003 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0002
  exact p0003

@[expose]
noncomputable def g_cfbhncardpwpw12step4tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw12stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))) p0001
  have p0003 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))) p0002
  have p0004 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))))
      p0003
  exact p0004

@[expose]
noncomputable def g_cfbhncardpwpw11step5tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw11stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))
      (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))) p0002
  have p0004 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))) p0003
  have p0005 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))))
      p0004
  exact p0005

@[expose]
noncomputable def g_cfbhncardpwpw16to3ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw16to4ndv
  have p0001 := @g_cfbhncardpwpw14step2tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardpwpw16to2ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw16to3ndv
  have p0001 := @g_cfbhncardpwpw13step3tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardpwpw16to1ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw16to2ndv
  have p0001 := @g_cfbhncardpwpw12step4tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardpwpw16to0ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw16to1ndv
  have p0001 := @g_cfbhncardpwpw11step5tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardtc3forwardndv (A : Class)
    (hyp_cfbhncardtc3forwardndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_chncard A))))
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))))) :=
  by
  have p0000 := @g_hncardtc2 A hyp_cfbhncardtc3forwardndv_1
  have p0001 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard A)))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A)))) p0000
  have p0002 := @g_hnordex A hyp_cfbhncardtc3forwardndv_1
  have p0003 := @g_pw1ex (syn_chnord A) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_chnord A)) p0003
  have p0005 := @g_tcnc (syn_cpw1 (syn_cpw1 (syn_chnord A))) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_chncard A))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A)))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))) p0001 p0005
  exact p0006

@[expose]
noncomputable def g_cfbhncardtc3ndv (A : Class)
    (hyp_cfbhncardtc3ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))))
        (syn_ctc (syn_ctc (syn_ctc (syn_chncard A))))) :=
  by
  have p0000 := @g_cfbhncardtc3forwardndv A hyp_cfbhncardtc3ndv_1
  have p0001 :=
    @g_eqcomi (syn_ctc (syn_ctc (syn_ctc (syn_chncard A))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))) p0000
  exact p0001

@[expose]
noncomputable def g_cfbhncardpw1ceq6tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) :=
  by
  have p0000 := @g_cfbhncardpw1ceqndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_c1c))) (syn_chncard (syn_c1c)) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))
      (syn_ctc (syn_chncard (syn_c1c))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))
      (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) p0002
  have p0004 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) p0003
  have p0005 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) p0004
  have p0006 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) p0005
  exact p0006

@[expose]
noncomputable def g_cfbhncardpwpw16basendv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) :=
  by
  have p0000 := @g_cfbhncardpwpw16to0ndv
  have p0001 := @g_cfbhncardpw1ceq6tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbsourceledgerndv :
    Nominal.NPrf
      (.classEq (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  have p0007 :=
    @g_pwex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0006
  have p0008 :=
    @g_cfbhncardtc3ndv
      (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0007
  have p0009 := @g_cfbhncardpwpw16basendv
  have p0010 :=
    @g_cfbtceqi
      (syn_chncard (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      p0009
  have p0011 :=
    @g_cfbtceqi
      (syn_ctc (syn_chncard (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      p0010
  have p0012 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      p0011
  have p0013 :=
    @g_eqtri
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      p0008 p0012
  exact p0013

@[expose]
noncomputable def g_cfbhncardpw2enpw1shiftndv (Y : Class) (Z : Class)
    (hyp_cfbhncardpw2enpw1shiftndv_1 : Nominal.NPrf (.classMem Z (syn_cvv)))
    (hyp_cfbhncardpw2enpw1shiftndv_2 : Nominal.NPrf (.classMem Y (syn_cvv)))
    (hyp_cfbhncardpw2enpw1shiftndv_3 : Nominal.NPrf (syn_wbr Z (syn_cen) (syn_cpw1 Y))) :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw Z)))
        (syn_ctc (syn_chncard (syn_cpw (syn_cpw Y))))) :=
  by
  have p0000 := @g_pwex Z hyp_cfbhncardpw2enpw1shiftndv_1
  have p0001 := @g_pwex (syn_cpw Z) p0000
  have p0002 := @g_pwex Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0003 := @g_pwex (syn_cpw Y) p0002
  have p0004 := @g_pw1ex (syn_cpw (syn_cpw Y)) p0003
  have p0005 := @g_enpw Z (syn_cpw1 Y)
  have p0006 := Nominal.mp hyp_cfbhncardpw2enpw1shiftndv_3 p0005
  have p0007 := @g_enpw1pw Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0008 := @g_ensymi (syn_cpw1 (syn_cpw Y)) (syn_cpw (syn_cpw1 Y))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_pm3_2i (syn_wbr (syn_cpw Z) (syn_cen) (syn_cpw (syn_cpw1 Y)))
      (syn_wbr (syn_cpw (syn_cpw1 Y)) (syn_cen) (syn_cpw1 (syn_cpw Y))) p0006 p0009
  have p0011 := @g_entr (syn_cpw Z) (syn_cpw (syn_cpw1 Y)) (syn_cpw1 (syn_cpw Y))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_enpw (syn_cpw Z) (syn_cpw1 (syn_cpw Y))
  have p0014 := Nominal.mp p0012 p0013
  have p0016 := @g_enpw1pw (syn_cpw Y) p0002
  have p0017 :=
    @g_ensymi (syn_cpw1 (syn_cpw (syn_cpw Y))) (syn_cpw (syn_cpw1 (syn_cpw Y)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wbr (syn_cpw (syn_cpw Z)) (syn_cen) (syn_cpw (syn_cpw1 (syn_cpw Y))))
      (syn_wbr (syn_cpw (syn_cpw1 (syn_cpw Y))) (syn_cen) (syn_cpw1 (syn_cpw (syn_cpw Y))))
      p0014 p0018
  have p0020 :=
    @g_entr (syn_cpw (syn_cpw Z)) (syn_cpw (syn_cpw1 (syn_cpw Y)))
      (syn_cpw1 (syn_cpw (syn_cpw Y)))
  have p0021 := Nominal.mp p0019 p0020
  have p0024 := @g_eqnc (syn_cpw (syn_cpw Z)) (syn_cpw1 (syn_cpw (syn_cpw Y))) p0001
  have p0025 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw (syn_cpw Z))) (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw Y)))))
      (syn_wbr (syn_cpw (syn_cpw Z)) (syn_cen) (syn_cpw1 (syn_cpw (syn_cpw Y)))) p0021
      p0024
  have p0026 :=
    @g_hncardnceqndv (syn_cpw (syn_cpw Z)) (syn_cpw1 (syn_cpw (syn_cpw Y))) p0001 p0004
      p0025
  have p0029 := @g_hncardtcshiftndv (syn_cpw (syn_cpw Y)) p0003
  have p0030 :=
    @g_eqcomi (syn_ctc (syn_chncard (syn_cpw (syn_cpw Y))))
      (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw Y)))) p0029
  have p0031 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw Z)))
      (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw Y))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw Y)))) p0026 p0030
  exact p0031

@[expose]
noncomputable def g_cfbtccli (A : Class)
    (hyp_cfbtccli_1 : Nominal.NPrf (.classMem A (syn_cncs))) :
    Nominal.NPrf (.classMem (syn_ctc A) (syn_cncs)) :=
  by
  have p0000 := @g_tccl A
  have p0001 := Nominal.mp hyp_cfbtccli_1 p0000
  exact p0001

@[expose]
noncomputable def g_cfbtargetqbaseexndv :
    Nominal.NPrf
      (.classMem (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))) (syn_cvv)) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_hnordex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pwex (syn_chnord (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pwex (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))) p0003
  exact p0004

@[expose]
noncomputable def g_cfbtargetqncndv :
    Nominal.NPrf
      (.classMem (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))
        (syn_cncs)) :=
  by
  have p0000 := @g_cfbtargetqbaseexndv
  have p0001 := @g_hncardnc (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbt6hncard1ncndv :
    Nominal.NPrf
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_cncs)) :=
  by
  have p0000 := @g_hncardnc1ndv
  have p0001 := @g_cfbtccli (syn_chncard (syn_c1c)) p0000
  have p0002 := @g_cfbtccli (syn_ctc (syn_chncard (syn_c1c))) p0001
  have p0003 := @g_cfbtccli (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) p0002
  have p0004 := @g_cfbtccli (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) p0003
  have p0005 :=
    @g_cfbtccli (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) p0004
  have p0006 :=
    @g_cfbtccli (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      p0005
  exact p0006

@[expose]
noncomputable def g_cfbt2targetqncndv :
    Nominal.NPrf
      (.classMem (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
        (syn_cncs)) :=
  by
  have p0000 := @g_cfbtargetqncndv
  have p0001 :=
    @g_cfbtccli (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))) p0000
  have p0002 :=
    @g_cfbtccli
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) p0001
  exact p0002

@[expose]
noncomputable def g_cfbfixedblockcancel3ndv :
    Nominal.NPrf
      (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                      (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) (syn_wbr
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_ctc (syn_ctc
              (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbt6hncard1ncndv
  have p0001 := @g_cfbt2targetqncndv
  have p0002 :=
    @g_tc3lecan
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbfixedblockouterhartogsndv (R : Class)
    (hyp_cfbfixedblockouterhartogsndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe)
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf
      (syn_wbr (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) :=
  by
  have p0000 := @g_hncardsuccshiftedndv R hyp_cfbfixedblockouterhartogsndv_1
  have p0001 := @g_wppconcrete6fntc7hncard1valndv
  have p0002 :=
    @g_breqtrri
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_clec) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbfixedblockpointimpndv (R : Class)
    (hyp_cfbfixedblockpointimpndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe)
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_ctc (syn_ctc
              (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) (syn_wbr
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbfixedblockouterhartogsndv R hyp_cfbfixedblockpointimpndv_1
  have p0001 := @g_cfbt6hncard1ncndv
  have p0002 := @g_cfbt2targetqncndv
  have p0003 := @g_wppconcrete6tcvalncndv
  have p0004 :=
    @g_lectr
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
  have p0005 :=
    @g_mp3an
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs))
      (.classMem (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
        (syn_cncs))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_cncs))
      (.imp (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_ctc (syn_ctc
                (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) (syn_wbr
            (syn_ctc (syn_ctc
                (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_clec)
            (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))
        (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))
      p0001 p0002 p0003 p0004
  have p0006 :=
    @g_mpan2
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_cfbhnordpw1shiftensymndv (A : Class)
    (hyp_cfbhnordpw1shiftensymndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_chnord (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_chnord A))) :=
  by
  have p0000 := @g_hnordpw1shiftenndv A hyp_cfbhnordpw1shiftensymndv_1
  have p0001 := @g_ensym (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A)))
      (syn_wbr (syn_chnord (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_chnord A))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbhncardpw2hnordpw1shiftndv (A : Class)
    (hyp_cfbhncardpw2hnordpw1shiftndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 A)))))
        (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord A)))))) :=
  by
  have p0000 := @g_pw1ex A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0001 := @g_hnordex (syn_cpw1 A) p0000
  have p0002 := @g_hnordex A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0003 := @g_cfbhnordpw1shiftensymndv A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0004 :=
    @g_cfbhncardpw2enpw1shiftndv (syn_chnord A) (syn_chnord (syn_cpw1 A)) p0001 p0002
      p0003
  exact p0004

@[expose]
noncomputable def g_cfbtarget6stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_cfbhncardpw2hnordpw1shiftndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  exact p0006

@[expose]
noncomputable def g_cfbtarget5stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw
                (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0004
  exact p0005

@[expose]
noncomputable def g_cfbtarget4stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw
            (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_ctc (syn_chncard (syn_cpw
              (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  exact p0004

@[expose]
noncomputable def g_cfbtarget3stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard
          (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  exact p0003

@[expose]
noncomputable def g_cfbtarget2stepndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_c1c)) p0001
  exact p0002

@[expose]
noncomputable def g_cfbtarget5step1tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget5stepndv
  have p0001 :=
    @g_cfbtceqi
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw
              (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0000
  exact p0001

@[expose]
noncomputable def g_cfbtarget4step2tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw
                  (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw
                    (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget4stepndv
  have p0001 :=
    @g_cfbtceqi
      (syn_chncard (syn_cpw
          (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_chncard
          (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0000
  have p0002 :=
    @g_cfbtceqi
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw
              (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_ctc (syn_ctc (syn_chncard
            (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0001
  exact p0002

@[expose]
noncomputable def g_cfbtarget3step3tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw
                  (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw
                    (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget3stepndv
  have p0001 :=
    @g_cfbtceqi
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0000
  have p0002 :=
    @g_cfbtceqi
      (syn_ctc (syn_chncard
          (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0001
  have p0003 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_chncard
            (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard
              (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0002
  exact p0003

@[expose]
noncomputable def g_cfbtarget2step4tndv :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                  (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                    (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget2stepndv
  have p0001 :=
    @g_cfbtceqi
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) p0000
  have p0002 :=
    @g_cfbtceqi
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      p0001
  have p0003 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc
          (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))
      p0002
  have p0004 :=
    @g_cfbtceqi
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard
              (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc
              (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))
      p0003
  exact p0004

@[expose]
noncomputable def g_cfbtarget6to4ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget6stepndv
  have p0001 := @g_cfbtarget5step1tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw
                (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbtarget6to3ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw
                    (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget6to4ndv
  have p0001 := @g_cfbtarget4step2tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw
                (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw
                (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbtarget6to2ndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw
                    (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget6to3ndv
  have p0001 := @g_cfbtarget3step3tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw
                (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbtargethncardledgerndv :
    Nominal.NPrf
      (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                    (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbtarget6to2ndv
  have p0001 := @g_cfbtarget2step4tndv
  have p0002 :=
    @g_eqtri
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbtargetledgerndv :
    Nominal.NPrf
      (.classEq (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                    (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) :=
  by
  have p0000 :=
    (Nominal.classEqRefl (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
  have p0001 :=
    @g_eqcomi
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0000
  have p0002 := @g_cfbtargethncardledgerndv
  have p0003 :=
    @g_eqtri
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_cfbfixedblockledgercmpndv :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
          (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wbr
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                      (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))))) :=
  by
  have p0000 := @g_cfbsourceledgerndv
  have p0001 := @g_cfbtargetledgerndv
  have p0002 :=
    @g_breq12i
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))
      (syn_clec) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbfixedblockledgercmpdndv
    (hyp_cfbfixedblockledgercmpdndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
            (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                      (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))))) :=
  by
  have p0000 := @g_cfbfixedblockledgercmpndv
  have p0001 :=
    @g_sylib (syn_wwpp)
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec)
        (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                    (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))))
      hyp_cfbfixedblockledgercmpdndv_1 p0000
  exact p0001

@[expose]
noncomputable def g_cfbfixedblockcancelleddndv
    (hyp_cfbfixedblockcancelleddndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
            (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_ctc (syn_ctc
              (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))) :=
  by
  have p0000 := @g_cfbfixedblockledgercmpdndv hyp_cfbfixedblockcancelleddndv_1
  have p0001 := @g_cfbfixedblockcancel3ndv
  have p0002 :=
    @g_syl (syn_wwpp)
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard
                    (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbfixedblockf6pointfromnclendv (R : Class)
    (hyp_cfbfixedblockf6pointfromnclendv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
            (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))))
    (hyp_cfbfixedblockf6pointfromnclendv_2 : Nominal.NPrf (syn_wbr R (syn_cwe)
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbfixedblockcancelleddndv hyp_cfbfixedblockf6pointfromnclendv_1
  have p0001 := @g_cfbfixedblockpointimpndv R hyp_cfbfixedblockf6pointfromnclendv_2
  have p0002 :=
    @g_syl (syn_wwpp)
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cfbpw16oneexndv :
    Nominal.NPrf
      (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cvv)) :=
  by
  have p0000 := @g_n_1cex
  have p0001 := @g_pw1ex (syn_c1c) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  exact p0006

@[expose]
noncomputable def g_cfbfixedblocksourceexndv :
    Nominal.NPrf
      (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (syn_cvv)) :=
  by
  have p0000 := @g_cfbpw16oneexndv
  have p0001 :=
    @g_pwex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0000
  have p0002 :=
    @g_hnordex
      (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0001
  have p0003 :=
    @g_pw1ex
      (syn_chnord (syn_cpw
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0002
  have p0004 :=
    @g_pw1ex
      (syn_cpw1 (syn_chnord (syn_cpw
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0003
  have p0005 :=
    @g_pw1ex
      (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0004
  exact p0005

@[expose]
noncomputable def g_cfbfixedblocktargetexndv :
    Nominal.NPrf
      (.classMem (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (syn_cvv)) :=
  by
  have p0000 := @g_cfbpw16oneexndv
  have p0001 :=
    @g_hnordex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0000
  have p0002 :=
    @g_pwex
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0001
  have p0003 :=
    @g_pwex
      (syn_cpw (syn_chnord
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0002
  have p0004 :=
    @g_hnordex
      (syn_cpw (syn_cpw (syn_chnord
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0003
  exact p0004

@[expose]
noncomputable def g_cfbnclefrominjimpndv (A : Class) (B : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv)
    (hyp_cfbnclefrominjimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_cfbnclefrominjimpndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))) :=
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
    @g_nclenc A B f dv_cache_0001 dv_cache_0002 hyp_cfbnclefrominjimpndv_1
      hyp_cfbnclefrominjimpndv_2
  have p0001 :=
    @g_biimpri (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))
      (syn_wex f (syn_wf1 (.cv f) A B)) p0000
  exact p0001

@[expose]
noncomputable def g_cfbfixedblocknclefrominjndv (f : Var)
    (hyp_cfbfixedblocknclefrominjndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw
                      (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
          (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))) :=
  by
  have dv_cache_0001 :
    f ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))).fv :=
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
      ((syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))).fv :=
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
  have p0000 := @g_cfbfixedblocksourceexndv
  have p0001 := @g_cfbfixedblocktargetexndv
  have p0002 :=
    @g_cfbnclefrominjimpndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      f dv_cache_0001 dv_cache_0002 p0000 p0001
  have p0003 :=
    @g_syl (syn_wwpp)
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
      (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec)
        (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
      hyp_cfbfixedblocknclefrominjndv_1 p0002
  exact p0003

@[expose]
noncomputable def g_cfbfixedblockf6pointfrominjndv (R : Class) (f : Var)
    (hyp_cfbfixedblockf6pointfrominjndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))))
    (hyp_cfbfixedblockf6pointfrominjndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe)
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) :=
  by
  have p0000 := @g_cfbfixedblocknclefrominjndv f hyp_cfbfixedblockf6pointfrominjndv_1
  have p0001 :=
    @g_cfbfixedblockf6pointfromnclendv R p0000 hyp_cfbfixedblockf6pointfrominjndv_2
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

@[expose]
noncomputable def g_cfbfixedblockf6pointfrominjnowendv (f : Var)
    (hyp_cfbfixedblockf6pointfrominjnowendv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) :=
  by
  have dv_cache_0001 :
    Disjoint ((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv
      ((syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))).fv :=
    by
    exact
      (show Disjoint ((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv
          ((syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset];
          exact
            (show
              Disjoint (((syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))).fv)
                (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv)
              from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
                exact
                  (show
                    Disjoint (((syn_chnord (syn_cpw1 (syn_c1c)))).fv)
                      (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord];
                      exact
                        (show
                          Disjoint (((syn_cpw1 (syn_c1c))).fv)
                            (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv)
                          from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                            exact
                              (show
                                Disjoint (((syn_c1c)).fv)
                                  (((syn_cpw
                                      (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv)
                                from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
                                  exact
                                    (show
                                      Disjoint ((∅ : Finset Var))
                                        (((syn_cpw
                                            (syn_cpw
                                              (syn_chnord (syn_cpw1 (syn_c1c)))))).fv)
                                      from (by simp))))))))))))
  have p0000 := @g_cfbtargetqbaseexndv
  have p0002 := @g_hncodecmpsetexg (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0003 := Nominal.mp p0000 p0002
  have p0005 := @g_hncodecmplnpwcndv (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0006 := Nominal.mp p0000 p0005
  have p0008 := @g_hncodecmplnkerndv (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0009 := Nominal.mp p0000 p0008
  have p0010 :=
    @g_hnordwefromcmp (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
      (syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))
      dv_cache_0001 p0000 p0003 p0006 p0009
  have p0011 :=
    @g_cfbfixedblockf6pointfrominjndv
      (syn_clnqord (syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))
        (syn_chwcn (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
      f hyp_cfbfixedblockf6pointfrominjnowendv_1 p0010
  exact p0011

@[expose]
noncomputable def g_cfbfixedblocknotwppfrominjndv (f : Var)
    (hyp_cfbfixedblocknotwppfrominjndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f
            (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf (.neg (syn_wwpp)) :=
  by
  have p0000 :=
    @g_cfbfixedblockf6pointfrominjnowendv f hyp_cfbfixedblocknotwppfrominjndv_1
  have p0001 := @g_wppconcrete6notwppfrompointndv p0000
  exact p0001

@[expose]
noncomputable def g_cfbthresholdnn2lencndv (X : Class)
    (hyp_cfbthresholdnn2lencndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbthresholdnn2lencndv_2 :
      Nominal.NPrf (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc X))) :
    Nominal.NPrf
      (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 X)))) :=
  by
  have p0000 := @g_nncex
  have p0001 := @g_ncelncsi (syn_cnnc) p0000
  have p0002 := @g_ncelncsi X hyp_cfbthresholdnn2lencndv_1
  have p0003 :=
    @g_pm3_2i (.classMem (syn_cnc (syn_cnnc)) (syn_cncs))
      (.classMem (syn_cnc X) (syn_cncs)) p0001 p0002
  have p0004 := @g_tlecg (syn_cnc (syn_cnnc)) (syn_cnc X)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_mpbi (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc X))
      (syn_wbr (syn_ctc (syn_cnc (syn_cnnc))) (syn_clec) (syn_ctc (syn_cnc X)))
      hyp_cfbthresholdnn2lencndv_2 p0005
  have p0009 := @g_tccl (syn_cnc (syn_cnnc))
  have p0010 := Nominal.mp p0001 p0009
  have p0012 := @g_tccl (syn_cnc X)
  have p0013 := Nominal.mp p0002 p0012
  have p0014 :=
    @g_pm3_2i (.classMem (syn_ctc (syn_cnc (syn_cnnc))) (syn_cncs))
      (.classMem (syn_ctc (syn_cnc X)) (syn_cncs)) p0010 p0013
  have p0015 := @g_tlecg (syn_ctc (syn_cnc (syn_cnnc))) (syn_ctc (syn_cnc X))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_cnc (syn_cnnc))) (syn_clec) (syn_ctc (syn_cnc X)))
      (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_clec)
        (syn_ctc (syn_ctc (syn_cnc X))))
      p0006 p0016
  have p0019 := @g_tc2nc (syn_cnnc) p0000
  have p0020 := @g_tcnnf1o
  have p0021 := @g_tcfnex
  have p0023 := @g_pw1ex (syn_cnnc) p0000
  have p0024 := @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0021 p0023
  have p0025 :=
    @g_f1oen (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))
      p0024
  have p0026 := Nominal.mp p0020 p0025
  have p0027 := @g_enpw1 (syn_cpw1 (syn_cnnc)) (syn_cnnc)
  have p0028 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cnnc)) (syn_cen) (syn_cnnc))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cpw1 (syn_cnnc))) p0026
      p0027
  have p0036 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cpw1 (syn_cnnc)))
      (syn_wbr (syn_cpw1 (syn_cnnc)) (syn_cen) (syn_cnnc)) p0028 p0026
  have p0037 := @g_entr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)
  have p0038 := Nominal.mp p0036 p0037
  have p0041 := @g_pw1ex (syn_cpw1 (syn_cnnc)) p0023
  have p0042 := @g_eqnc (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cnnc) p0041
  have p0043 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (syn_cnc (syn_cnnc)))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cnnc)) p0038 p0042
  have p0044 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc (syn_cnnc))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (syn_cnc (syn_cnnc)) p0019 p0043
  have p0045 := @g_tc2nc X hyp_cfbthresholdnn2lencndv_1
  have p0046 :=
    @g_breq12i (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_cnc (syn_cnnc))
      (syn_ctc (syn_ctc (syn_cnc X))) (syn_cnc (syn_cpw1 (syn_cpw1 X))) (syn_clec) p0044
      p0045
  have p0047 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_clec)
        (syn_ctc (syn_ctc (syn_cnc X))))
      (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 X)))) p0017
      p0046
  exact p0047

@[expose]
noncomputable def g_cfbliteralunivhncardboundndv :
    Nominal.NPrf
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))) :=
  by
  have p0000 := @g_vvex
  have p0001 := @g_pw1ex (syn_cvv) p0000
  have p0002 := @g_pw1ex (syn_cpw1 (syn_cvv)) p0001
  have p0003 := @g_ncelncsi (syn_cpw1 (syn_cpw1 (syn_cvv))) p0002
  have p0004 := @g_nncex
  have p0005 := @g_ncelncsi (syn_cnnc) p0004
  have p0010 :=
    @g_n_3pm3_2i (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs))
      (.classMem (syn_cnc (syn_cnnc)) (syn_cncs))
      (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)) p0003 p0005 p0003
  have p0012 := @g_ssv (syn_cnnc)
  have p0015 := @g_nclec (syn_cnnc) (syn_cvv) p0004 p0000
  have p0016 := Nominal.mp p0012 p0015
  have p0017 := @g_cfbthresholdnn2lencndv (syn_cvv) p0000 p0016
  have p0018 :=
    @g_pm3_2i
      (syn_w3a (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs))
        (.classMem (syn_cnc (syn_cnnc)) (syn_cncs))
        (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)))
      (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      p0010 p0017
  have p0019 :=
    @g_lemuc2 (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnc (syn_cnnc))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0020 := Nominal.mp p0018 p0019
  have p0022 := @g_wppqkrelliteralnceqndv (syn_cvv) p0000
  have p0023 := @g_xpvv
  have p0024 := @g_pw1eq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_pw1eq (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))) (syn_cpw1 (syn_cvv))
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @g_xpeq1i (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc) p0027
  have p0029 :=
    @g_nceqi (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cnnc))
      (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0028
  have p0030 :=
    @g_eqtri (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
      (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cnnc)))
      (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc))) p0022 p0029
  have p0035 := @g_mucnc (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc) p0002 p0004
  have p0036 :=
    @g_eqcomi
      (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc)))
      (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc))) p0035
  have p0037 :=
    @g_eqtri (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
      (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc)))
      p0030 p0036
  have p0044 :=
    @g_mucnc (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0002 p0002
  have p0047 := @g_pw1xpshiftenndv (syn_cvv) (syn_cvv) p0000 p0000
  have p0048 :=
    @g_enpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))
  have p0049 :=
    @g_mpbi
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))) (syn_cen)
        (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cen)
        (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))))
      p0047 p0048
  have p0054 := @g_pw1xpshiftenndv (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0001 p0001
  have p0055 :=
    @g_pm3_2i
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cen)
        (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))))
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))) (syn_cen)
        (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      p0049 p0054
  have p0056 :=
    @g_entr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))))
      (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))))
      (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0057 := Nominal.mp p0055 p0056
  have p0058 :=
    @g_ensym (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))))
      (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0059 :=
    @g_mpbi
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cen)
        (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))))
      p0057 p0058
  have p0065 :=
    @g_breq2i (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))))
      (syn_cpw1 (syn_cpw1 (syn_cvv)))
      (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cen)
      p0027
  have p0066 :=
    @g_mpbi
      (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))))
      (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      p0059 p0065
  have p0073 :=
    @g_xpex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0002 p0002
  have p0074 :=
    @g_eqnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) p0073
  have p0075 :=
    @g_mpbir
      (.classEq (syn_cnc
          (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))))
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      p0066 p0074
  have p0076 :=
    @g_eqtri
      (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc)
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0044 p0075
  have p0077 :=
    @g_eqcomi
      (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc)
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0076
  have p0078 :=
    @g_breq12i (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
      (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc)))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc)
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_clec) p0037 p0077
  have p0079 :=
    @g_mpbir
      (syn_wbr (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_clec)
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_wbr
        (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc)))
        (syn_clec) (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc)
          (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0020 p0078
  have p0082 := @g_xpkex (syn_cvv) (syn_cvv) p0000 p0000
  have p0084 := @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0082 p0004
  have p0088 :=
    @g_hncardnclecndv (syn_cpw1 (syn_cpw1 (syn_cvv)))
      (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0084 p0002
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

@[expose]
noncomputable def g_cfbliteralp17hncardboundndv :
    Nominal.NPrf
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))) :=
  by
  have p0000 := @g_cfbliteralunivhncardboundndv
  have p0001 := @g_vvex
  have p0003 := @g_xpkex (syn_cvv) (syn_cvv) p0001 p0001
  have p0004 := @g_nncex
  have p0005 := @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0003 p0004
  have p0006 := @g_hncardnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))
  have p0007 := Nominal.mp p0005 p0006
  have p0009 := @g_pw1ex (syn_cvv) p0001
  have p0010 := @g_pw1ex (syn_cpw1 (syn_cvv)) p0009
  have p0011 := @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_pm3_2i
      (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)) p0007 p0012
  have p0014 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))))
        (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0000 p0015
  have p0022 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0005
  have p0028 := @g_pw1ex (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0005
  have p0033 := @g_xpkex (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0009 p0009
  have p0035 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc) p0033 p0004
  have p0037 := @g_wpplitshiftenndv (syn_cvv) p0001
  have p0044 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0028
  have p0045 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))))
        (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))))
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cen)
        (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      p0037 p0044
  have p0046 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0028
      p0035 p0045
  have p0047 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))))
      (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      p0022 p0046
  have p0051 := @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cvv))) p0010
  have p0052 :=
    @g_breq12i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_clec) p0047 p0051
  have p0053 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))))
        (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wbr (syn_chncard
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0016 p0052
  have p0061 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))
  have p0062 := Nominal.mp p0035 p0061
  have p0066 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0010
  have p0067 := @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0068 := Nominal.mp p0066 p0067
  have p0069 :=
    @g_pm3_2i
      (.classMem (syn_chncard
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cncs))
      p0062 p0068
  have p0070 :=
    @g_tlecg
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0071 := Nominal.mp p0069 p0070
  have p0072 :=
    @g_mpbi
      (syn_wbr (syn_chncard
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wbr (syn_ctc (syn_chncard
            (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))))
        (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      p0053 p0071
  have p0080 :=
    @g_hncardtcshiftndv
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0035
  have p0088 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))
      p0035
  have p0095 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0010 p0010
  have p0097 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_cnnc) p0095 p0004
  have p0100 := @g_wpplitshiftenndv (syn_cpw1 (syn_cvv)) p0009
  have p0109 :=
    @g_eqnc
      (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cnnc))
      p0088
  have p0110 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1
            (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_cnc
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc))))
      (syn_wbr (syn_cpw1
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_cen)
        (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cnnc)))
      p0100 p0109
  have p0111 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cnnc))
      p0088 p0097 p0110
  have p0112 :=
    @g_eqtri
      (syn_ctc (syn_chncard
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))))
      (syn_chncard (syn_cpw1
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))))
      (syn_chncard (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cnnc)))
      p0080 p0111
  have p0117 := @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0066
  have p0118 :=
    @g_breq12i
      (syn_ctc (syn_chncard
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))))
      (syn_chncard (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cnnc)))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_clec) p0112
      p0117
  have p0119 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard
            (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))))
        (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      (syn_wbr (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      p0072 p0118
  have p0129 :=
    @g_hncardnc
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cnnc))
  have p0130 := Nominal.mp p0097 p0129
  have p0135 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0066
  have p0136 := @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0137 := Nominal.mp p0135 p0136
  have p0138 :=
    @g_pm3_2i
      (.classMem (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc))) (syn_cncs))
      (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cncs))
      p0130 p0137
  have p0139 :=
    @g_tlecg
      (syn_chncard (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cnnc)))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0140 := Nominal.mp p0138 p0139
  have p0141 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cnnc)))) (syn_clec)
        (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0119 p0140
  have p0151 :=
    @g_hncardtcshiftndv
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cnnc))
      p0097
  have p0161 :=
    @g_pw1ex
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cnnc))
      p0097
  have p0170 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0066 p0066
  have p0172 :=
    @g_xpex
      (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cnnc) p0170 p0004
  have p0176 := @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cvv))) p0010
  have p0187 :=
    @g_eqnc
      (syn_cpw1 (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))
      p0161
  have p0188 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cnnc)))) (syn_cnc (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))))
      (syn_wbr (syn_cpw1 (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))
      p0176 p0187
  have p0189 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))
      p0161 p0172 p0188
  have p0190 :=
    @g_eqtri
      (syn_ctc (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc))))
      (syn_chncard (syn_cpw1 (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))
      p0151 p0189
  have p0196 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0135
  have p0197 :=
    @g_breq12i
      (syn_ctc (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      (syn_clec) p0190 p0196
  have p0198 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cnnc)))) (syn_clec)
        (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_clec)
        (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0141 p0197
  have p0210 :=
    @g_hncardnc
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))
  have p0211 := Nominal.mp p0172 p0210
  have p0217 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0135
  have p0218 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0219 := Nominal.mp p0217 p0218
  have p0220 :=
    @g_pm3_2i
      (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
        (syn_cncs))
      p0211 p0219
  have p0221 :=
    @g_tlecg
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0222 := Nominal.mp p0220 p0221
  have p0223 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_clec)
        (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_clec) (syn_ctc
          (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      p0198 p0222
  have p0235 :=
    @g_hncardtcshiftndv
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))
      p0172
  have p0247 :=
    @g_pw1ex
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))
      p0172
  have p0258 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0135 p0135
  have p0260 :=
    @g_xpex
      (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_cnnc) p0258 p0004
  have p0265 := @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0066
  have p0278 :=
    @g_eqnc
      (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))
      p0247
  have p0279 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_cnc (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))))
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_cen) (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))
      p0265 p0278
  have p0280 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))
      p0247 p0260 p0279
  have p0281 :=
    @g_eqtri
      (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))))
      (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))
      p0235 p0280
  have p0288 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0217
  have p0289 :=
    @g_breq12i
      (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))
      (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_clec) p0281 p0288
  have p0290 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_clec) (syn_ctc
          (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_wbr (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_clec)
        (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      p0223 p0289
  have p0304 :=
    @g_hncardnc
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))
  have p0305 := Nominal.mp p0260 p0304
  have p0312 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0217
  have p0313 :=
    @g_hncardnc
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0314 := Nominal.mp p0312 p0313
  have p0315 :=
    @g_pm3_2i
      (.classMem (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_cncs))
      (.classMem (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
        (syn_cncs))
      p0305 p0314
  have p0316 :=
    @g_tlecg
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
  have p0317 := Nominal.mp p0315 p0316
  have p0318 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_clec)
        (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_clec)
        (syn_ctc (syn_chncard
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
      p0290 p0317
  have p0332 :=
    @g_hncardtcshiftndv
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))
      p0260
  have p0346 :=
    @g_pw1ex
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))
      p0260
  have p0359 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0217 p0217
  have p0361 :=
    @g_xpex
      (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      (syn_cnnc) p0359 p0004
  have p0367 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0135
  have p0382 :=
    @g_eqnc
      (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))
      p0346
  have p0383 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_cnc
          (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
      (syn_wbr (syn_cpw1 (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_cen)
        (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
      p0367 p0382
  have p0384 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))
      p0346 p0361 p0383
  have p0385 :=
    @g_eqtri
      (syn_ctc (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))))
      (syn_chncard (syn_cpw1 (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))))
      (syn_chncard (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
      p0332 p0384
  have p0393 :=
    @g_hncardtcshiftndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0312
  have p0394 :=
    @g_breq12i
      (syn_ctc (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))))
      (syn_chncard (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
      (syn_ctc (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_chncard (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_clec) p0385 p0393
  have p0395 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_clec)
        (syn_ctc (syn_chncard
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
      (syn_wbr (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
      p0318 p0394
  have p0411 :=
    @g_hncardnc
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))
  have p0412 := Nominal.mp p0361 p0411
  have p0420 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      p0312
  have p0421 :=
    @g_hncardnc
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
  have p0422 := Nominal.mp p0420 p0421
  have p0423 :=
    @g_pm3_2i
      (.classMem (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
        (syn_cncs))
      (.classMem (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
        (syn_cncs))
      p0412 p0422
  have p0424 :=
    @g_tlecg
      (syn_chncard (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
      (syn_chncard (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
  have p0425 := Nominal.mp p0423 p0424
  have p0426 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
        (syn_clec) (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
        (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      p0395 p0425
  have p0442 :=
    @g_hncardtcshiftndv
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))
      p0361
  have p0458 :=
    @g_pw1ex
      (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))
      p0361
  have p0473 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0312
      p0312
  have p0475 :=
    @g_xpex
      (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_cnnc) p0473 p0004
  have p0482 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0217
  have p0499 :=
    @g_eqnc
      (syn_cpw1 (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
        (syn_cnnc))
      p0458
  have p0500 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
        (syn_cnc (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))))
      (syn_wbr (syn_cpw1 (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
        (syn_cen) (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cnnc)))
      p0482 p0499
  have p0501 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cxp
          (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
        (syn_cnnc))
      p0458 p0475 p0500
  have p0502 :=
    @g_eqtri
      (syn_ctc (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
      (syn_chncard (syn_cpw1 (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cnnc)))
      p0442 p0501
  have p0503 :=
    @g_breq1i
      (syn_ctc (syn_chncard (syn_cxp
            (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cnnc)))
      (syn_ctc (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
      (syn_clec) p0502
  have p0504 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp
              (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))))
        (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      p0426 p0503
  have p0522 :=
    @g_hncardnc
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
        (syn_cnnc))
  have p0523 := Nominal.mp p0475 p0522
  have p0534 :=
    @g_tccl
      (syn_chncard (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
  have p0535 := Nominal.mp p0422 p0534
  have p0536 :=
    @g_pm3_2i
      (.classMem (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))) (syn_cncs))
      (.classMem (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) (syn_cncs))
      p0523 p0535
  have p0537 :=
    @g_tlecg
      (syn_chncard (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cnnc)))
      (syn_ctc (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
  have p0538 := Nominal.mp p0536 p0537
  have p0539 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
              (syn_cnnc)))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))))
      p0504 p0538
  have p0557 :=
    @g_hncardtcshiftndv
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
        (syn_cnnc))
      p0475
  have p0575 :=
    @g_pw1ex
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
        (syn_cnnc))
      p0475
  have p0592 :=
    @g_xpkex
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0420 p0420
  have p0594 :=
    @g_xpex
      (syn_cxpk (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_cnnc) p0592 p0004
  have p0602 :=
    @g_wpplitshiftenndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0312
  have p0621 :=
    @g_eqnc
      (syn_cpw1 (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
        (syn_cnnc))
      p0575
  have p0622 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
              (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
            (syn_cnnc))))
      (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)))
      p0602 p0621
  have p0623 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cnnc)))
      (syn_cxp (syn_cxpk (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
        (syn_cnnc))
      p0575 p0594 p0622
  have p0624 :=
    @g_eqtri
      (syn_ctc (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))))
      (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)))
      p0557 p0623
  have p0625 :=
    @g_breq1i
      (syn_ctc (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cnnc))))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      (syn_clec) p0624
  have p0626 :=
    @g_mpbi
      (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
              (syn_cnnc)))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))))
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))))
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

@[expose]
noncomputable def g_cfbliteralp16onehncardboundndv :
    Nominal.NPrf
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) :=
  by
  have p0000 := @g_cfbliteralp17hncardboundndv
  have p0001 := @g_n_1cex
  have p0002 := @g_pw1ex (syn_c1c) p0001
  have p0003 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0004
  have p0006 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0006
  have p0015 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0007
      p0007
  have p0016 := @g_nncex
  have p0017 :=
    @g_xpex
      (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cnnc) p0015 p0016
  have p0018 := @g_vvex
  have p0019 := @g_pw1ex (syn_cvv) p0018
  have p0020 := @g_pw1ex (syn_cpw1 (syn_cvv)) p0019
  have p0021 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0020
  have p0022 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0021
  have p0023 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0022
  have p0024 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0023
  have p0025 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
      p0024
  have p0034 :=
    @g_xpkex
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0025 p0025
  have p0036 :=
    @g_xpex
      (syn_cxpk (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_cnnc) p0034 p0016
  have p0037 := @g_df1c2
  have p0038 := @g_pw1eq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0039 := Nominal.mp p0037 p0038
  have p0040 := @g_pw1eq (syn_cpw1 (syn_c1c)) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0041 := Nominal.mp p0039 p0040
  have p0042 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0045 := Nominal.mp p0043 p0044
  have p0046 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0047 := Nominal.mp p0045 p0046
  have p0048 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0049 := Nominal.mp p0047 p0048
  have p0063 :=
    @g_xpkeq12i
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0049 p0049
  have p0064 :=
    @g_xpeq1i
      (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cxpk (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
      (syn_cnnc) p0063
  have p0065 :=
    @g_nceqi
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cnnc))
      (syn_cxp (syn_cxpk (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
        (syn_cnnc))
      p0064
  have p0066 :=
    @g_hncardnceqndv
      (syn_cxp (syn_cxpk
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cnnc))
      (syn_cxp (syn_cxpk (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
          (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
        (syn_cnnc))
      p0017 p0036 p0065
  have p0067 :=
    @g_eqcomi
      (syn_chncard (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cnnc)))
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)))
      p0066
  have p0096 :=
    @g_nceqi (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0049
  have p0097 :=
    @g_hncardnceqndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
      p0007 p0025 p0096
  have p0098 :=
    @g_tceq
      (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_chncard (syn_cpw1
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
  have p0099 := Nominal.mp p0097 p0098
  have p0100 :=
    @g_tceq
      (syn_ctc (syn_chncard
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_ctc (syn_chncard (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
  have p0101 := Nominal.mp p0099 p0100
  have p0102 :=
    @g_eqcomi
      (syn_ctc (syn_ctc (syn_chncard
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      p0101
  have p0103 :=
    @g_breq12i
      (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
            (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)))
      (syn_chncard (syn_cxp (syn_cxpk
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cnnc)))
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))
      (syn_ctc (syn_ctc (syn_chncard
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_clec) p0067 p0102
  have p0104 :=
    @g_mpbi
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))))
      (syn_wbr (syn_chncard (syn_cxp (syn_cxpk
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0000 p0103
  exact p0104

@[expose]
noncomputable def g_cfbfixedblockhnqgraphexndv (X : Class)
    (hyp_cfbfixedblockhnqgraphexndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cvv)) :=
  by
  have p0000 := @g_hnordex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0001 := @g_pwex (syn_chnord X) p0000
  have p0002 := @g_pwex (syn_cpw (syn_chnord X)) p0001
  have p0003 := @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0004 := @g_pw1ex (syn_cpw X) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_cpw X)) p0004
  have p0006 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw X))) p0005
  have p0010 :=
    @g_unex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_cpw (syn_cpw (syn_chnord X))) p0006 p0002
  have p0011 :=
    @g_pm3_2i (.classMem (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv))
      (.classMem (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cvv))
      p0002 p0010
  have p0012 :=
    @g_hnqincexg
      (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_cpw (syn_cpw (syn_chnord X)))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_cnvex
      (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
        (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      p0013
  have p0027 :=
    @g_pm3_2i (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cvv))
      (.classMem (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cvv))
      p0006 p0010
  have p0028 :=
    @g_hnqincexg
      (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0029 := Nominal.mp p0027 p0028
  have p0033 := @g_hnsiquomapexgndv (syn_cpw1 (syn_cpw1 (syn_cpw X)))
  have p0034 := Nominal.mp p0005 p0033
  have p0037 := @g_hnsiquomapexgndv (syn_cpw1 (syn_cpw X))
  have p0038 := Nominal.mp p0004 p0037
  have p0039 := @g_siex (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) p0038
  have p0041 := @g_hnsiquomapexgndv (syn_cpw X)
  have p0042 := Nominal.mp p0003 p0041
  have p0043 := @g_siex (syn_chnsiquomap (syn_cpw X)) p0042
  have p0044 := @g_siex (syn_csi (syn_chnsiquomap (syn_cpw X))) p0043
  have p0045 :=
    @g_coex (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
      (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) p0039 p0044
  have p0046 :=
    @g_coex (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
      (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
        (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))
      p0034 p0045
  have p0047 :=
    @g_coex
      (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
        (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
          (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
      p0029 p0046
  have p0048 :=
    @g_coex
      (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X))))))
      (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cpw (syn_cpw (syn_chnord X)))))
        (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
            (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
      p0014 p0047
  have p0050 := @g_hnordex (syn_cpw X) p0003
  have p0051 := @g_pw1ex (syn_chnord (syn_cpw X)) p0050
  have p0052 := @g_pw1ex (syn_cpw1 (syn_chnord (syn_cpw X))) p0051
  have p0053 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) p0052
  have p0054 :=
    @g_resex
      (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
          (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cpw (syn_cpw (syn_chnord X)))))
          (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
            (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
              (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0048 p0053
  exact p0054

@[expose]
noncomputable def g_cfbwppfixedblockhnqinjexndv (f : Var) (X : Class) (dv_X_f : f ∉ X.fv)
    (hyp_cfbwppfixedblockhnqinjexndv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_cfbwppfixedblockhnqinjexndv_2 : Nominal.NPrf
        (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec)
          (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wex f
          (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
            (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))))) :=
  by
  have dv_cache_0001 :
    f ∉
      ((syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))).fv :=
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
      ((syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
                (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                    (syn_cpw (syn_cpw (syn_chnord X)))))
                (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                    (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))).fv :=
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
    @g_cfbwppfixedblockhnqgraphinjndv X hyp_cfbwppfixedblockhnqinjexndv_1
      hyp_cfbwppfixedblockhnqinjexndv_2
  have p0001 := @g_cfbfixedblockhnqgraphexndv X hyp_cfbwppfixedblockhnqinjexndv_1
  have p0002 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
      (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))) (.cv f)
      (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
            (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
  have p0003 :=
    @g_spcegv
      (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))
      f
      (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
            (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cpw (syn_cpw (syn_chnord X)))))
            (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
              (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
      (syn_cvv) dv_cache_0001 dv_cache_0002 p0002
  have p0004 := Nominal.mp p0001 p0003
  have p0005 :=
    @g_syl (syn_wwpp)
      (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X)))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom
              (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                  (syn_cpw (syn_cpw (syn_chnord X)))))
              (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X))))
                (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X))))
                  (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
        (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))
      (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))))
      p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wppfiniteblocknotwppndv : Nominal.NPrf (.neg (syn_wwpp)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  have dv_cache_0001 :
    f ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
  have p0000 := @g_cfbpw16oneexndv
  have p0001 := @g_cfbliteralp16onehncardboundndv
  have p0002 :=
    @g_cfbwppfixedblockhnqinjexndv f
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      dv_cache_0001 p0000 p0001
  have p0003 := @g_cfbfixedblocknotwppfrominjndv f p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end
