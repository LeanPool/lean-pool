/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block017

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part074`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnsicodemap2valclndv (v : Var) (A : Class) (_dv_A_v : v ∉ A.fv)
    (_hyp_hnsicodemap2valclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classEq
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
              (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (.classMem
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
            (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))) :=
  by
  have p0000 := @g_hnsicodemapfndv A
  have p0001 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (.cv v) (syn_chwcn A)) p0000
  have p0002 := @g_id (.classMem (.cv v) (syn_chwcn A))
  have p0003 := @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0004 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0002 p0003
  have p0005 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A))
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0001 p0004
  have p0006 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv v))
      (syn_chnsicodemap A)
  have p0007 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A)))
      p0005 p0006
  have p0008 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))
  have p0009 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
        (syn_cpw1 (syn_chwcn (syn_cpw1 A))))
      p0007 p0008
  have p0010 :=
    @g_hnsicodemapvalclndv (syn_cpw1 A)
      (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
  have p0011 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
        (syn_cpw1 (syn_chwcn (syn_cpw1 A))))
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cop (syn_csi
            (syn_cfv (syn_c1st)
              (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_cpw1
            (syn_cfv (syn_c2nd)
              (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      p0009 p0010
  have p0012 := @g_fvex (syn_csn (.cv v)) (syn_chnsicodemap A)
  have p0013 := @g_unisn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0012
  have p0014 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_c1st) p0013
  have p0015 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c1st)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (.classMem (.cv v) (syn_chwcn A)) p0014
  have p0019 := @g_hnsicodemapvalclndv A (syn_csn (.cv v))
  have p0020 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))))))
      p0004 p0019
  have p0021 := @g_vex v
  have p0022 := @g_unisn (.cv v) p0021
  have p0023 := @g_fveq2i (syn_cuni (syn_csn (.cv v))) (.cv v) (syn_c1st) p0022
  have p0024 :=
    @g_id
      (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)))
  have p0025 :=
    @g_sieqdndv
      (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)))
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)) p0024
  have p0026 := Nominal.mp p0023 p0025
  have p0029 := @g_fveq2i (syn_cuni (syn_csn (.cv v))) (.cv v) (syn_c2nd) p0022
  have p0030 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))
      (syn_cfv (syn_c2nd) (.cv v))
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @g_opeq12i (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))))
      (syn_csi (syn_cfv (syn_c1st) (.cv v)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0026 p0031
  have p0033 :=
    @g_a1i
      (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classMem (.cv v) (syn_chwcn A)) p0032
  have p0034 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      p0020 p0033
  have p0035 := @g_fvex (.cv v) (syn_c1st)
  have p0036 := @g_siex (syn_cfv (syn_c1st) (.cv v)) p0035
  have p0037 := @g_fvex (.cv v) (syn_c2nd)
  have p0038 := @g_pw1ex (syn_cfv (syn_c2nd) (.cv v)) p0037
  have p0039 :=
    @g_op1std (syn_csi (syn_cfv (syn_c1st) (.cv v)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0036 p0038
  have p0040 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
        (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      p0034 p0039
  have p0041 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A))
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
      (syn_csi (syn_cfv (syn_c1st) (.cv v))) p0015 p0040
  have p0042 :=
    @g_id
      (.classEq (syn_cfv (syn_c1st)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_csi (syn_cfv (syn_c1st) (.cv v))))
  have p0043 :=
    @g_sieqdndv
      (.classEq (syn_cfv (syn_c1st)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_csi (syn_cfv (syn_c1st) (.cv v))) p0042
  have p0044 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_c1st)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (.classEq (syn_csi (syn_cfv (syn_c1st)
            (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))))
      p0041 p0043
  have p0047 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_c2nd) p0013
  have p0048 :=
    @g_a1i
      (.classEq (syn_cfv (syn_c2nd)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (.classMem (.cv v) (syn_chwcn A)) p0047
  have p0072 :=
    @g_op2ndd (syn_csi (syn_cfv (syn_c1st) (.cv v)))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0036 p0038
  have p0073 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
        (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v)))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      p0034 p0072
  have p0074 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A))
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0048 p0073
  have p0075 :=
    @g_pw1eq
      (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0076 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_c2nd)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0074 p0075
  have p0077 :=
    @g_opeq12d (.classMem (.cv v) (syn_chwcn A))
      (syn_csi (syn_cfv (syn_c1st)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
      (syn_cpw1 (syn_cfv (syn_c2nd)
          (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0044 p0076
  have p0078 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (syn_cop (syn_csi (syn_cfv (syn_c1st)
            (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_cpw1
          (syn_cfv (syn_c2nd)
            (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0011 p0077
  have p0079 := @g_hnsicodemapfndv (syn_cpw1 A)
  have p0080 :=
    @g_a1i
      (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv v) (syn_chwcn A)) p0079
  have p0091 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A))
      (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
        (syn_cpw1 (syn_chwcn (syn_cpw1 A))))
      p0080 p0009
  have p0092 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))
      (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
      (syn_chnsicodemap (syn_cpw1 A))
  have p0093 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A))
      (syn_wa (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
          (syn_cpw1 (syn_chwcn (syn_cpw1 A)))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0091 p0092
  have p0094 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0078 p0093
  exact p0094


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part075`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodepw12repdndv (v : Var) (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v)
    (hyp_hncodepw12repdndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (syn_wrex v (syn_chwcn A)
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let t : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_v : t ≠ v := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_t_ne_u : t ≠ u := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_v : q ≠ v := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t_ne_q : t ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_t : q ≠ t := Ne.symm fresh_t_ne_q
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_q_ne_z : q ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_q : z ≠ q := Ne.symm fresh_q_ne_z
  have dv_cache_0001 : t ∉ ((syn_cpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_t_not_A,
          not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_u, fresh_t_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cuni (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_t,
          not_false_eq_true])
  have dv_cache_0005 :
    q ∉
      ((syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          Finset.mem_union, Finset.mem_singleton, fresh_q_ne_t, fresh_q_not_A,
          fresh_q_ne_u, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cuni (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_q,
          not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_not_A, fresh_z_ne_u, fresh_z_ne_q,
          or_false, not_false_eq_true])
  have dv_cache_0009 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have dv_cache_0010 : v ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_z, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_v,
          not_false_eq_true])
  have dv_cache_0012 :
    v ∉
      ((syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_v), fresh_v_ne_z, dv_A_v, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    z ∉ ((Wff.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_u,
          fresh_z_ne_v, or_false, and_false, not_false_eq_true])
  have dv_cache_0015 :
    q ∉ ((Wff.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_A, or_false, not_false_eq_true])
  have dv_cache_0016 :
    q ∉
      ((syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_u,
          fresh_q_ne_v, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_u,
          fresh_t_ne_v, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    t ∉ ((Wff.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_u, fresh_t_not_A, or_false, not_false_eq_true])
  have p0000 := @g_pw1ex A hyp_hncodepw12repdndv_1
  have p0001 := @g_pw1ex (syn_cpw1 A) p0000
  have p0002 := @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw1 A)) (.cv u) p0001
  have p0003 := @g_id (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
  have p0004 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (.classMem (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_chnord (syn_cpw1 (syn_cpw1 A)))))
      (.imp (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      p0002 p0003
  have p0006 :=
    @g_hnsiquomappreexclndv t (syn_cpw1 A)
      (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) dv_cache_0001 dv_cache_0002
      p0000
  have p0007 :=
    @g_syl (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_chnord (syn_cpw1 (syn_cpw1 A))))
      (syn_wrex t (syn_cpw1 (syn_chnord (syn_cpw1 A)))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      p0004 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
  have p0009 := @g_pw1argclcl (syn_chnord (syn_cpw1 A)) (.cv t)
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
      (syn_wa (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A)))
        (.classEq (.cv t) (syn_csn (syn_cuni (.cv t)))))
      p0008 p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A)))
      (.classEq (.cv t) (syn_csn (syn_cuni (.cv t))))
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (syn_wa (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A)))
        (.classEq (.cv t) (syn_csn (syn_cuni (.cv t)))))
      (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A))) p0010 p0011
  have p0013 :=
    @g_hnsiquomappreexclndv q A (syn_cuni (.cv t)) dv_cache_0003 dv_cache_0004
      hyp_hncodepw12repdndv_1
  have p0014 :=
    @g_syl
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classMem (syn_cuni (.cv t)) (syn_chnord (syn_cpw1 A)))
      (syn_wrex q (syn_cpw1 (syn_chnord A))
        (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
      p0012 p0013
  have p0015 :=
    @g_nfv
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      q dv_cache_0005
  have p0016 :=
    @g_nfri
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      q p0015
  have p0017 :=
    @g_simpr
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0018 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0017 p0018
  have p0020 := @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0019 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0021 p0022
  have p0024 := @g_vex q
  have p0025 := @g_uniex (.cv q) p0024
  have p0026 := @g_elhnordclndv z A (syn_cuni (.cv q)) dv_cache_0006 dv_cache_0007
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @g_biimpi (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
      p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (syn_cuni (.cv q)) (syn_chnord A))
      (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
      p0023 p0028
  have p0030 :=
    @g_nfv
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      z dv_cache_0008
  have p0031 :=
    @g_nfri
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      z p0030
  have p0032 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0033 :=
    @g_simpl (.classMem (.cv z) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
      (.classMem (.cv z) (syn_chwcn A)) p0032 p0033
  have p0035 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
  have p0036 :=
    @g_simpl
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
  have p0037 :=
    @g_simpr (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
      p0036 p0037
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
      p0035 p0038
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) p0036 p0008
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) p0035 p0043
  have p0045 := @g_hnsicodemapfndv A
  have p0046 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      p0045
  have p0050 := @g_snelpw1 (.cv z) (syn_chwcn A)
  have p0051 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (.cv z) (syn_chwcn A))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))) p0034 p0050
  have p0052 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))) p0046 p0051
  have p0053 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv z))
      (syn_chnsicodemap A)
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)))
        (.classMem (syn_csn (.cv z)) (syn_cpw1 (syn_chwcn A))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A)))
      p0052 p0053
  have p0057 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
  have p0058 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
      (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) p0017 p0057
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))) p0035 p0058
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) p0035 p0019
  have p0069 :=
    @g_simpr (.classMem (.cv z) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) p0032 p0069
  have p0071 := @g_eqid (syn_cec (.cv z) (syn_chwniso A))
  have p0072 :=
    @g_a1i (.classEq (syn_cec (.cv z) (syn_chwniso A)) (syn_cec (.cv z) (syn_chwniso A)))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      p0071
  have p0073 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))
      (syn_cec (.cv z) (syn_chwniso A)) p0070 p0072
  have p0074 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (.cv z) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))) p0034 p0073
  have p0075 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
      p0064 p0074
  have p0076 :=
    @g_hnsiquomaprepvalndv z A q dv_cache_0003 dv_cache_0006 dv_cache_0009
      hyp_hncodepw12repdndv_1
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A))))
      p0075 p0076
  have p0078 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwniso (syn_cpw1 A)))
      p0059 p0077
  have p0079 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A)))
      (.classEq (syn_cuni (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))
          (syn_chwniso (syn_cpw1 A))))
      p0054 p0078
  have p0080 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
      (syn_wa (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))
          (syn_chwcn (syn_cpw1 A))) (.classEq (syn_cuni (.cv t))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))
            (syn_chwniso (syn_cpw1 A)))))
      p0044 p0079
  have p0082 :=
    @g_hnsiquomaprepvalcl2ndv (syn_cpw1 A)
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) t dv_cache_0001 p0000
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (syn_wa
          (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A)))
          (.classEq (syn_cuni (.cv t)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))
              (syn_chwniso (syn_cpw1 A))))))
      (.classEq (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      p0080 p0082
  have p0084 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
      (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))
      (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
        (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
      p0039 p0083
  have p0085 :=
    @g_a1d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      p0003
  have p0086 := @g_hnsicodemapfndv (syn_cpw1 A)
  have p0087 :=
    @g_a1i
      (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      p0086
  have p0098 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A))
  have p0099 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) (syn_chwcn (syn_cpw1 A)))
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))
        (syn_cpw1 (syn_chwcn (syn_cpw1 A))))
      p0054 p0098
  have p0100 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))
        (syn_cpw1 (syn_chwcn (syn_cpw1 A))))
      p0087 p0099
  have p0101 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))
      (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))
      (syn_chnsicodemap (syn_cpw1 A))
  have p0102 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
        (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))
          (syn_cpw1 (syn_chwcn (syn_cpw1 A)))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      p0100 p0101
  have p0103 :=
    @g_pm3_2 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
  have p0104 :=
    @g_syl5
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
        (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      p0102 p0103
  have p0105 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
              (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
                (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
            (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
          (syn_wa (.classMem (.cv z) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
            (syn_chwcn (syn_cpw1 (syn_cpw1 A))))))
      p0085 p0104
  have p0106 :=
    @g_pm2_43d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      p0105
  have p0109 :=
    @g_hwnisoclasseqbcl (syn_cpw1 (syn_cpw1 A)) (.cv u)
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
      p0001
  have p0110 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
          (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))
      p0106 p0109
  have p0111 :=
    @g_bi1
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
  have p0112 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))
      (.imp (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
            (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))
      p0110 p0111
  have p0113 :=
    @g_mpdi (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))) (syn_cec
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
          (syn_chwniso (syn_cpw1 (syn_cpw1 A)))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
      p0084 p0112
  have p0114 :=
    @g_pm3_2 (.classMem (.cv z) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
  have p0115 :=
    @g_syl9 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
      (.classMem (.cv z) (syn_chwcn A))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))
      p0113 p0114
  have p0116 :=
    @g_syl5
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (.classMem (.cv z) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
              (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
                (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
            (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
              (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
          (syn_wa (.classMem (.cv z) (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))))
      p0034 p0115
  have p0117 :=
    @g_pm2_43d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))
      p0116
  have p0118 := @g_id (.classEq (.cv v) (.cv z))
  have p0119 := @g_sneqd (.classEq (.cv v) (.cv z)) (.cv v) (.cv z) p0118
  have p0120 :=
    @g_fveq2d (.classEq (.cv v) (.cv z)) (syn_csn (.cv v)) (syn_csn (.cv z))
      (syn_chnsicodemap A) p0119
  have p0121 :=
    @g_sneqd (.classEq (.cv v) (.cv z)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))
      (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))) p0120
  have p0122 :=
    @g_fveq2d (.classEq (.cv v) (.cv z))
      (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
      (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))
      (syn_chnsicodemap (syn_cpw1 A)) p0121
  have p0123 :=
    @g_breq2d (.classEq (.cv v) (.cv z))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))
      (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
        (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))
      (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))) p0122
  have p0124 :=
    @g_rspcev
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))
      (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
        (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
          (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z))))))
      v (.cv z) (syn_chwcn A) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0123
  have p0125 :=
    @g_syl6 (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
        (syn_wa (.classMem (.cv z) (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))))
      (syn_wa (.classMem (.cv z) (syn_chwcn A))
        (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv z)))))))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0117 p0124
  have p0126 :=
    @g_exp4d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (.cv z) (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0125
  have p0127 :=
    @g_imp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (.cv z) (syn_chwcn A))
      (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
        (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0126
  have p0128 :=
    @g_exp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.classMem (.cv z) (syn_chwcn A))
      (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
        (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0127
  have p0129 :=
    @g_alimdv (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.imp (.classMem (.cv z) (syn_chwcn A))
        (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      z dv_cache_0013 p0128
  have p0130 :=
    @g_syl5
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.all z (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
            (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
              (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
            (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.all z (.imp (.classMem (.cv z) (syn_chwcn A))
          (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
            (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
      p0031 p0129
  have p0131 :=
    (Nominal.biimpRefl (syn_wral z (syn_chwcn A)
        (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
  have p0132 :=
    @g_syl6ibr (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (.all z (.imp (.classMem (.cv z) (syn_chwcn A))
          (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
            (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
      (syn_wral z (syn_chwcn A)
        (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      p0130 p0131
  have p0133 :=
    @g_nfv
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      z dv_cache_0014
  have p0134 :=
    @g_r19_23 (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      z (syn_chwcn A) p0133
  have p0135 :=
    @g_syl6ib (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wral z (syn_chwcn A)
        (.imp (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.imp (syn_wrex z (syn_chwcn A)
          (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
        (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0132 p0134
  have p0136 :=
    @g_mpdi (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))))
      (syn_wrex z (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv z) (syn_chwniso A))))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0029 p0135
  have p0137 :=
    @g_exp4d (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0136
  have p0138 :=
    @g_imp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
        (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0137
  have p0139 :=
    @g_exp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
        (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0138
  have p0140 :=
    @g_alimdv (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
        (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      q dv_cache_0015 p0139
  have p0141 :=
    @g_syl5
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.all q (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
          (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
            (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))))
      (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.all q (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
            (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
      p0016 p0140
  have p0142 :=
    (Nominal.biimpRefl (syn_wral q (syn_cpw1 (syn_chnord A))
        (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
  have p0143 :=
    @g_syl6ibr (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (.all q (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
            (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
                (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                  (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))))
      (syn_wral q (syn_cpw1 (syn_chnord A))
        (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      p0141 p0142
  have p0144 :=
    @g_nfv
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      q dv_cache_0016
  have p0145 :=
    @g_r19_23 (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      q (syn_cpw1 (syn_chnord A)) p0144
  have p0146 :=
    @g_syl6ib (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (syn_wral q (syn_cpw1 (syn_chnord A))
        (.imp (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q)))
          (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
                (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))))
      (.imp (syn_wrex q (syn_cpw1 (syn_chnord A))
          (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
        (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
              (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))
      p0143 p0145
  have p0147 :=
    @g_mpdi (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (syn_wrex q (syn_cpw1 (syn_chnord A))
        (.classEq (syn_cuni (.cv t)) (syn_cfv (syn_chnsiquomap A) (.cv q))))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0014 p0146
  have p0148 :=
    @g_exp3a (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classMem (.cv t) (syn_cpw1 (syn_chnord (syn_cpw1 A))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0147
  have p0149 :=
    @g_rexlimdv (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
        (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t)))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      t (syn_cpw1 (syn_chnord (syn_cpw1 A))) dv_cache_0017 dv_cache_0018 p0148
  have p0150 :=
    @g_mpd (.classMem (.cv u) (syn_chwcn (syn_cpw1 (syn_cpw1 A))))
      (syn_wrex t (syn_cpw1 (syn_chnord (syn_cpw1 A)))
        (.classEq (syn_cec (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A))))
          (syn_cfv (syn_chnsiquomap (syn_cpw1 A)) (.cv t))))
      (syn_wrex v (syn_chwcn A) (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
          (syn_cfv (syn_chnsicodemap (syn_cpw1 A))
            (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))
      p0007 p0149
  exact p0150


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part076`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpquotbrproxyimpndv (v : Var) (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv)
    (hyp_hncodecmpquotbrproxyimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec (.cv v) (syn_chwniso A)))
          (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact dv_A_r))))))
  have p0000 :=
    @g_a1i (.classMem A (syn_cvv))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      hyp_hncodecmpquotbrproxyimpndv_1
  have p0001 := @g_hncodecmpsetexg A
  have p0002 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0004 :=
    @g_eleq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_cvv) p0003
  have p0005 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0002
      p0004
  have p0007 := @g_hncodecmpsetrefndv A
  have p0008 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      p0000 p0007
  have p0010 :=
    @g_breq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0003
  have p0011 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0008 p0010
  have p0013 := @g_hncodecmpsettransndv A
  have p0014 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))
      p0000 p0013
  have p0016 :=
    @g_breq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0003
  have p0017 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0014 p0016
  have p0018 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0011 p0017
  have p0019 := @g_hncodecmpsetssxpndv A
  have p0020 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      p0019
  have p0022 :=
    @g_sseq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0003
  have p0023 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0020 p0022
  have p0024 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
        (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0018 p0023
  have p0025 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0026 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0027 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0025 p0026
  have p0029 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0030 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A)) p0025 p0029
  have p0031 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0027 p0030
  have p0032 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
          (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
        (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0024
      p0031
  have p0033 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv r) (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
            (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
          (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      p0005 p0032
  have p0034 := @g_brlnqordkern (syn_chwcn A) (.cv r) (.cv u) (.cv v) dv_cache_0001
  have p0035 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wa
            (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
              (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
            (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker (.cv r)))
          (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_clnker (.cv r))))
        (syn_wbr (.cv u) (.cv r) (.cv v)))
      p0033 p0034
  have p0037 := @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0038 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0003 p0037
  have p0040 := @g_hncodecmplnkerndv A
  have p0041 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem A (syn_cvv))
      (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0000 p0040
  have p0042 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0038 p0041
  have p0043 := @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) (.cv u)
  have p0044 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (.classEq (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_cec (.cv u) (syn_chwniso A)))
      p0042 p0043
  have p0052 := @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) (.cv v)
  have p0053 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (.classEq (syn_cec (.cv v) (syn_clnker (.cv r))) (syn_cec (.cv v) (syn_chwniso A)))
      p0042 p0052
  have p0054 :=
    @g_breq12d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec (.cv v) (syn_clnker (.cv r))) (syn_cec (.cv v) (syn_chwniso A))
      (syn_clnqord (.cv r) (syn_chwcn A)) p0044 p0053
  have p0055 :=
    @g_bicomd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (.cv v) (syn_clnker (.cv r))))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (.cv v) (syn_chwniso A)))
      p0054
  have p0057 :=
    @g_breqd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (.cv u) (.cv v) p0003
  have p0058 :=
    @g_bicomd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (.cv r) (.cv v)) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      p0057
  have p0059 :=
    @g_n_3bitr4d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (.cv v) (syn_clnker (.cv r))))
      (syn_wbr (.cv u) (.cv r) (.cv v))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (.cv v) (syn_chwniso A)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) p0035 p0055 p0058
  exact p0059

@[expose]
noncomputable def g_hncodecmpquotbrproxyimpclndv (A : Class) (B : Class) (C : Class)
    (r : Var) (dv_A_r : r ∉ A.fv)
    (hyp_hncodecmpquotbrproxyimpclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({ r } : Finset Var)
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0004 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0005 :
    v ∉
      ((Wff.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
            (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_r, fresh_v_not_A, fresh_v_ne_u, fresh_v_not_C,
          or_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0007 :
    u ∉
      ((Wff.imp (.classMem C (syn_chwcn A)) (.imp
            (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
              (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
                (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_C, fresh_u_not_A, fresh_u_ne_r, fresh_u_not_B,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_id
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
  have p0001 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0002 := @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0003 := @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0004 := @g_elex B (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0003 p0004
  have p0006 := @g_biid (.classMem C (syn_chwcn A))
  have p0007 :=
    @g_a1i (syn_wb (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classEq (.cv u) B) p0006
  have p0008 := @g_biid (.classEq (.cv r) (syn_chncodecmpset A))
  have p0009 :=
    @g_a1i
      (syn_wb (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (.cv u) B) p0008
  have p0010 := @g_id (.classEq (.cv u) B)
  have p0011 := @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0010
  have p0014 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A))
      p0011 p0007
  have p0015 :=
    @g_anbi12d (.classEq (.cv u) B) (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) p0009 p0014
  have p0016 := @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0017 :=
    @g_breq1d (.classEq (.cv u) B) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A))
      (syn_clnqord (.cv r) (syn_chwcn A)) p0016
  have p0019 := @g_breq1d (.classEq (.cv u) B) (.cv u) B C (syn_chncodecmpset A) p0010
  have p0020 :=
    @g_bibi12d (.classEq (.cv u) B)
      (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec C (syn_chwniso A)))
      (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec C (syn_chwniso A)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) C) (syn_wbr B (syn_chncodecmpset A) C) p0017
      p0019
  have p0021 :=
    @g_imbi12d (.classEq (.cv u) B)
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C))
      (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))
      p0015 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem C (syn_chwcn A))
      (.classMem C (syn_chwcn A))
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)))
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)))
      p0007 p0021
  have p0023 := @g_elex C (syn_chwcn A)
  have p0025 :=
    @g_a1i
      (syn_wb (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (.cv v) C) p0008
  have p0026 := @g_biid (.classMem (.cv u) (syn_chwcn A))
  have p0027 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv v) C) p0026
  have p0028 := @g_id (.classEq (.cv v) C)
  have p0029 := @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0028
  have p0030 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem C (syn_chwcn A)) p0027 p0029
  have p0031 :=
    @g_anbi12d (.classEq (.cv v) C) (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A))) p0025 p0030
  have p0032 := @g_eceq1 (.cv v) C (syn_chwniso A)
  have p0033 :=
    @g_breq2d (.classEq (.cv v) C) (syn_cec (.cv v) (syn_chwniso A))
      (syn_cec C (syn_chwniso A)) (syn_cec (.cv u) (syn_chwniso A))
      (syn_clnqord (.cv r) (syn_chwcn A)) p0032
  have p0035 :=
    @g_breq2d (.classEq (.cv v) C) (.cv v) C (.cv u) (syn_chncodecmpset A) p0028
  have p0036 :=
    @g_bibi12d (.classEq (.cv v) C)
      (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (.cv v) (syn_chwniso A)))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec C (syn_chwniso A)))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv u) (syn_chncodecmpset A) C) p0033 p0035
  have p0037 :=
    @g_imbi12d (.classEq (.cv v) C)
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C))
      p0031 p0036
  have p0038 :=
    @g_hncodecmpquotbrproxyimpndv v u A r dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hncodecmpquotbrproxyimpclndv_1
  have p0039 :=
    @g_vtoclg
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))))
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)))
      v C (syn_cvv) dv_cache_0004 dv_cache_0005 p0037 p0038
  have p0040 :=
    @g_syl (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv))
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)))
      p0023 p0039
  have p0041 :=
    @g_vtoclg
      (.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
            (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C))))
      (.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
            (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))))
      u B (syn_cvv) dv_cache_0006 dv_cache_0007 p0022 p0040
  have p0042 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_cvv))
      (.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
            (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
              (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))))
      p0005 p0041
  have p0043 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A))
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)))
      p0002 p0042
  have p0044 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
            (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)))
      p0001 p0043
  have p0045 :=
    @g_mpd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))
      p0000 p0044
  exact p0045

@[expose]
noncomputable def g_hncodecmpquotstrictbrproxyimpclndv (A : Class) (B : Class) (C : Class)
    (r : Var) (dv_A_r : r ∉ A.fv)
    (hyp_hncodecmpquotstrictbrproxyimpclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb
          (syn_wbr (syn_cec B (syn_chwniso A))
            (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
            (syn_cec C (syn_chwniso A)))
          (syn_wbr B (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) C))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact dv_A_r))))))
  have p0000 :=
    @g_a1i (.classMem A (syn_cvv))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0001 := @g_hncodecmpsetexg A
  have p0002 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0004 :=
    @g_eleq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_cvv) p0003
  have p0005 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0002
      p0004
  have p0007 := @g_hwcnexg A
  have p0008 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0000 p0007
  have p0009 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0005 p0008
  have p0011 := @g_hncodecmpsetrefndv A
  have p0012 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))
      p0000 p0011
  have p0014 :=
    @g_breq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0003
  have p0015 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0012 p0014
  have p0017 := @g_hncodecmpsettransndv A
  have p0018 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A))
      p0000 p0017
  have p0020 :=
    @g_breq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0003
  have p0021 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0018 p0020
  have p0022 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
      (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0015 p0021
  have p0024 := @g_hncodecmpsetconnexndv A
  have p0025 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))
      p0000 p0024
  have p0027 :=
    @g_breq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cconnex) p0003
  have p0028 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))
      (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0025 p0027
  have p0029 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
        (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
      (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) p0022 p0028
  have p0030 := @g_hncodecmpsetssxpndv A
  have p0031 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      p0030
  have p0033 :=
    @g_sseq1d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0003
  have p0034 :=
    @g_mpbird
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0031 p0033
  have p0035 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
          (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
        (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
      (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0029 p0034
  have p0036 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
            (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
          (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
        (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      p0009 p0035
  have p0037 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0038 := @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0039 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_chwcn A)) p0037 p0038
  have p0041 := @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0042 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A)) p0037 p0041
  have p0043 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0039 p0042
  have p0044 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
              (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
            (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
          (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))))
      (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) p0036 p0043
  have p0045 := @g_brlnqordstrict (syn_chwcn A) (.cv r) B C dv_cache_0001
  have p0046 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
          (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A))
                (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)))
              (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)))
            (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec B (syn_clnker (.cv r)))
          (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
          (syn_cec C (syn_clnker (.cv r)))) (syn_wbr B (syn_cdif (.cv r) (syn_ccnv (.cv r))) C))
      p0044 p0045
  have p0048 := @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0049 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0003 p0048
  have p0051 := @g_hncodecmplnkerndv A
  have p0052 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classMem A (syn_cvv))
      (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0000 p0051
  have p0053 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0049 p0052
  have p0054 := @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) B
  have p0055 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (.classEq (syn_cec B (syn_clnker (.cv r))) (syn_cec B (syn_chwniso A))) p0053 p0054
  have p0063 := @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) C
  have p0064 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.classEq (syn_clnker (.cv r)) (syn_chwniso A))
      (.classEq (syn_cec C (syn_clnker (.cv r))) (syn_cec C (syn_chwniso A))) p0053 p0063
  have p0065 :=
    @g_breq12d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_cec B (syn_clnker (.cv r))) (syn_cec B (syn_chwniso A))
      (syn_cec C (syn_clnker (.cv r))) (syn_cec C (syn_chwniso A))
      (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) p0055 p0064
  have p0066 :=
    @g_bicomd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr (syn_cec B (syn_clnker (.cv r)))
        (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec C (syn_clnker (.cv r))))
      (syn_wbr (syn_cec B (syn_chwniso A))
        (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_chwniso A)))
      p0065
  have p0069 :=
    @g_cnveqd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) p0003
  have p0070 :=
    @g_difeq12d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A))
      p0003 p0069
  have p0071 :=
    @g_breqd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_cdif (.cv r) (syn_ccnv (.cv r)))
      (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) B C p0070
  have p0072 :=
    @g_bicomd
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr B (syn_cdif (.cv r) (syn_ccnv (.cv r))) C)
      (syn_wbr B (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) C)
      p0071
  have p0073 :=
    @g_n_3bitr4d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
      (syn_wbr (syn_cec B (syn_clnker (.cv r)))
        (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec C (syn_clnker (.cv r))))
      (syn_wbr B (syn_cdif (.cv r) (syn_ccnv (.cv r))) C)
      (syn_wbr (syn_cec B (syn_chwniso A))
        (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_chwniso A)))
      (syn_wbr B (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) C)
      p0046 p0066 p0072
  exact p0073

@[expose]
noncomputable def g_hnwcutrelambfnnoarndv (A : Class) (D : Class) (R : Class)
    (hyp_hnwcutrelambfnnoarndv_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnwcutrelambfnnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn A)) :=
  by
  have p0000 := @g_hnwcutrelfndv D R hyp_hnwcutrelambfnnoarndv_2
  have p0001 := @g_hwcnssbase A D hyp_hnwcutrelambfnnoarndv_1
  have p0002 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wss (syn_chwcn D) (syn_chwcn A)) p0000 p0001
  have p0003 := @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0004 := Nominal.mp p0002 p0003
  exact p0004

@[expose]
noncomputable def g_hnwcutambfactorvalnoarndv (A : Class) (D : Class) (R : Class)
    (q : Var) (_dv_D_q : q ∉ D.fv) (_dv_R_q : q ∉ R.fv)
    (hyp_hnwcutambfactorvalnoarndv_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnwcutambfactorvalnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_hnwcutambfactorvalnoarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) :=
  by
  have p0000 :=
    @g_hnwcutrelambfnnoarndv A D R hyp_hnwcutambfactorvalnoarndv_1
      hyp_hnwcutambfactorvalnoarndv_2
  have p0001 := @g_sifmap (syn_cpw1 D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0004 := @g_hnwcutsirelvalndv D R q hyp_hnwcutambfactorvalnoarndv_2
  have p0005 := @g_hwcnssbase A D hyp_hnwcutambfactorvalnoarndv_1
  have p0006 := @g_pw12argcl (.cv q) D
  have p0007 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_hnwcutcodecnclndv (syn_cuni (syn_cuni (.cv q))) D R hyp_hnwcutambfactorvalnoarndv_2
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn D)) p0007
      p0008
  have p0010 :=
    @g_sseldi (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_chwcn D) (syn_chwcn A)
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) p0005 p0009
  have p0011 :=
    @g_qmapcompvald (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) A
      (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_csi (syn_chnwcutrel R D))
      (syn_cpw1 (syn_cpw1 D)) q hyp_hnwcutambfactorvalnoarndv_3 p0002 p0003 p0004 p0010
  exact p0011

@[expose]
noncomputable def g_hnwcutambfactorvalcodendv (A : Class) (B : Class) (q : Var)
    (dv_B_q : q ∉ B.fv)
    (hyp_hnwcutambfactorvalcodendv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_hnwcutambfactorvalcodendv_2 : Nominal.NPrf (.classMem B (syn_chwcn A))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q))
          (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
              (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) :=
  by
  have dv_cache_0001 : q ∉ ((syn_cfv (syn_c2nd) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_B_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cfv (syn_c1st) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, dv_B_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_hwcnbaseclndv A B
  have p0001 := Nominal.mp hyp_hnwcutambfactorvalcodendv_2 p0000
  have p0002 := @g_hwcnweclndv A B
  have p0003 := Nominal.mp hyp_hnwcutambfactorvalcodendv_2 p0002
  have p0004 :=
    @g_hnwcutambfactorvalnoarndv A (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) q
      dv_cache_0001 dv_cache_0002 p0001 p0003 hyp_hnwcutambfactorvalcodendv_1
  exact p0004

@[expose]
noncomputable def g_hnwcuttxpeq1dndv (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_hnwcuttxpeq1dndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ctxp A C) (syn_ctxp B C))) :=
  by
  have p0000 := @g_coeq2d ph A B (syn_ccnv (syn_c1st)) hyp_hnwcuttxpeq1dndv_1
  have p0001 :=
    @g_ineq1d ph (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c1st)) B)
      (syn_ccom (syn_ccnv (syn_c2nd)) C) p0000
  have p0002 := (Nominal.classEqRefl (syn_ctxp A C))
  have p0003 := (Nominal.classEqRefl (syn_ctxp B C))
  have p0004 :=
    @g_n_3eqtr4g ph
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) C))
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) B) (syn_ccom (syn_ccnv (syn_c2nd)) C))
      (syn_ctxp A C) (syn_ctxp B C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_hnwcutimageeqdndv (ph : Wff) (A : Class) (B : Class)
    (hyp_hnwcutimageeqdndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cimage A) (syn_cimage B))) :=
  by
  have p0000 := @g_sieqdndv ph A B hyp_hnwcutimageeqdndv_1
  have p0001 := @g_cnveqd ph (syn_csi A) (syn_csi B) p0000
  have p0002 :=
    @g_coeq2d ph (syn_ccnv (syn_csi A)) (syn_ccnv (syn_csi B)) (syn_csset) p0001
  have p0003 :=
    @g_hnwcuttxpeq1dndv ph (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))
      (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))) (syn_cvv) p0002
  have p0004 :=
    (Nominal.classEqRefl (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))
  have p0005 :=
    (Nominal.classEqRefl (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))))
  have p0006 :=
    @g_n_3eqtr4g ph (syn_ctxp (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv))
      (syn_ctxp (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))) (syn_cvv))
      (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))
      (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) p0003 p0004 p0005
  have p0007 :=
    @g_difeq2d ph (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))
      (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) (syn_cins2 (syn_csset))
      p0006
  have p0015 :=
    @g_difeq1d ph (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))
      (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) (syn_cins2 (syn_csset))
      p0006
  have p0016 :=
    @g_uneq12d ph
      (syn_cdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))
      (syn_cdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))))
      (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))
        (syn_cins2 (syn_csset)))
      (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))
        (syn_cins2 (syn_csset)))
      p0007 p0015
  have p0017 :=
    (Nominal.classEqRefl (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))))
  have p0018 :=
    (Nominal.classEqRefl (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))))
  have p0019 :=
    @g_n_3eqtr4g ph
      (syn_cun (syn_cdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))
        (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))
          (syn_cins2 (syn_csset))))
      (syn_cun (syn_cdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))))
        (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))
          (syn_cins2 (syn_csset))))
      (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))
      (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))))
      p0016 p0017 p0018
  have p0020 :=
    @g_imaeq1d ph
      (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))
      (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))))
      (syn_c1c) p0019
  have p0021 :=
    @g_compleqd ph
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c))
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_c1c))
      p0020
  have p0022 := (Nominal.classEqRefl (syn_cimage A))
  have p0023 := (Nominal.classEqRefl (syn_cimage B))
  have p0024 :=
    @g_n_3eqtr4g ph
      (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)))
      (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_c1c)))
      (syn_cimage A) (syn_cimage B) p0021 p0022 p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part077`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutreleq12dndv (ph : Wff) (D : Class) (R : Class) (S : Class)
    (E : Class) (hyp_hnwcutreleq12dndv_1 : Nominal.NPrf (.imp ph (.classEq R S)))
    (hyp_hnwcutreleq12dndv_2 : Nominal.NPrf (.imp ph (.classEq D E))) :
    Nominal.NPrf (.imp ph (.classEq (syn_chnwcutrel R D) (syn_chnwcutrel S E))) :=
  by
  have p0000 := @g_reseq2d ph R S (syn_cid) hyp_hnwcutreleq12dndv_1
  have p0001 :=
    @g_hnwcutimageeqdndv ph (syn_cres (syn_cid) R) (syn_cres (syn_cid) S) p0000
  have p0002 :=
    @g_coeq1d ph (syn_cimage (syn_cres (syn_cid) R)) (syn_cimage (syn_cres (syn_cid) S))
      (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))) p0001
  have p0003 :=
    @g_hnwcuttxpeq1dndv ph
      (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
        (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))))
      (syn_ccom (syn_cimage (syn_cres (syn_cid) S))
        (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid))))
      (syn_cid) p0002
  have p0004 := (Nominal.classEqRefl (syn_chnwcodefn R))
  have p0005 := (Nominal.classEqRefl (syn_chnwcodefn S))
  have p0006 :=
    @g_n_3eqtr4g ph
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) R))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      (syn_ctxp (syn_ccom (syn_cimage (syn_cres (syn_cid) S))
          (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_cid)))) (syn_cid))
      (syn_chnwcodefn R) (syn_chnwcodefn S) p0003 p0004 p0005
  have p0007 := @g_reseq2d ph D E (syn_cid) hyp_hnwcutreleq12dndv_2
  have p0008 :=
    @g_hnwcutimageeqdndv ph (syn_cres (syn_cid) D) (syn_cres (syn_cid) E) p0007
  have p0009 := @g_difeq1d ph R S (syn_cid) hyp_hnwcutreleq12dndv_1
  have p0010 := @g_cnveqd ph (syn_cdif R (syn_cid)) (syn_cdif S (syn_cid)) p0009
  have p0011 :=
    @g_hnwcutimageeqdndv ph (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_ccnv (syn_cdif S (syn_cid))) p0010
  have p0012 :=
    @g_coeq12d ph (syn_cimage (syn_cres (syn_cid) D)) (syn_cimage (syn_cres (syn_cid) E))
      (syn_cimage (syn_ccnv (syn_cdif R (syn_cid))))
      (syn_cimage (syn_ccnv (syn_cdif S (syn_cid)))) p0008 p0011
  have p0013 := (Nominal.classEqRefl (syn_chnwsegfn R D))
  have p0014 := (Nominal.classEqRefl (syn_chnwsegfn S E))
  have p0015 :=
    @g_n_3eqtr4g ph
      (syn_ccom (syn_cimage (syn_cres (syn_cid) D))
        (syn_cimage (syn_ccnv (syn_cdif R (syn_cid)))))
      (syn_ccom (syn_cimage (syn_cres (syn_cid) E))
        (syn_cimage (syn_ccnv (syn_cdif S (syn_cid)))))
      (syn_chnwsegfn R D) (syn_chnwsegfn S E) p0012 p0013 p0014
  have p0016 :=
    @g_coeq12d ph (syn_chnwcodefn R) (syn_chnwcodefn S) (syn_chnwsegfn R D)
      (syn_chnwsegfn S E) p0006 p0015
  have p0017 := (Nominal.classEqRefl (syn_chnwcutfn R D))
  have p0018 := (Nominal.classEqRefl (syn_chnwcutfn S E))
  have p0019 :=
    @g_n_3eqtr4g ph (syn_ccom (syn_chnwcodefn R) (syn_chnwsegfn R D))
      (syn_ccom (syn_chnwcodefn S) (syn_chnwsegfn S E)) (syn_chnwcutfn R D)
      (syn_chnwcutfn S E) p0016 p0017 p0018
  have p0020 := @g_reseq1 (syn_chnwcutfn R D) (syn_chnwcutfn S E) (syn_cpw1 D)
  have p0021 :=
    @g_syl ph (.classEq (syn_chnwcutfn R D) (syn_chnwcutfn S E))
      (.classEq (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D))
        (syn_cres (syn_chnwcutfn S E) (syn_cpw1 D)))
      p0019 p0020
  have p0022 := @g_pw1eq D E
  have p0023 :=
    @g_syl ph (.classEq D E) (.classEq (syn_cpw1 D) (syn_cpw1 E)) hyp_hnwcutreleq12dndv_2
      p0022
  have p0024 := @g_reseq2d ph (syn_cpw1 D) (syn_cpw1 E) (syn_chnwcutfn S E) p0023
  have p0025 :=
    @g_eqtrd ph (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D))
      (syn_cres (syn_chnwcutfn S E) (syn_cpw1 D))
      (syn_cres (syn_chnwcutfn S E) (syn_cpw1 E)) p0021 p0024
  have p0026 := (Nominal.classEqRefl (syn_chnwcutrel R D))
  have p0027 := (Nominal.classEqRefl (syn_chnwcutrel S E))
  have p0028 :=
    @g_n_3eqtr4g ph (syn_cres (syn_chnwcutfn R D) (syn_cpw1 D))
      (syn_cres (syn_chnwcutfn S E) (syn_cpw1 E)) (syn_chnwcutrel R D)
      (syn_chnwcutrel S E) p0025 p0026 p0027
  exact p0028

@[expose]
noncomputable def g_hnwcutcodeeq12clndv (C : Class) (D : Class) (R : Class) (S : Class)
    (E : Class) :
    Nominal.NPrf
      (.imp (.classMem C (syn_cvv)) (.imp (syn_wa (.classEq R S) (.classEq D E))
          (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
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
  have dv_cache_0002 : Disjoint ((Class.cv x)).fv (S).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv x)).fv (S).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((S).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (S).fv from (by exact fresh_x_not_S))))))
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.imp (syn_wa (.classEq R S) (.classEq D E))
          (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          Finset.mem_union, fresh_x_not_R, fresh_x_not_S, fresh_x_not_D, fresh_x_not_E,
          fresh_x_not_C, or_false, not_false_eq_true])
  have p0000 := @g_biid (syn_wa (.classEq R S) (.classEq D E))
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wa (.classEq R S) (.classEq D E)) (syn_wa (.classEq R S) (.classEq D E)))
      (.classEq (.cv x) C) p0000
  have p0002 := @g_hnwcutcodeeq3 (.cv x) C D R dv_cache_0001
  have p0003 := @g_hnwcutcodeeq3 (.cv x) C E S dv_cache_0002
  have p0004 :=
    @g_eqeq12d (.classEq (.cv x) C) (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D C)
      (syn_chnwcutcode S E (.cv x)) (syn_chnwcutcode S E C) p0002 p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv x) C) (syn_wa (.classEq R S) (.classEq D E))
      (syn_wa (.classEq R S) (.classEq D E))
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv x)))
      (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)) p0001 p0004
  have p0006 := @g_hnwcutcodeeq12ndv x D R S E
  have p0007 :=
    @g_vtoclg
      (.imp (syn_wa (.classEq R S) (.classEq D E))
        (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv x))))
      (.imp (syn_wa (.classEq R S) (.classEq D E))
        (.classEq (syn_chnwcutcode R D C) (syn_chnwcutcode S E C)))
      x C (syn_cvv) dv_cache_0003 dv_cache_0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_hnwcutambfactorvalimpclndv (A : Class) (B : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_B_q : q ∉ B.fv)
    (hyp_hnwcutambfactorvalimpclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chwcn A))
        (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A)
                (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
              (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
                (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))) :=
  by
  have dv_cache_0001 :
    q ∉
      ((syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_c0)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, dv_B_q,
          dv_A_q, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_id
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0001 :=
    @g_fveq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      B
      (syn_cif (.classMem B (syn_chwcn A)) B
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c2nd) p0000
  have p0002 :=
    @g_pw1eq (syn_cfv (syn_c2nd) B)
      (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0003 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      p0001 p0002
  have p0004 :=
    @g_pw1eq (syn_cpw1 (syn_cfv (syn_c2nd) B))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
  have p0005 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1
            (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
      p0003 p0004
  have p0006 :=
    @g_eleq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.cv q) p0005
  have p0008 :=
    @g_fveq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      B
      (syn_cif (.classMem B (syn_chwcn A)) B
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c1st) p0000
  have p0011 :=
    @g_hnwcutreleq12dndv
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0008 p0001
  have p0012 :=
    @g_sieqdndv
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))
      (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0011
  have p0013 :=
    @g_coeq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))
      (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_chnqmap1 A) p0012
  have p0014 :=
    @g_fveq1d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.cv q)
      (syn_ccom (syn_chnqmap1 A)
        (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
      (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
      p0013
  have p0019 :=
    @g_jca
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st)
          (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0008 p0001
  have p0020 := @g_vex q
  have p0021 := @g_uniex (.cv q) p0020
  have p0022 := @g_uniex (syn_cuni (.cv q)) p0021
  have p0023 :=
    @g_hnwcutcodeeq12clndv (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) B)
      (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))) (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
          (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))))
      p0019 p0024
  have p0026 :=
    @g_eceq1
      (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
        (syn_cuni (syn_cuni (.cv q))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cuni (syn_cuni (.cv q))))
      (syn_chwniso A)
  have p0027 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
          (syn_cuni (syn_cuni (.cv q)))) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))))
      (.classEq (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode
            (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0025 p0026
  have p0028 :=
    @g_eqeq12d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_ccom (syn_chnqmap1 A)
          (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))))))) (.cv q))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
          (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
      p0014 p0027
  have p0029 :=
    @g_imbi12d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q))
        (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                  (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                    (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0))))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0006 p0028
  have p0030 := @g_eqid (syn_c0)
  have p0031 := @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A))
  have p0032 := @g_hncodecmpdefaultcnndv A
  have p0033 :=
    @g_a1i
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem B (syn_chwcn A)))) p0032
  have p0034 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A)) B
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A) p0031 p0033
  have p0035 := Nominal.mp p0030 p0034
  have p0036 :=
    @g_hnwcutambfactorvalcodendv A
      (syn_cif (.classMem B (syn_chwcn A)) B
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      q dv_cache_0001 hyp_hnwcutambfactorvalimpclndv_1 p0035
  have p0037 :=
    @g_dedth (.classMem B (syn_chwcn A))
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q))
          (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)
              (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0))))))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))
      B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      p0029 p0036
  exact p0037

@[expose]
noncomputable def g_hnwcutambfactorvalimpndv (u : Var) (A : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (_dv_A_u : u ∉ A.fv) (dv_q_u : q ≠ u)
    (hyp_hnwcutambfactorvalimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv q)) (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))) :=
  by
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_q_u,
          not_false_eq_true])
  have p0000 :=
    @g_hnwcutambfactorvalimpclndv A (.cv u) q dv_cache_0001 dv_cache_0002
      hyp_hnwcutambfactorvalimpndv_1
  exact p0000


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part078`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutambordbrproxyimpndv (u : Var) (A : Class) (r : Var) (q : Var)
    (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_q : q ∉ A.fv) (dv_A_r : r ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (_dv_p_q : p ≠ q) (_dv_p_r : p ≠ r) (dv_p_u : p ≠ u)
    (_dv_q_r : q ≠ r) (dv_q_u : q ≠ u) (_dv_r_u : r ≠ u)
    (hyp_hnwcutambordbrproxyimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A)))
          (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
            (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
        (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
          (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A)
                (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))))) :=
  by
  have dv_cache_0001 : p ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_p_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0004 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_p, not_false_eq_true])
  have dv_cache_0005 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show p ≠ u from (by exact dv_p_u))
  have dv_cache_0006 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_q, not_false_eq_true])
  have dv_cache_0007 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show q ≠ u from (by exact dv_q_u))
  have p0000 :=
    @g_simpr
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0001 :=
    @g_pw12si2brndv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) q p
      dv_cache_0001
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
        (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @g_a1i (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      hyp_hnwcutambordbrproxyimpndv_1
  have p0004 :=
    @g_simpl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
  have p0005 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0004 p0005
  have p0008 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0000 p0008
  have p0010 := @g_pw12argcl (.cv p) (syn_cfv (syn_c2nd) (.cv u))
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
        (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))))
      p0009 p0010
  have p0012 :=
    @g_simpld
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
      (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0011
  have p0014 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0000 p0014
  have p0016 := @g_pw12argcl (.cv q) (syn_cfv (syn_c2nd) (.cv u))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)))
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0015 p0016
  have p0018 :=
    @g_simpld
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) p0012 p0018
  have p0020 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))))
      p0006 p0019
  have p0021 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
          (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u)))))
      p0003 p0020
  have p0022 :=
    @g_hnwcutcodecmpbrclndv u A (syn_cuni (syn_cuni (.cv p)))
      (syn_cuni (syn_cuni (.cv q))) dv_cache_0002
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
            (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))))
        (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))))
      p0021 p0022
  have p0024 :=
    @g_bicomd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))))
      (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u))
        (syn_cuni (syn_cuni (.cv q))))
      p0023
  have p0025 :=
    @g_bitrd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
      (syn_wbr (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (.cv u))
        (syn_cuni (syn_cuni (.cv q))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))))
      p0002 p0024
  have p0027 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv r) (syn_chncodecmpset A)) p0004 p0027
  have p0038 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))) p0006 p0012
  have p0039 := @g_hnwcutcodeambientclndv u A (syn_cuni (syn_cuni (.cv p))) dv_cache_0002
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A))
      p0038 p0039
  have p0050 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))) p0006 p0018
  have p0051 := @g_hnwcutcodeambientclndv u A (syn_cuni (syn_cuni (.cv q))) dv_cache_0002
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A))
      p0050 p0051
  have p0053 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A))
      p0040 p0052
  have p0054 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A)))
      p0028 p0053
  have p0055 :=
    @g_hncodecmpquotbrproxyimpclndv A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cuni (syn_cuni (.cv p))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cuni (syn_cuni (.cv q))))
      r dv_cache_0003 hyp_hnwcutambordbrproxyimpndv_1
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv p)))) (syn_chwcn A)) (.classMem
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))
          (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q))))))
      p0054 p0055
  have p0057 :=
    @g_bicomd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wbr (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))))
      p0056
  have p0058 :=
    @g_bitrd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chncodecmpset A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))))
      (syn_wbr (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0025 p0057
  have p0065 :=
    @g_hnwcutambfactorvalimpndv u A p dv_cache_0004 dv_cache_0002 dv_cache_0005
      hyp_hnwcutambordbrproxyimpndv_1
  have p0066 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv u) (syn_chwcn A))
      (.imp (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))))
      p0006 p0065
  have p0067 :=
    @g_mpd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)))
      p0009 p0066
  have p0074 :=
    @g_hnwcutambfactorvalimpndv u A q dv_cache_0006 dv_cache_0002 dv_cache_0007
      hyp_hnwcutambordbrproxyimpndv_1
  have p0075 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv u) (syn_chwcn A))
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv q)) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))
      p0006 p0074
  have p0076 :=
    @g_mpd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv q)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0015 p0075
  have p0077 :=
    @g_breq12d
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv p))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv q))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
      (syn_clnqord (.cv r) (syn_chwcn A)) p0067 p0076
  have p0078 :=
    @g_bicomd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A)
            (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv q)))
      (syn_wbr (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0077
  have p0079 :=
    @g_bitrd
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
          (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
      (syn_wbr (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A)
            (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv q)))
      p0058 p0078
  exact p0079

@[expose]
noncomputable def g_hnwcutambfactorfnnoarndv (A : Class) (D : Class) (R : Class)
    (hyp_hnwcutambfactorfnnoarndv_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnwcutambfactorfnnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_hnwcutambfactorfnnoarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
        (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) :=
  by
  have p0000 := @g_hnqmap1f A hyp_hnwcutambfactorfnnoarndv_3
  have p0001 := @g_hnwcutrelfndv D R hyp_hnwcutambfactorfnnoarndv_2
  have p0002 := @g_hwcnssbase A D hyp_hnwcutambfactorfnnoarndv_1
  have p0003 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D))
      (syn_wss (syn_chwcn D) (syn_chwcn A)) p0001 p0002
  have p0004 := @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_sifmap (syn_cpw1 D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))
      (syn_wf (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn A)))
      p0000 p0007
  have p0009 :=
    @g_fco (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)
      (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

@[expose]
noncomputable def g_hnwcutclassinjambnoarndv (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (hyp_hnwcutclassinjambnoarndv_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnwcutclassinjambnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_hnwcutclassinjambnoarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
            (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))) (.classEq B C))) :=
  by
  have p0000 :=
    @g_simpr (syn_wa (.classMem B D) (.classMem C D))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0001 :=
    @g_simpl (syn_wa (.classMem B D) (.classMem C D))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
  have p0002 := @g_hwcnssbase A D hyp_hnwcutclassinjambnoarndv_1
  have p0003 := @g_simpl (.classMem B D) (.classMem C D)
  have p0004 := @g_hnwcutcodecnclndv B D R hyp_hnwcutclassinjambnoarndv_2
  have p0005 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D)
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn D)) p0003 p0004
  have p0006 :=
    @g_sseldi (syn_wa (.classMem B D) (.classMem C D)) (syn_chwcn D) (syn_chwcn A)
      (syn_chnwcutcode R D B) p0002 p0005
  have p0008 := @g_simpr (.classMem B D) (.classMem C D)
  have p0009 := @g_hnwcutcodecnclndv C D R hyp_hnwcutclassinjambnoarndv_2
  have p0010 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D)
      (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0008 p0009
  have p0011 :=
    @g_sseldi (syn_wa (.classMem B D) (.classMem C D)) (syn_chwcn D) (syn_chwcn A)
      (syn_chnwcutcode R D C) p0002 p0010
  have p0012 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D))
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn A))
      (.classMem (syn_chnwcutcode R D C) (syn_chwcn A)) p0006 p0011
  have p0013 :=
    @g_hwnisoclasseqbcl A (syn_chnwcutcode R D B) (syn_chnwcutcode R D C)
      hyp_hnwcutclassinjambnoarndv_3
  have p0014 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D))
      (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn A))
        (.classMem (syn_chnwcutcode R D C) (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
        (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)))
      p0012 p0013
  have p0015 :=
    @g_biimpd (syn_wa (.classMem B D) (.classMem C D))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
      (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)) p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wa (.classMem B D) (.classMem C D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
        (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)))
      p0001 p0015
  have p0017 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
      (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C)) p0000
      p0016
  have p0025 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D))
      (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))
      (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)) p0005 p0010
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wa (.classMem B D) (.classMem C D))
      (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))
        (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)))
      p0001 p0025
  have p0027 := @g_hwnisobaserestrcl A (syn_chnwcutcode R D B) (syn_chnwcutcode R D C) D
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))
        (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)))
      (.imp (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C))
        (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)))
      p0026 p0027
  have p0029 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso A) (syn_chnwcutcode R D C))
      (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)) p0017
      p0028
  have p0039 := @g_brex R D (syn_cwe)
  have p0040 := Nominal.mp hyp_hnwcutclassinjambnoarndv_2 p0039
  have p0041 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0040
  have p0042 :=
    @g_hwnisoclasseqbcl D (syn_chnwcutcode R D B) (syn_chnwcutcode R D C) p0041
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wa (.classMem (syn_chnwcutcode R D B) (syn_chwcn D))
        (.classMem (syn_chnwcutcode R D C) (syn_chwcn D)))
      (syn_wb (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
        (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)))
      p0026 p0042
  have p0044 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C)) p0043
  have p0045 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wbr (syn_chnwcutcode R D B) (syn_chwniso D) (syn_chnwcutcode R D C))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      p0029 p0044
  have p0047 := @g_hnwcutclassinjclndv B C D R hyp_hnwcutclassinjambnoarndv_2
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (syn_wa (.classMem B D) (.classMem C D))
      (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))
      p0001 p0047
  have p0049 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem B D) (.classMem C D))
        (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A))))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)))
      (.classEq B C) p0045 p0048
  have p0050 :=
    @g_ex (syn_wa (.classMem B D) (.classMem C D))
      (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso A))
        (syn_cec (syn_chnwcutcode R D C) (syn_chwniso A)))
      (.classEq B C) p0049
  exact p0050


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part079`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutambfactorf1noarndv (A : Class) (D : Class) (R : Class)
    (hyp_hnwcutambfactorf1noarndv_1 : Nominal.NPrf (syn_wss D A))
    (hyp_hnwcutambfactorf1noarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_hnwcutambfactorf1noarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
        (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0003 : r ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_D, not_false_eq_true])
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
  have dv_cache_0005 : r ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_D,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0009 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0010 :
    q ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, fresh_q_not_A, fresh_q_not_D, fresh_q_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    r ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          Finset.mem_union, fresh_r_not_A, fresh_r_not_D, fresh_r_not_R, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_hnwcutambfactorfnnoarndv A D R hyp_hnwcutambfactorf1noarndv_1
      hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
        (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
  have p0002 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0003 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0002 p0003
  have p0005 := @g_pw12argcl (.cv q) D
  have p0006 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D)
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @g_simprd
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0001 p0007
  have p0013 :=
    @g_hnwcutambfactorvalnoarndv A D R q dv_cache_0001 dv_cache_0002
      hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2
      hyp_hnwcutambfactorf1noarndv_3
  have p0014 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0004 p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0001 p0014
  have p0016 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) p0015
  have p0017 :=
    @g_simpr
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
        (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
  have p0018 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)) p0016
      p0017
  have p0021 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) p0002 p0021
  have p0023 :=
    @g_hnwcutambfactorvalnoarndv A D R r dv_cache_0003 dv_cache_0004
      hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2
      hyp_hnwcutambfactorf1noarndv_3
  have p0024 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A)))
      p0022 p0023
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A)))
      p0001 p0024
  have p0026 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))
      (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A)) p0018
      p0025
  have p0033 :=
    @g_simpld
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0001 p0033
  have p0039 := @g_pw12argcl (.cv r) D
  have p0040 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) D)
        (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))))
      p0022 p0039
  have p0041 :=
    @g_simpld
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) D)
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0001 p0041
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (.classMem (syn_cuni (syn_cuni (.cv q))) D)
      (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0034 p0042
  have p0044 :=
    @g_hnwcutclassinjambnoarndv A (syn_cuni (syn_cuni (.cv q)))
      (syn_cuni (syn_cuni (.cv r))) D R hyp_hnwcutambfactorf1noarndv_1
      hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D)
        (.classMem (syn_cuni (syn_cuni (.cv r))) D))
      (.imp (.classEq
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
          (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A)))
        (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))))
      p0043 p0044
  have p0046 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
        (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A)))
      (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))) p0026 p0045
  have p0047 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) p0046
  have p0048 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (.cv r))))
      p0047
  have p0049 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0008 p0048
  have p0056 :=
    @g_simprd
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classMem (syn_cuni (syn_cuni (.cv r))) D)
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0040
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0001 p0056
  have p0058 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0057
  have p0059 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
            (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))))
      (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) (.cv r) p0049 p0058
  have p0060 :=
    @g_ex
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
        (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0059
  have p0061 :=
    @g_ralrimivva (syn_wbr R (syn_cwe) D)
      (.imp (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
        (.classEq (.cv q) (.cv r)))
      q r (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cpw1 D)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0060
  have p0062 := Nominal.mp hyp_hnwcutambfactorf1noarndv_2 p0061
  have p0063 :=
    @g_pm3_2i
      (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
        (syn_cpw1 (syn_cpw1 D)) (syn_chnord A))
      (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq
              (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
              (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
            (.classEq (.cv q) (.cv r)))))
      p0000 p0062
  have p0064 :=
    @g_dff13 q r (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)
      (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) dv_cache_0009
      dv_cache_0005 dv_cache_0010 dv_cache_0011 dv_cache_0008
  have p0065_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
          (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wa
          (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
            (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wral q (syn_cpw1 (syn_cpw1 D))
            (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq
                  (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
                  (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
                (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cpw1 syn_chnord syn_cqs
          syn_wrex syn_cec syn_cima syn_csn syn_chwcn syn_chwniso
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
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
      p0064
  have p0065 :=
    @g_mpbir
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
        (syn_cpw1 (syn_cpw1 D)) (syn_chnord A))
      (syn_wa (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))
          (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wral q (syn_cpw1 (syn_cpw1 D))
          (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq
                (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q))
                (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
              (.classEq (.cv q) (.cv r))))))
      p0063 p0065_e01_recanon
  exact p0065

@[expose]
noncomputable def g_hnwcutambfactorf1codendv (A : Class) (B : Class)
    (hyp_hnwcutambfactorf1codendv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_hnwcutambfactorf1codendv_2 : Nominal.NPrf (.classMem B (syn_chwcn A))) :
    Nominal.NPrf
      (syn_wf1 (syn_ccom (syn_chnqmap1 A)
          (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) :=
  by
  have p0000 := @g_hwcnbaseclndv A B
  have p0001 := Nominal.mp hyp_hnwcutambfactorf1codendv_2 p0000
  have p0002 := @g_hwcnweclndv A B
  have p0003 := Nominal.mp hyp_hnwcutambfactorf1codendv_2 p0002
  have p0004 :=
    @g_hnwcutambfactorf1noarndv A (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) p0001
      p0003 hyp_hnwcutambfactorf1codendv_1
  exact p0004

@[expose]
noncomputable def g_hnwcutambfactorf1impclndv (A : Class) (B : Class)
    (hyp_hnwcutambfactorf1impclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A))) :=
  by
  have p0000 :=
    @g_id
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0001 :=
    @g_fveq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      B
      (syn_cif (.classMem B (syn_chwcn A)) B
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c1st) p0000
  have p0003 :=
    @g_fveq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      B
      (syn_cif (.classMem B (syn_chwcn A)) B
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c2nd) p0000
  have p0004 :=
    @g_hnwcutreleq12dndv
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0001 p0003
  have p0005 :=
    @g_sieqdndv
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))
      (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0004
  have p0006 :=
    @g_coeq2d
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))
      (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_chnqmap1 A) p0005
  have p0007 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)
      (syn_ccom (syn_chnqmap1 A)
        (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
      (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
  have p0008 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_ccom (syn_chnqmap1 A)
          (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
        (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))))))))
      (syn_wb (syn_wf1 (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1
          (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                  (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                    (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)))
      p0006 p0007
  have p0011 :=
    @g_pw1eq (syn_cfv (syn_c2nd) B)
      (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0012 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      p0003 p0011
  have p0013 :=
    @g_pw1eq (syn_cpw1 (syn_cfv (syn_c2nd) B))
      (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
  have p0014 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd)
            (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1
            (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
      p0012 p0013
  have p0015 :=
    @g_f1eq2 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_chnord A)
      (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
  have p0016 :=
    @g_syl
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1
            (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))))
      (syn_wb (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                  (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                    (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1
          (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                  (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                    (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))))) (syn_chnord A)))
      p0014 p0015
  have p0017 :=
    @g_bitrd
      (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A)
          (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))) (syn_chnord A))
      p0008 p0016
  have p0018 := @g_eqid (syn_c0)
  have p0019 := @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A))
  have p0020 := @g_hncodecmpdefaultcnndv A
  have p0021 :=
    @g_a1i
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem B (syn_chwcn A)))) p0020
  have p0022 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A)) B
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A) p0019 p0021
  have p0023 := Nominal.mp p0018 p0022
  have p0024 :=
    @g_hnwcutambfactorf1codendv A
      (syn_cif (.classMem B (syn_chwcn A)) B
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      hyp_hnwcutambfactorf1impclndv_1 p0023
  have p0025 :=
    @g_dedth (.classMem B (syn_chwcn A))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A)
          (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st)
                (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd)
              (syn_cif (.classMem B (syn_chwcn A)) B
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))))) (syn_chnord A))
      B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      p0017 p0024
  exact p0025

@[expose]
noncomputable def g_hnwcutambfactorf1impndv (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv)
    (hyp_hnwcutambfactorf1impndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A))) :=
  by
  have p0000 := @g_hnwcutambfactorf1impclndv A (.cv u) hyp_hnwcutambfactorf1impndv_1
  exact p0000


end NFChoice.DirectNominalPrf.WPPReplay

end
