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

/-- Checked nominal proof certificate identified upstream as `g_hnsicodemap2valclndv`. -/
@[expose]
noncomputable def gHnsicodemap2valclndv (v : Var) (A : Class) (_dv_A_v : v ∉ A.fv)
    (_hyp_hnsicodemap2valclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (synChwcn A)) (synWa (.classEq
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
              (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))) (.classMem
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
            (synChwcn (synCpw1 (synCpw1 A)))))) :=
  by
  have p0000 := @gHnsicodemapfndv A
  have p0001 :=
    @gA1i (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (.classMem (.cv v) (synChwcn A)) p0000
  have p0002 := @gId (.classMem (.cv v) (synChwcn A))
  have p0003 := @gSnelpw1 (.cv v) (synChwcn A)
  have p0004 :=
    @gSylibr (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A))) p0002 p0003
  have p0005 :=
    @gJca (.classMem (.cv v) (synChwcn A))
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A))) p0001 p0004
  have p0006 :=
    @gFfvelrn (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synCsn (.cv v))
      (synChnsicodemap A)
  have p0007 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A))))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwcn (synCpw1 A)))
      p0005 p0006
  have p0008 :=
    @gSnelpw1 (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwcn (synCpw1 A))
  have p0009 :=
    @gSylibr (.classMem (.cv v) (synChwcn A))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
        (synCpw1 (synChwcn (synCpw1 A))))
      p0007 p0008
  have p0010 :=
    @gHnsicodemapvalclndv (synCpw1 A)
      (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
  have p0011 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
        (synCpw1 (synChwcn (synCpw1 A))))
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))) (synCop (synCsi
            (synCfv (synC1st)
              (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))) (synCpw1
            (synCfv (synC2nd)
              (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      p0009 p0010
  have p0012 := @gFvex (synCsn (.cv v)) (synChnsicodemap A)
  have p0013 := @gUnisn (synCfv (synChnsicodemap A) (synCsn (.cv v))) p0012
  have p0014 :=
    @gFveq2i (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synC1st) p0013
  have p0015 :=
    @gA1i
      (.classEq (synCfv (synC1st)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCfv (synC1st) (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (.classMem (.cv v) (synChwcn A)) p0014
  have p0019 := @gHnsicodemapvalclndv A (synCsn (.cv v))
  have p0020 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (.classMem (synCsn (.cv v)) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synChnsicodemap A) (synCsn (.cv v)))
        (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn (.cv v)))))
          (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (.cv v)))))))
      p0004 p0019
  have p0021 := @gVex v
  have p0022 := @gUnisn (.cv v) p0021
  have p0023 := @gFveq2i (synCuni (synCsn (.cv v))) (.cv v) (synC1st) p0022
  have p0024 :=
    @gId
      (.classEq (synCfv (synC1st) (synCuni (synCsn (.cv v)))) (synCfv (synC1st) (.cv v)))
  have p0025 :=
    @gSieqdndv
      (.classEq (synCfv (synC1st) (synCuni (synCsn (.cv v)))) (synCfv (synC1st) (.cv v)))
      (synCfv (synC1st) (synCuni (synCsn (.cv v)))) (synCfv (synC1st) (.cv v)) p0024
  have p0026 := Nominal.mp p0023 p0025
  have p0029 := @gFveq2i (synCuni (synCsn (.cv v))) (.cv v) (synC2nd) p0022
  have p0030 :=
    @gPw1eq (synCfv (synC2nd) (synCuni (synCsn (.cv v))))
      (synCfv (synC2nd) (.cv v))
  have p0031 := Nominal.mp p0029 p0030
  have p0032 :=
    @gOpeq12i (synCsi (synCfv (synC1st) (synCuni (synCsn (.cv v)))))
      (synCsi (synCfv (synC1st) (.cv v)))
      (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (.cv v)))))
      (synCpw1 (synCfv (synC2nd) (.cv v))) p0026 p0031
  have p0033 :=
    @gA1i
      (.classEq (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn (.cv v)))))
          (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (.cv v))))))
        (synCop (synCsi (synCfv (synC1st) (.cv v)))
          (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classMem (.cv v) (synChwcn A)) p0032
  have p0034 :=
    @gEqtrd (.classMem (.cv v) (synChwcn A))
      (synCfv (synChnsicodemap A) (synCsn (.cv v)))
      (synCop (synCsi (synCfv (synC1st) (synCuni (synCsn (.cv v)))))
        (synCpw1 (synCfv (synC2nd) (synCuni (synCsn (.cv v))))))
      (synCop (synCsi (synCfv (synC1st) (.cv v))) (synCpw1 (synCfv (synC2nd) (.cv v))))
      p0020 p0033
  have p0035 := @gFvex (.cv v) (synC1st)
  have p0036 := @gSiex (synCfv (synC1st) (.cv v)) p0035
  have p0037 := @gFvex (.cv v) (synC2nd)
  have p0038 := @gPw1ex (synCfv (synC2nd) (.cv v)) p0037
  have p0039 :=
    @gOp1std (synCsi (synCfv (synC1st) (.cv v)))
      (synCpw1 (synCfv (synC2nd) (.cv v)))
      (synCfv (synChnsicodemap A) (synCsn (.cv v))) p0036 p0038
  have p0040 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synChnsicodemap A) (synCsn (.cv v)))
        (synCop (synCsi (synCfv (synC1st) (.cv v)))
          (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classEq (synCfv (synC1st) (synCfv (synChnsicodemap A) (synCsn (.cv v))))
        (synCsi (synCfv (synC1st) (.cv v))))
      p0034 p0039
  have p0041 :=
    @gEqtrd (.classMem (.cv v) (synChwcn A))
      (synCfv (synC1st) (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC1st) (synCfv (synChnsicodemap A) (synCsn (.cv v))))
      (synCsi (synCfv (synC1st) (.cv v))) p0015 p0040
  have p0042 :=
    @gId
      (.classEq (synCfv (synC1st)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCsi (synCfv (synC1st) (.cv v))))
  have p0043 :=
    @gSieqdndv
      (.classEq (synCfv (synC1st)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCsi (synCfv (synC1st) (.cv v))))
      (synCfv (synC1st) (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCsi (synCfv (synC1st) (.cv v))) p0042
  have p0044 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synC1st)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCsi (synCfv (synC1st) (.cv v))))
      (.classEq (synCsi (synCfv (synC1st)
            (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
        (synCsi (synCsi (synCfv (synC1st) (.cv v)))))
      p0041 p0043
  have p0047 :=
    @gFveq2i (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (synCfv (synChnsicodemap A) (synCsn (.cv v))) (synC2nd) p0013
  have p0048 :=
    @gA1i
      (.classEq (synCfv (synC2nd)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCfv (synC2nd) (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (.classMem (.cv v) (synChwcn A)) p0047
  have p0072 :=
    @gOp2ndd (synCsi (synCfv (synC1st) (.cv v)))
      (synCpw1 (synCfv (synC2nd) (.cv v)))
      (synCfv (synChnsicodemap A) (synCsn (.cv v))) p0036 p0038
  have p0073 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synChnsicodemap A) (synCsn (.cv v)))
        (synCop (synCsi (synCfv (synC1st) (.cv v)))
          (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classEq (synCfv (synC2nd) (synCfv (synChnsicodemap A) (synCsn (.cv v))))
        (synCpw1 (synCfv (synC2nd) (.cv v))))
      p0034 p0072
  have p0074 :=
    @gEqtrd (.classMem (.cv v) (synChwcn A))
      (synCfv (synC2nd) (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCfv (synC2nd) (synCfv (synChnsicodemap A) (synCsn (.cv v))))
      (synCpw1 (synCfv (synC2nd) (.cv v))) p0048 p0073
  have p0075 :=
    @gPw1eq
      (synCfv (synC2nd) (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synCpw1 (synCfv (synC2nd) (.cv v)))
  have p0076 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synC2nd)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
        (synCpw1 (synCfv (synC2nd) (.cv v))))
      (.classEq (synCpw1 (synCfv (synC2nd)
            (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0074 p0075
  have p0077 :=
    @gOpeq12d (.classMem (.cv v) (synChwcn A))
      (synCsi (synCfv (synC1st)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synCsi (synCsi (synCfv (synC1st) (.cv v))))
      (synCpw1 (synCfv (synC2nd)
          (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))) p0044 p0076
  have p0078 :=
    @gEqtrd (.classMem (.cv v) (synChwcn A))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (synCop (synCsi (synCfv (synC1st)
            (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))) (synCpw1
          (synCfv (synC2nd)
            (synCuni (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0011 p0077
  have p0079 := @gHnsicodemapfndv (synCpw1 A)
  have p0080 :=
    @gA1i
      (synWf (synChnsicodemap (synCpw1 A)) (synCpw1 (synChwcn (synCpw1 A)))
        (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (.cv v) (synChwcn A)) p0079
  have p0091 :=
    @gJca (.classMem (.cv v) (synChwcn A))
      (synWf (synChnsicodemap (synCpw1 A)) (synCpw1 (synChwcn (synCpw1 A)))
        (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
        (synCpw1 (synChwcn (synCpw1 A))))
      p0080 p0009
  have p0092 :=
    @gFfvelrn (synCpw1 (synChwcn (synCpw1 A))) (synChwcn (synCpw1 (synCpw1 A)))
      (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
      (synChnsicodemap (synCpw1 A))
  have p0093 :=
    @gSyl (.classMem (.cv v) (synChwcn A))
      (synWa (synWf (synChnsicodemap (synCpw1 A)) (synCpw1 (synChwcn (synCpw1 A)))
          (synChwcn (synCpw1 (synCpw1 A))))
        (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
          (synCpw1 (synChwcn (synCpw1 A)))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0091 p0092
  have p0094 :=
    @gJca (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synCop (synCsi (synCsi (synCfv (synC1st) (.cv v))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
        (synChwcn (synCpw1 (synCpw1 A))))
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

/-- Checked nominal proof certificate identified upstream as `g_hncodepw12repdndv`. -/
@[expose]
noncomputable def gHncodepw12repdndv (v : Var) (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v)
    (hyp_hncodepw12repdndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (synWrex v (synChwcn A)
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))) :=
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
  have dv_cache_0001 : t ∉ ((synCpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_t_not_A,
          not_false_eq_true])
  have dv_cache_0002 : t ∉ ((synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))).fv :=
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
  have dv_cache_0004 : q ∉ ((synCuni (.cv t))).fv :=
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
      ((synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))).fv :=
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
  have dv_cache_0007 : z ∉ ((synCuni (.cv q))).fv :=
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
      ((synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))).fv :=
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
  have dv_cache_0011 : v ∉ ((synChwcn A)).fv :=
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
      ((synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))).fv :=
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
    z ∉ ((Wff.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))).fv :=
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
      ((synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))).fv :=
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
    q ∉ ((Wff.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))).fv :=
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
      ((synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))).fv :=
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
      ((synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))).fv :=
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
    t ∉ ((Wff.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))).fv :=
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
  have p0000 := @gPw1ex A hyp_hncodepw12repdndv_1
  have p0001 := @gPw1ex (synCpw1 A) p0000
  have p0002 := @gHwnisoclasselhnordcl (synCpw1 (synCpw1 A)) (.cv u) p0001
  have p0003 := @gId (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
  have p0004 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (.classMem (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synChnord (synCpw1 (synCpw1 A)))))
      (.imp (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
        (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))))
      p0002 p0003
  have p0006 :=
    @gHnsiquomappreexclndv t (synCpw1 A)
      (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) dv_cache_0001 dv_cache_0002
      p0000
  have p0007 :=
    @gSyl (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synChnord (synCpw1 (synCpw1 A))))
      (synWrex t (synCpw1 (synChnord (synCpw1 A)))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      p0004 p0006
  have p0008 :=
    @gSimpl (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))
  have p0009 := @gPw1argclcl (synChnord (synCpw1 A)) (.cv t)
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
      (synWa (.classMem (synCuni (.cv t)) (synChnord (synCpw1 A)))
        (.classEq (.cv t) (synCsn (synCuni (.cv t)))))
      p0008 p0009
  have p0011 :=
    @gSimpl (.classMem (synCuni (.cv t)) (synChnord (synCpw1 A)))
      (.classEq (.cv t) (synCsn (synCuni (.cv t))))
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (synWa (.classMem (synCuni (.cv t)) (synChnord (synCpw1 A)))
        (.classEq (.cv t) (synCsn (synCuni (.cv t)))))
      (.classMem (synCuni (.cv t)) (synChnord (synCpw1 A))) p0010 p0011
  have p0013 :=
    @gHnsiquomappreexclndv q A (synCuni (.cv t)) dv_cache_0003 dv_cache_0004
      hyp_hncodepw12repdndv_1
  have p0014 :=
    @gSyl
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classMem (synCuni (.cv t)) (synChnord (synCpw1 A)))
      (synWrex q (synCpw1 (synChnord A))
        (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
      p0012 p0013
  have p0015 :=
    @gNfv
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      q dv_cache_0005
  have p0016 :=
    @gNfri
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      q p0015
  have p0017 :=
    @gSimpr
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
  have p0018 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
  have p0019 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synChnord A))) p0017 p0018
  have p0020 := @gPw1argclcl (synChnord A) (.cv q)
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0019 p0020
  have p0022 :=
    @gSimpl (.classMem (synCuni (.cv q)) (synChnord A))
      (.classEq (.cv q) (synCsn (synCuni (.cv q))))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (synCuni (.cv q)) (synChnord A))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      (.classMem (synCuni (.cv q)) (synChnord A)) p0021 p0022
  have p0024 := @gVex q
  have p0025 := @gUniex (.cv q) p0024
  have p0026 := @gElhnordclndv z A (synCuni (.cv q)) dv_cache_0006 dv_cache_0007
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @gBiimpi (.classMem (synCuni (.cv q)) (synChnord A))
      (synWrex z (synChwcn A) (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
      p0027
  have p0029 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (synCuni (.cv q)) (synChnord A))
      (synWrex z (synChwcn A) (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
      p0023 p0028
  have p0030 :=
    @gNfv
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      z dv_cache_0008
  have p0031 :=
    @gNfri
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      z p0030
  have p0032 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (.cv z) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
  have p0033 :=
    @gSimpl (.classMem (.cv z) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv z) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
      (.classMem (.cv z) (synChwcn A)) p0032 p0033
  have p0035 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (.cv z) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
  have p0036 :=
    @gSimpl
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
  have p0037 :=
    @gSimpr (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))
  have p0038 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))
      p0036 p0037
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))
      p0035 p0038
  have p0043 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A)))) p0036 p0008
  have p0044 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A)))) p0035 p0043
  have p0045 := @gHnsicodemapfndv A
  have p0046 :=
    @gA1i (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      p0045
  have p0050 := @gSnelpw1 (.cv z) (synChwcn A)
  have p0051 :=
    @gSylibr
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (.cv z) (synChwcn A))
      (.classMem (synCsn (.cv z)) (synCpw1 (synChwcn A))) p0034 p0050
  have p0052 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (.cv z)) (synCpw1 (synChwcn A))) p0046 p0051
  have p0053 :=
    @gFfvelrn (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)) (synCsn (.cv z))
      (synChnsicodemap A)
  have p0054 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (synWf (synChnsicodemap A) (synCpw1 (synChwcn A)) (synChwcn (synCpw1 A)))
        (.classMem (synCsn (.cv z)) (synCpw1 (synChwcn A))))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwcn (synCpw1 A)))
      p0052 p0053
  have p0057 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
  have p0058 :=
    @gSyl
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
      (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))) p0017 p0057
  have p0059 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))) p0035 p0058
  have p0064 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (.cv q) (synCpw1 (synChnord A))) p0035 p0019
  have p0069 :=
    @gSimpr (.classMem (.cv z) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
  have p0070 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv z) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
      (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))) p0032 p0069
  have p0071 := @gEqid (synCec (.cv z) (synChwniso A))
  have p0072 :=
    @gA1i (.classEq (synCec (.cv z) (synChwniso A)) (synCec (.cv z) (synChwniso A)))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      p0071
  have p0073 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))
      (synCec (.cv z) (synChwniso A)) p0070 p0072
  have p0074 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (.cv z) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))) p0034 p0073
  have p0075 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (synWa (.classMem (.cv z) (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
      p0064 p0074
  have p0076 :=
    @gHnsiquomaprepvalndv z A q dv_cache_0003 dv_cache_0006 dv_cache_0009
      hyp_hncodepw12repdndv_1
  have p0077 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCec (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwniso (synCpw1 A))))
      p0075 p0076
  have p0078 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))
      (synCec (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwniso (synCpw1 A)))
      p0059 p0077
  have p0079 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwcn (synCpw1 A)))
      (.classEq (synCuni (.cv t)) (synCec (synCfv (synChnsicodemap A) (synCsn (.cv z)))
          (synChwniso (synCpw1 A))))
      p0054 p0078
  have p0080 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
      (synWa (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv z)))
          (synChwcn (synCpw1 A))) (.classEq (synCuni (.cv t))
          (synCec (synCfv (synChnsicodemap A) (synCsn (.cv z)))
            (synChwniso (synCpw1 A)))))
      p0044 p0079
  have p0082 :=
    @gHnsiquomaprepvalcl2ndv (synCpw1 A)
      (synCfv (synChnsicodemap A) (synCsn (.cv z))) t dv_cache_0001 p0000
  have p0083 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A)))) (synWa
          (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwcn (synCpw1 A)))
          (.classEq (synCuni (.cv t)) (synCec (synCfv (synChnsicodemap A) (synCsn (.cv z)))
              (synChwniso (synCpw1 A))))))
      (.classEq (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)) (synCec
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      p0080 p0082
  have p0084 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
      (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))
      (synCec (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
        (synChwniso (synCpw1 (synCpw1 A))))
      p0039 p0083
  have p0085 :=
    @gA1d (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      p0003
  have p0086 := @gHnsicodemapfndv (synCpw1 A)
  have p0087 :=
    @gA1i
      (synWf (synChnsicodemap (synCpw1 A)) (synCpw1 (synChwcn (synCpw1 A)))
        (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      p0086
  have p0098 :=
    @gSnelpw1 (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwcn (synCpw1 A))
  have p0099 :=
    @gSylibr
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (synCfv (synChnsicodemap A) (synCsn (.cv z))) (synChwcn (synCpw1 A)))
      (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))
        (synCpw1 (synChwcn (synCpw1 A))))
      p0054 p0098
  have p0100 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWf (synChnsicodemap (synCpw1 A)) (synCpw1 (synChwcn (synCpw1 A)))
        (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))
        (synCpw1 (synChwcn (synCpw1 A))))
      p0087 p0099
  have p0101 :=
    @gFfvelrn (synCpw1 (synChwcn (synCpw1 A))) (synChwcn (synCpw1 (synCpw1 A)))
      (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))
      (synChnsicodemap (synCpw1 A))
  have p0102 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (synWf (synChnsicodemap (synCpw1 A)) (synCpw1 (synChwcn (synCpw1 A)))
          (synChwcn (synCpw1 (synCpw1 A))))
        (.classMem (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))
          (synCpw1 (synChwcn (synCpw1 A)))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
        (synChwcn (synCpw1 (synCpw1 A))))
      p0100 p0101
  have p0103 :=
    @g_pm3_2 (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
        (synChwcn (synCpw1 (synCpw1 A))))
  have p0104 :=
    @gSyl5
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
        (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      p0102 p0103
  have p0105 :=
    @gSyl6 (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.imp (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
              (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
                (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
            (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
          (synWa (.classMem (.cv z) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
        (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
            (synChwcn (synCpw1 (synCpw1 A))))))
      p0085 p0104
  have p0106 :=
    @gPm243d (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      p0105
  have p0109 :=
    @gHwnisoclasseqbcl (synCpw1 (synCpw1 A)) (.cv u)
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
      p0001
  have p0110 :=
    @gSyl6 (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A)))) (.classMem
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
          (synChwcn (synCpw1 (synCpw1 A)))))
      (synWb (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))))
      p0106 p0109
  have p0111 :=
    @gBi1
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))
  have p0112 :=
    @gSyl6 (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWb (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))))
      (.imp (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
            (synChwniso (synCpw1 (synCpw1 A)))))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))))
      p0110 p0111
  have p0113 :=
    @gMpdi (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A)))) (synCec
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
          (synChwniso (synCpw1 (synCpw1 A)))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))
      p0084 p0112
  have p0114 :=
    @g_pm3_2 (.classMem (.cv z) (synChwcn A))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))
  have p0115 :=
    @gSyl9 (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))
      (.classMem (.cv z) (synChwcn A))
      (synWa (.classMem (.cv z) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))))
      p0113 p0114
  have p0116 :=
    @gSyl5
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (.classMem (.cv z) (synChwcn A))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.imp (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
              (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
                (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
            (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
              (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
          (synWa (.classMem (.cv z) (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))))
      p0034 p0115
  have p0117 :=
    @gPm243d (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv z) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))))
      p0116
  have p0118 := @gId (.classEq (.cv v) (.cv z))
  have p0119 := @gSneqd (.classEq (.cv v) (.cv z)) (.cv v) (.cv z) p0118
  have p0120 :=
    @gFveq2d (.classEq (.cv v) (.cv z)) (synCsn (.cv v)) (synCsn (.cv z))
      (synChnsicodemap A) p0119
  have p0121 :=
    @gSneqd (.classEq (.cv v) (.cv z)) (synCfv (synChnsicodemap A) (synCsn (.cv v)))
      (synCfv (synChnsicodemap A) (synCsn (.cv z))) p0120
  have p0122 :=
    @gFveq2d (.classEq (.cv v) (.cv z))
      (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))
      (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))
      (synChnsicodemap (synCpw1 A)) p0121
  have p0123 :=
    @gBreq2d (.classEq (.cv v) (.cv z))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))
      (synCfv (synChnsicodemap (synCpw1 A))
        (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))
      (.cv u) (synChwniso (synCpw1 (synCpw1 A))) p0122
  have p0124 :=
    @gRspcev
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))
      (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
        (synCfv (synChnsicodemap (synCpw1 A))
          (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z))))))
      v (.cv z) (synChwcn A) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0123
  have p0125 :=
    @gSyl6 (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
        (synWa (.classMem (.cv z) (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))))
      (synWa (.classMem (.cv z) (synChwcn A))
        (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv z)))))))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0117 p0124
  have p0126 :=
    @gExp4d (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (.cv z) (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0125
  have p0127 :=
    @gImp3a (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (.cv z) (synChwcn A))
      (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
        (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0126
  have p0128 :=
    @gExp3a (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.classMem (.cv z) (synChwcn A))
      (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
        (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0127
  have p0129 :=
    @gAlimdv (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.imp (.classMem (.cv z) (synChwcn A))
        (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      z dv_cache_0013 p0128
  have p0130 :=
    @gSyl5
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.all z (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
            (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
              (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
          (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
            (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.all z (.imp (.classMem (.cv z) (synChwcn A))
          (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
            (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
      p0031 p0129
  have p0131 :=
    (Nominal.biimpRefl (synWral z (synChwcn A)
        (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
  have p0132 :=
    @gSyl6ibr (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (.all z (.imp (.classMem (.cv z) (synChwcn A))
          (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
            (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
      (synWral z (synChwcn A)
        (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      p0130 p0131
  have p0133 :=
    @gNfv
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      z dv_cache_0014
  have p0134 :=
    @gR1923 (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      z (synChwcn A) p0133
  have p0135 :=
    @gSyl6ib (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWral z (synChwcn A)
        (.imp (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.imp (synWrex z (synChwcn A)
          (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
        (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0132 p0134
  have p0136 :=
    @gMpdi (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
        (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))))
      (synWrex z (synChwcn A) (.classEq (synCuni (.cv q)) (synCec (.cv z) (synChwniso A))))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0029 p0135
  have p0137 :=
    @gExp4d (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0136
  have p0138 :=
    @gImp3a (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
        (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0137
  have p0139 :=
    @gExp3a (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
        (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0138
  have p0140 :=
    @gAlimdv (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.imp (.classMem (.cv q) (synCpw1 (synChnord A)))
        (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      q dv_cache_0015 p0139
  have p0141 :=
    @gSyl5
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.all q (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
          (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
            (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))))
      (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.all q (.imp (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
            (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
      p0016 p0140
  have p0142 :=
    (Nominal.biimpRefl (synWral q (synCpw1 (synChnord A))
        (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
  have p0143 :=
    @gSyl6ibr (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (.all q (.imp (.classMem (.cv q) (synCpw1 (synChnord A)))
          (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
            (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
                (synCfv (synChnsicodemap (synCpw1 A))
                  (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))))
      (synWral q (synCpw1 (synChnord A))
        (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      p0141 p0142
  have p0144 :=
    @gNfv
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      q dv_cache_0016
  have p0145 :=
    @gR1923 (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      q (synCpw1 (synChnord A)) p0144
  have p0146 :=
    @gSyl6ib (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (synWral q (synCpw1 (synChnord A))
        (.imp (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q)))
          (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synCfv (synChnsicodemap (synCpw1 A))
                (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))))
      (.imp (synWrex q (synCpw1 (synChnord A))
          (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
        (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synCfv (synChnsicodemap (synCpw1 A))
              (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v))))))))
      p0143 p0145
  have p0147 :=
    @gMpdi (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWa (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (synWrex q (synCpw1 (synChnord A))
        (.classEq (synCuni (.cv t)) (synCfv (synChnsiquomap A) (.cv q))))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0014 p0146
  have p0148 :=
    @gExp3a (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classMem (.cv t) (synCpw1 (synChnord (synCpw1 A))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      p0147
  have p0149 :=
    @gRexlimdv (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
        (synCfv (synChnsiquomap (synCpw1 A)) (.cv t)))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
      t (synCpw1 (synChnord (synCpw1 A))) dv_cache_0017 dv_cache_0018 p0148
  have p0150 :=
    @gMpd (.classMem (.cv u) (synChwcn (synCpw1 (synCpw1 A))))
      (synWrex t (synCpw1 (synChnord (synCpw1 A)))
        (.classEq (synCec (.cv u) (synChwniso (synCpw1 (synCpw1 A))))
          (synCfv (synChnsiquomap (synCpw1 A)) (.cv t))))
      (synWrex v (synChwcn A) (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
          (synCfv (synChnsicodemap (synCpw1 A))
            (synCsn (synCfv (synChnsicodemap A) (synCsn (.cv v)))))))
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

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpquotbrproxyimpndv`. -/
@[expose]
noncomputable def gHncodecmpquotbrproxyimpndv (v : Var) (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv)
    (hyp_hncodecmpquotbrproxyimpndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))) (synWb
          (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec (.cv v) (synChwniso A)))
          (synWbr (.cv u) (synChncodecmpset A) (.cv v)))) :=
  by
  have dv_cache_0001 : Disjoint ((synChwcn A)).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint ((synChwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact dv_A_r))))))
  have p0000 :=
    @gA1i (.classMem A (synCvv))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      hyp_hncodecmpquotbrproxyimpndv_1
  have p0001 := @gHncodecmpsetexg A
  have p0002 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0000 p0001
  have p0003 :=
    @gSimpl (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0004 :=
    @gEleq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synCvv) p0003
  have p0005 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv r) (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0002
      p0004
  have p0007 := @gHncodecmpsetrefndv A
  have p0008 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      p0000 p0007
  have p0010 :=
    @gBreq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCref) p0003
  have p0011 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCref) (synChwcn A)) p0008 p0010
  have p0013 := @gHncodecmpsettransndv A
  have p0014 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A))
      p0000 p0013
  have p0016 :=
    @gBreq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCtrans) p0003
  have p0017 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv r) (synCtrans) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)) p0014 p0016
  have p0018 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (.cv r) (synCtrans) (synChwcn A)) p0011 p0017
  have p0019 := @gHncodecmpsetssxpndv A
  have p0020 :=
    @gA1i (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      p0019
  have p0022 :=
    @gSseq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)) p0003
  have p0023 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))
      (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) p0020 p0022
  have p0024 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (synWbr (.cv r) (synCref) (synChwcn A))
        (synWbr (.cv r) (synCtrans) (synChwcn A)))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))) p0018 p0023
  have p0025 :=
    @gSimpr (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0026 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0027 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0025 p0026
  have p0029 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0030 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A)) p0025 p0029
  have p0031 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0027 p0030
  have p0032 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
          (synWbr (.cv r) (synCtrans) (synChwcn A)))
        (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0024
      p0031
  have p0033 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv r) (synCvv))
      (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
            (synWbr (.cv r) (synCtrans) (synChwcn A)))
          (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      p0005 p0032
  have p0034 := @gBrlnqordkern (synChwcn A) (.cv r) (.cv u) (.cv v) dv_cache_0001
  have p0035 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv r) (synCvv)) (synWa (synWa
            (synWa (synWbr (.cv r) (synCref) (synChwcn A))
              (synWbr (.cv r) (synCtrans) (synChwcn A)))
            (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))))
      (synWb (synWbr (synCec (.cv u) (synClnker (.cv r)))
          (synClnqord (.cv r) (synChwcn A)) (synCec (.cv v) (synClnker (.cv r))))
        (synWbr (.cv u) (.cv r) (.cv v)))
      p0033 p0034
  have p0037 := @gLnkereq (.cv r) (synChncodecmpset A)
  have p0038 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (synClnker (.cv r)) (synClnker (synChncodecmpset A))) p0003 p0037
  have p0040 := @gHncodecmplnkerndv A
  have p0041 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem A (synCvv))
      (.classEq (synClnker (synChncodecmpset A)) (synChwniso A)) p0000 p0040
  have p0042 :=
    @gEqtrd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synClnker (.cv r)) (synClnker (synChncodecmpset A)) (synChwniso A) p0038 p0041
  have p0043 := @gEceq2 (synClnker (.cv r)) (synChwniso A) (.cv u)
  have p0044 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classEq (synClnker (.cv r)) (synChwniso A))
      (.classEq (synCec (.cv u) (synClnker (.cv r))) (synCec (.cv u) (synChwniso A)))
      p0042 p0043
  have p0052 := @gEceq2 (synClnker (.cv r)) (synChwniso A) (.cv v)
  have p0053 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classEq (synClnker (.cv r)) (synChwniso A))
      (.classEq (synCec (.cv v) (synClnker (.cv r))) (synCec (.cv v) (synChwniso A)))
      p0042 p0052
  have p0054 :=
    @gBreq12d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synCec (.cv u) (synClnker (.cv r))) (synCec (.cv u) (synChwniso A))
      (synCec (.cv v) (synClnker (.cv r))) (synCec (.cv v) (synChwniso A))
      (synClnqord (.cv r) (synChwcn A)) p0044 p0053
  have p0055 :=
    @gBicomd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (synCec (.cv u) (synClnker (.cv r))) (synClnqord (.cv r) (synChwcn A))
        (synCec (.cv v) (synClnker (.cv r))))
      (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (.cv v) (synChwniso A)))
      p0054
  have p0057 :=
    @gBreqd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.cv r) (synChncodecmpset A) (.cv u) (.cv v) p0003
  have p0058 :=
    @gBicomd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (.cv r) (.cv v)) (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      p0057
  have p0059 :=
    @gN3bitr4d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (synCec (.cv u) (synClnker (.cv r))) (synClnqord (.cv r) (synChwcn A))
        (synCec (.cv v) (synClnker (.cv r))))
      (synWbr (.cv u) (.cv r) (.cv v))
      (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (.cv v) (synChwniso A)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v)) p0035 p0055 p0058
  exact p0059

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpquotbrproxyimpclndv`. -/
@[expose]
noncomputable def gHncodecmpquotbrproxyimpclndv (A : Class) (B : Class) (C : Class)
    (r : Var) (dv_A_r : r ∉ A.fv)
    (hyp_hncodecmpquotbrproxyimpclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C))) :=
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
      ((Wff.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
            (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
              (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C)))).fv :=
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
      ((Wff.imp (.classMem C (synChwcn A)) (.imp
            (synWa (.classEq (.cv r) (synChncodecmpset A))
              (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
              (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
                (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C))))).fv :=
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
    @gId
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
  have p0001 :=
    @gSimpr (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
  have p0002 := @gSimpr (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0003 := @gSimpl (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0004 := @gElex B (synChwcn A)
  have p0005 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synChwcn A)) (.classMem B (synCvv)) p0003 p0004
  have p0006 := @gBiid (.classMem C (synChwcn A))
  have p0007 :=
    @gA1i (synWb (.classMem C (synChwcn A)) (.classMem C (synChwcn A)))
      (.classEq (.cv u) B) p0006
  have p0008 := @gBiid (.classEq (.cv r) (synChncodecmpset A))
  have p0009 :=
    @gA1i
      (synWb (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (.cv u) B) p0008
  have p0010 := @gId (.classEq (.cv u) B)
  have p0011 := @gEleq1d (.classEq (.cv u) B) (.cv u) B (synChwcn A) p0010
  have p0014 :=
    @gAnbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem C (synChwcn A)) (.classMem C (synChwcn A))
      p0011 p0007
  have p0015 :=
    @gAnbi12d (.classEq (.cv u) B) (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))) p0009 p0014
  have p0016 := @gEceq1 (.cv u) B (synChwniso A)
  have p0017 :=
    @gBreq1d (.classEq (.cv u) B) (synCec (.cv u) (synChwniso A))
      (synCec B (synChwniso A)) (synCec C (synChwniso A))
      (synClnqord (.cv r) (synChwcn A)) p0016
  have p0019 := @gBreq1d (.classEq (.cv u) B) (.cv u) B C (synChncodecmpset A) p0010
  have p0020 :=
    @gBibi12d (.classEq (.cv u) B)
      (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec C (synChwniso A)))
      (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec C (synChwniso A)))
      (synWbr (.cv u) (synChncodecmpset A) C) (synWbr B (synChncodecmpset A) C) p0017
      p0019
  have p0021 :=
    @gImbi12d (.classEq (.cv u) B)
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWb (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
          (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C))
      (synWb (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
          (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C))
      p0015 p0020
  have p0022 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem C (synChwcn A))
      (.classMem C (synChwcn A))
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C)))
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C)))
      p0007 p0021
  have p0023 := @gElex C (synChwcn A)
  have p0025 :=
    @gA1i
      (synWb (.classEq (.cv r) (synChncodecmpset A)) (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (.cv v) C) p0008
  have p0026 := @gBiid (.classMem (.cv u) (synChwcn A))
  have p0027 :=
    @gA1i (synWb (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv v) C) p0026
  have p0028 := @gId (.classEq (.cv v) C)
  have p0029 := @gEleq1d (.classEq (.cv v) C) (.cv v) C (synChwcn A) p0028
  have p0030 :=
    @gAnbi12d (.classEq (.cv v) C) (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem C (synChwcn A)) p0027 p0029
  have p0031 :=
    @gAnbi12d (.classEq (.cv v) C) (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A))) p0025 p0030
  have p0032 := @gEceq1 (.cv v) C (synChwniso A)
  have p0033 :=
    @gBreq2d (.classEq (.cv v) C) (synCec (.cv v) (synChwniso A))
      (synCec C (synChwniso A)) (synCec (.cv u) (synChwniso A))
      (synClnqord (.cv r) (synChwcn A)) p0032
  have p0035 :=
    @gBreq2d (.classEq (.cv v) C) (.cv v) C (.cv u) (synChncodecmpset A) p0028
  have p0036 :=
    @gBibi12d (.classEq (.cv v) C)
      (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (.cv v) (synChwniso A)))
      (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec C (synChwniso A)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv u) (synChncodecmpset A) C) p0033 p0035
  have p0037 :=
    @gImbi12d (.classEq (.cv v) C)
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A))))
      (synWb (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
          (synCec (.cv v) (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) (.cv v)))
      (synWb (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
          (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C))
      p0031 p0036
  have p0038 :=
    @gHncodecmpquotbrproxyimpndv v u A r dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hncodecmpquotbrproxyimpclndv_1
  have p0039 :=
    @gVtoclg
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))) (synWb
          (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec (.cv v) (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) (.cv v))))
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C)))
      v C (synCvv) dv_cache_0004 dv_cache_0005 p0037 p0038
  have p0040 :=
    @gSyl (.classMem C (synChwcn A)) (.classMem C (synCvv))
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C)))
      p0023 p0039
  have p0041 :=
    @gVtoclg
      (.imp (.classMem C (synChwcn A)) (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
            (synWbr (synCec (.cv u) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
              (synCec C (synChwniso A))) (synWbr (.cv u) (synChncodecmpset A) C))))
      (.imp (.classMem C (synChwcn A)) (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
            (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
            (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
              (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C))))
      u B (synCvv) dv_cache_0006 dv_cache_0007 p0022 p0040
  have p0042 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synCvv))
      (.imp (.classMem C (synChwcn A)) (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
            (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
            (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
              (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C))))
      p0005 p0041
  have p0043 :=
    @gMpd (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A))
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C)))
      p0002 p0042
  have p0044 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
            (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C)))
      p0001 p0043
  have p0045 :=
    @gMpd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWb (synWbr (synCec B (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
          (synCec C (synChwniso A))) (synWbr B (synChncodecmpset A) C))
      p0000 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as
`g_hncodecmpquotstrictbrproxyimpclndv`.
-/
@[expose]
noncomputable def gHncodecmpquotstrictbrproxyimpclndv (A : Class) (B : Class) (C : Class)
    (r : Var) (dv_A_r : r ∉ A.fv)
    (hyp_hncodecmpquotstrictbrproxyimpclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A))
          (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))) (synWb
          (synWbr (synCec B (synChwniso A))
            (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
            (synCec C (synChwniso A)))
          (synWbr B (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) C))) :=
  by
  have dv_cache_0001 : Disjoint ((synChwcn A)).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint ((synChwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact dv_A_r))))))
  have p0000 :=
    @gA1i (.classMem A (synCvv))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0001 := @gHncodecmpsetexg A
  have p0002 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0000 p0001
  have p0003 :=
    @gSimpl (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
  have p0004 :=
    @gEleq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synCvv) p0003
  have p0005 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem (.cv r) (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0002
      p0004
  have p0007 := @gHwcnexg A
  have p0008 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv)) p0000 p0007
  have p0009 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)) p0005 p0008
  have p0011 := @gHncodecmpsetrefndv A
  have p0012 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))
      p0000 p0011
  have p0014 :=
    @gBreq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCref) p0003
  have p0015 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCref) (synChwcn A)) p0012 p0014
  have p0017 := @gHncodecmpsettransndv A
  have p0018 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A))
      p0000 p0017
  have p0020 :=
    @gBreq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCtrans) p0003
  have p0021 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr (.cv r) (synCtrans) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCtrans) (synChwcn A)) p0018 p0020
  have p0022 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr (.cv r) (synCref) (synChwcn A))
      (synWbr (.cv r) (synCtrans) (synChwcn A)) p0015 p0021
  have p0024 := @gHncodecmpsetconnexndv A
  have p0025 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A))
      p0000 p0024
  have p0027 :=
    @gBreq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synChwcn A) (synCconnex) p0003
  have p0028 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr (.cv r) (synCconnex) (synChwcn A))
      (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A)) p0025 p0027
  have p0029 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (synWbr (.cv r) (synCref) (synChwcn A))
        (synWbr (.cv r) (synCtrans) (synChwcn A)))
      (synWbr (.cv r) (synCconnex) (synChwcn A)) p0022 p0028
  have p0030 := @gHncodecmpsetssxpndv A
  have p0031 :=
    @gA1i (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      p0030
  have p0033 :=
    @gSseq1d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A)) p0003
  have p0034 :=
    @gMpbird
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))
      (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) p0031 p0033
  have p0035 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
          (synWbr (.cv r) (synCtrans) (synChwcn A)))
        (synWbr (.cv r) (synCconnex) (synChwcn A)))
      (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))) p0029 p0034
  have p0036 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
            (synWbr (.cv r) (synCtrans) (synChwcn A)))
          (synWbr (.cv r) (synCconnex) (synChwcn A)))
        (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A))))
      p0009 p0035
  have p0037 :=
    @gSimpr (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
  have p0038 := @gSimpl (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0039 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synChwcn A)) p0037 p0038
  have p0041 := @gSimpr (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0042 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A)) p0037 p0041
  have p0043 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem B (synChwcn A)) (.classMem C (synChwcn A)) p0039 p0042
  have p0044 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv))) (synWa
          (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
              (synWbr (.cv r) (synCtrans) (synChwcn A)))
            (synWbr (.cv r) (synCconnex) (synChwcn A)))
          (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))) p0036 p0043
  have p0045 := @gBrlnqordstrict (synChwcn A) (.cv r) B C dv_cache_0001
  have p0046 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWa (synWa (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
          (synWa (synWa (synWa (synWbr (.cv r) (synCref) (synChwcn A))
                (synWbr (.cv r) (synCtrans) (synChwcn A)))
              (synWbr (.cv r) (synCconnex) (synChwcn A)))
            (synWss (.cv r) (synCxp (synChwcn A) (synChwcn A)))))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWb (synWbr (synCec B (synClnker (.cv r)))
          (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
          (synCec C (synClnker (.cv r)))) (synWbr B (synCdif (.cv r) (synCcnv (.cv r))) C))
      p0044 p0045
  have p0048 := @gLnkereq (.cv r) (synChncodecmpset A)
  have p0049 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (synClnker (.cv r)) (synClnker (synChncodecmpset A))) p0003 p0048
  have p0051 := @gHncodecmplnkerndv A
  have p0052 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classMem A (synCvv))
      (.classEq (synClnker (synChncodecmpset A)) (synChwniso A)) p0000 p0051
  have p0053 :=
    @gEqtrd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synClnker (.cv r)) (synClnker (synChncodecmpset A)) (synChwniso A) p0049 p0052
  have p0054 := @gEceq2 (synClnker (.cv r)) (synChwniso A) B
  have p0055 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classEq (synClnker (.cv r)) (synChwniso A))
      (.classEq (synCec B (synClnker (.cv r))) (synCec B (synChwniso A))) p0053 p0054
  have p0063 := @gEceq2 (synClnker (.cv r)) (synChwniso A) C
  have p0064 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.classEq (synClnker (.cv r)) (synChwniso A))
      (.classEq (synCec C (synClnker (.cv r))) (synCec C (synChwniso A))) p0053 p0063
  have p0065 :=
    @gBreq12d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synCec B (synClnker (.cv r))) (synCec B (synChwniso A))
      (synCec C (synClnker (.cv r))) (synCec C (synChwniso A))
      (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) p0055 p0064
  have p0066 :=
    @gBicomd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr (synCec B (synClnker (.cv r)))
        (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec C (synClnker (.cv r))))
      (synWbr (synCec B (synChwniso A))
        (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) (synCec C (synChwniso A)))
      p0065
  have p0069 :=
    @gCnveqd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) p0003
  have p0070 :=
    @gDifeq12d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (.cv r) (synChncodecmpset A) (synCcnv (.cv r)) (synCcnv (synChncodecmpset A))
      p0003 p0069
  have p0071 :=
    @gBreqd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synCdif (.cv r) (synCcnv (.cv r)))
      (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) B C p0070
  have p0072 :=
    @gBicomd
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr B (synCdif (.cv r) (synCcnv (.cv r))) C)
      (synWbr B (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) C)
      p0071
  have p0073 :=
    @gN3bitr4d
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A))))
      (synWbr (synCec B (synClnker (.cv r)))
        (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec C (synClnker (.cv r))))
      (synWbr B (synCdif (.cv r) (synCcnv (.cv r))) C)
      (synWbr (synCec B (synChwniso A))
        (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) (synCec C (synChwniso A)))
      (synWbr B (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) C)
      p0046 p0066 p0072
  exact p0073

/-- Checked nominal proof certificate identified upstream as `g_hnwcutrelambfnnoarndv`. -/
@[expose]
noncomputable def gHnwcutrelambfnnoarndv (A : Class) (D : Class) (R : Class)
    (hyp_hnwcutrelambfnnoarndv_1 : Nominal.NPrf (synWss D A))
    (hyp_hnwcutrelambfnnoarndv_2 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn A)) :=
  by
  have p0000 := @gHnwcutrelfndv D R hyp_hnwcutrelambfnnoarndv_2
  have p0001 := @gHwcnssbase A D hyp_hnwcutrelambfnnoarndv_1
  have p0002 :=
    @gPm32i (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWss (synChwcn D) (synChwcn A)) p0000 p0001
  have p0003 := @gFss (synCpw1 D) (synChwcn D) (synChwcn A) (synChnwcutrel R D)
  have p0004 := Nominal.mp p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorvalnoarndv`. -/
@[expose]
noncomputable def gHnwcutambfactorvalnoarndv (A : Class) (D : Class) (R : Class)
    (q : Var) (_dv_D_q : q ∉ D.fv) (_dv_R_q : q ∉ R.fv)
    (hyp_hnwcutambfactorvalnoarndv_1 : Nominal.NPrf (synWss D A))
    (hyp_hnwcutambfactorvalnoarndv_2 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_hnwcutambfactorvalnoarndv_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A)))) :=
  by
  have p0000 :=
    @gHnwcutrelambfnnoarndv A D R hyp_hnwcutambfactorvalnoarndv_1
      hyp_hnwcutambfactorvalnoarndv_2
  have p0001 := @gSifmap (synCpw1 D) (synChwcn A) (synChnwcutrel R D)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gId (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0004 := @gHnwcutsirelvalndv D R q hyp_hnwcutambfactorvalnoarndv_2
  have p0005 := @gHwcnssbase A D hyp_hnwcutambfactorvalnoarndv_1
  have p0006 := @gPw12argcl (.cv q) D
  have p0007 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0008 :=
    @gHnwcutcodecnclndv (synCuni (synCuni (.cv q))) D R hyp_hnwcutambfactorvalnoarndv_2
  have p0009 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwcn D)) p0007
      p0008
  have p0010 :=
    @gSseldi (.classMem (.cv q) (synCpw1 (synCpw1 D))) (synChwcn D) (synChwcn A)
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) p0005 p0009
  have p0011 :=
    @gQmapcompvald (.classMem (.cv q) (synCpw1 (synCpw1 D))) A
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synCsi (synChnwcutrel R D))
      (synCpw1 (synCpw1 D)) q hyp_hnwcutambfactorvalnoarndv_3 p0002 p0003 p0004 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorvalcodendv`. -/
@[expose]
noncomputable def gHnwcutambfactorvalcodendv (A : Class) (B : Class) (q : Var)
    (dv_B_q : q ∉ B.fv)
    (hyp_hnwcutambfactorvalcodendv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_hnwcutambfactorvalcodendv_2 : Nominal.NPrf (.classMem B (synChwcn A))) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) B)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B)))) (.cv q))
          (synCec (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
              (synCuni (synCuni (.cv q)))) (synChwniso A)))) :=
  by
  have dv_cache_0001 : q ∉ ((synCfv (synC2nd) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_B_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCfv (synC1st) B)).fv :=
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
  have p0000 := @gHwcnbaseclndv A B
  have p0001 := Nominal.mp hyp_hnwcutambfactorvalcodendv_2 p0000
  have p0002 := @gHwcnweclndv A B
  have p0003 := Nominal.mp hyp_hnwcutambfactorvalcodendv_2 p0002
  have p0004 :=
    @gHnwcutambfactorvalnoarndv A (synCfv (synC2nd) B) (synCfv (synC1st) B) q
      dv_cache_0001 dv_cache_0002 p0001 p0003 hyp_hnwcutambfactorvalcodendv_1
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnwcuttxpeq1dndv`. -/
@[expose]
noncomputable def gHnwcuttxpeq1dndv (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_hnwcuttxpeq1dndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCtxp A C) (synCtxp B C))) :=
  by
  have p0000 := @gCoeq2d ph A B (synCcnv (synC1st)) hyp_hnwcuttxpeq1dndv_1
  have p0001 :=
    @gIneq1d ph (synCcom (synCcnv (synC1st)) A) (synCcom (synCcnv (synC1st)) B)
      (synCcom (synCcnv (synC2nd)) C) p0000
  have p0002 := (Nominal.classEqRefl (synCtxp A C))
  have p0003 := (Nominal.classEqRefl (synCtxp B C))
  have p0004 :=
    @gN3eqtr4g ph
      (synCin (synCcom (synCcnv (synC1st)) A) (synCcom (synCcnv (synC2nd)) C))
      (synCin (synCcom (synCcnv (synC1st)) B) (synCcom (synCcnv (synC2nd)) C))
      (synCtxp A C) (synCtxp B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnwcutimageeqdndv`. -/
@[expose]
noncomputable def gHnwcutimageeqdndv (ph : Wff) (A : Class) (B : Class)
    (hyp_hnwcutimageeqdndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCimage A) (synCimage B))) :=
  by
  have p0000 := @gSieqdndv ph A B hyp_hnwcutimageeqdndv_1
  have p0001 := @gCnveqd ph (synCsi A) (synCsi B) p0000
  have p0002 :=
    @gCoeq2d ph (synCcnv (synCsi A)) (synCcnv (synCsi B)) (synCsset) p0001
  have p0003 :=
    @gHnwcuttxpeq1dndv ph (synCcom (synCsset) (synCcnv (synCsi A)))
      (synCcom (synCsset) (synCcnv (synCsi B))) (synCvv) p0002
  have p0004 :=
    (Nominal.classEqRefl (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))))
  have p0005 :=
    (Nominal.classEqRefl (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))))
  have p0006 :=
    @gN3eqtr4g ph (synCtxp (synCcom (synCsset) (synCcnv (synCsi A))) (synCvv))
      (synCtxp (synCcom (synCsset) (synCcnv (synCsi B))) (synCvv))
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))) p0003 p0004 p0005
  have p0007 :=
    @gDifeq2d ph (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))) (synCins2 (synCsset))
      p0006
  have p0015 :=
    @gDifeq1d ph (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))) (synCins2 (synCsset))
      p0006
  have p0016 :=
    @gUneq12d ph
      (synCdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))))
      (synCdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))))
      (synCdif (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))
        (synCins2 (synCsset)))
      (synCdif (synCins3 (synCcom (synCsset) (synCcnv (synCsi B))))
        (synCins2 (synCsset)))
      p0007 p0015
  have p0017 :=
    (Nominal.classEqRefl (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))))
  have p0018 :=
    (Nominal.classEqRefl (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi B))))))
  have p0019 :=
    @gN3eqtr4g ph
      (synCun (synCdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))))
        (synCdif (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))
          (synCins2 (synCsset))))
      (synCun (synCdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))))
        (synCdif (synCins3 (synCcom (synCsset) (synCcnv (synCsi B))))
          (synCins2 (synCsset))))
      (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))))
      (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))))
      p0016 p0017 p0018
  have p0020 :=
    @gImaeq1d ph
      (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))))
      (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi B)))))
      (synC1c) p0019
  have p0021 :=
    @gCompleqd ph
      (synCima (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c))
      (synCima (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi B))))) (synC1c))
      p0020
  have p0022 := (Nominal.classEqRefl (synCimage A))
  have p0023 := (Nominal.classEqRefl (synCimage B))
  have p0024 :=
    @gN3eqtr4g ph
      (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c)))
      (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi B))))) (synC1c)))
      (synCimage A) (synCimage B) p0021 p0022 p0023
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutreleq12dndv`. -/
@[expose]
noncomputable def gHnwcutreleq12dndv (ph : Wff) (D : Class) (R : Class) (S : Class)
    (E : Class) (hyp_hnwcutreleq12dndv_1 : Nominal.NPrf (.imp ph (.classEq R S)))
    (hyp_hnwcutreleq12dndv_2 : Nominal.NPrf (.imp ph (.classEq D E))) :
    Nominal.NPrf (.imp ph (.classEq (synChnwcutrel R D) (synChnwcutrel S E))) :=
  by
  have p0000 := @gReseq2d ph R S (synCid) hyp_hnwcutreleq12dndv_1
  have p0001 :=
    @gHnwcutimageeqdndv ph (synCres (synCid) R) (synCres (synCid) S) p0000
  have p0002 :=
    @gCoeq1d ph (synCimage (synCres (synCid) R)) (synCimage (synCres (synCid) S))
      (synCcom (synCcross) (synCtxp (synCid) (synCid))) p0001
  have p0003 :=
    @gHnwcuttxpeq1dndv ph
      (synCcom (synCimage (synCres (synCid) R))
        (synCcom (synCcross) (synCtxp (synCid) (synCid))))
      (synCcom (synCimage (synCres (synCid) S))
        (synCcom (synCcross) (synCtxp (synCid) (synCid))))
      (synCid) p0002
  have p0004 := (Nominal.classEqRefl (synChnwcodefn R))
  have p0005 := (Nominal.classEqRefl (synChnwcodefn S))
  have p0006 :=
    @gN3eqtr4g ph
      (synCtxp (synCcom (synCimage (synCres (synCid) R))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      (synCtxp (synCcom (synCimage (synCres (synCid) S))
          (synCcom (synCcross) (synCtxp (synCid) (synCid)))) (synCid))
      (synChnwcodefn R) (synChnwcodefn S) p0003 p0004 p0005
  have p0007 := @gReseq2d ph D E (synCid) hyp_hnwcutreleq12dndv_2
  have p0008 :=
    @gHnwcutimageeqdndv ph (synCres (synCid) D) (synCres (synCid) E) p0007
  have p0009 := @gDifeq1d ph R S (synCid) hyp_hnwcutreleq12dndv_1
  have p0010 := @gCnveqd ph (synCdif R (synCid)) (synCdif S (synCid)) p0009
  have p0011 :=
    @gHnwcutimageeqdndv ph (synCcnv (synCdif R (synCid)))
      (synCcnv (synCdif S (synCid))) p0010
  have p0012 :=
    @gCoeq12d ph (synCimage (synCres (synCid) D)) (synCimage (synCres (synCid) E))
      (synCimage (synCcnv (synCdif R (synCid))))
      (synCimage (synCcnv (synCdif S (synCid)))) p0008 p0011
  have p0013 := (Nominal.classEqRefl (synChnwsegfn R D))
  have p0014 := (Nominal.classEqRefl (synChnwsegfn S E))
  have p0015 :=
    @gN3eqtr4g ph
      (synCcom (synCimage (synCres (synCid) D))
        (synCimage (synCcnv (synCdif R (synCid)))))
      (synCcom (synCimage (synCres (synCid) E))
        (synCimage (synCcnv (synCdif S (synCid)))))
      (synChnwsegfn R D) (synChnwsegfn S E) p0012 p0013 p0014
  have p0016 :=
    @gCoeq12d ph (synChnwcodefn R) (synChnwcodefn S) (synChnwsegfn R D)
      (synChnwsegfn S E) p0006 p0015
  have p0017 := (Nominal.classEqRefl (synChnwcutfn R D))
  have p0018 := (Nominal.classEqRefl (synChnwcutfn S E))
  have p0019 :=
    @gN3eqtr4g ph (synCcom (synChnwcodefn R) (synChnwsegfn R D))
      (synCcom (synChnwcodefn S) (synChnwsegfn S E)) (synChnwcutfn R D)
      (synChnwcutfn S E) p0016 p0017 p0018
  have p0020 := @gReseq1 (synChnwcutfn R D) (synChnwcutfn S E) (synCpw1 D)
  have p0021 :=
    @gSyl ph (.classEq (synChnwcutfn R D) (synChnwcutfn S E))
      (.classEq (synCres (synChnwcutfn R D) (synCpw1 D))
        (synCres (synChnwcutfn S E) (synCpw1 D)))
      p0019 p0020
  have p0022 := @gPw1eq D E
  have p0023 :=
    @gSyl ph (.classEq D E) (.classEq (synCpw1 D) (synCpw1 E)) hyp_hnwcutreleq12dndv_2
      p0022
  have p0024 := @gReseq2d ph (synCpw1 D) (synCpw1 E) (synChnwcutfn S E) p0023
  have p0025 :=
    @gEqtrd ph (synCres (synChnwcutfn R D) (synCpw1 D))
      (synCres (synChnwcutfn S E) (synCpw1 D))
      (synCres (synChnwcutfn S E) (synCpw1 E)) p0021 p0024
  have p0026 := (Nominal.classEqRefl (synChnwcutrel R D))
  have p0027 := (Nominal.classEqRefl (synChnwcutrel S E))
  have p0028 :=
    @gN3eqtr4g ph (synCres (synChnwcutfn R D) (synCpw1 D))
      (synCres (synChnwcutfn S E) (synCpw1 E)) (synChnwcutrel R D)
      (synChnwcutrel S E) p0025 p0026 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeeq12clndv`. -/
@[expose]
noncomputable def gHnwcutcodeeq12clndv (C : Class) (D : Class) (R : Class) (S : Class)
    (E : Class) :
    Nominal.NPrf
      (.imp (.classMem C (synCvv)) (.imp (synWa (.classEq R S) (.classEq D E))
          (.classEq (synChnwcutcode R D C) (synChnwcutcode S E C)))) :=
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
      ((Wff.imp (synWa (.classEq R S) (.classEq D E))
          (.classEq (synChnwcutcode R D C) (synChnwcutcode S E C)))).fv :=
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
  have p0000 := @gBiid (synWa (.classEq R S) (.classEq D E))
  have p0001 :=
    @gA1i
      (synWb (synWa (.classEq R S) (.classEq D E)) (synWa (.classEq R S) (.classEq D E)))
      (.classEq (.cv x) C) p0000
  have p0002 := @gHnwcutcodeeq3 (.cv x) C D R dv_cache_0001
  have p0003 := @gHnwcutcodeeq3 (.cv x) C E S dv_cache_0002
  have p0004 :=
    @gEqeq12d (.classEq (.cv x) C) (synChnwcutcode R D (.cv x)) (synChnwcutcode R D C)
      (synChnwcutcode S E (.cv x)) (synChnwcutcode S E C) p0002 p0003
  have p0005 :=
    @gImbi12d (.classEq (.cv x) C) (synWa (.classEq R S) (.classEq D E))
      (synWa (.classEq R S) (.classEq D E))
      (.classEq (synChnwcutcode R D (.cv x)) (synChnwcutcode S E (.cv x)))
      (.classEq (synChnwcutcode R D C) (synChnwcutcode S E C)) p0001 p0004
  have p0006 := @gHnwcutcodeeq12ndv x D R S E
  have p0007 :=
    @gVtoclg
      (.imp (synWa (.classEq R S) (.classEq D E))
        (.classEq (synChnwcutcode R D (.cv x)) (synChnwcutcode S E (.cv x))))
      (.imp (synWa (.classEq R S) (.classEq D E))
        (.classEq (synChnwcutcode R D C) (synChnwcutcode S E C)))
      x C (synCvv) dv_cache_0003 dv_cache_0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorvalimpclndv`. -/
@[expose]
noncomputable def gHnwcutambfactorvalimpclndv (A : Class) (B : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (dv_B_q : q ∉ B.fv)
    (hyp_hnwcutambfactorvalimpclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synChwcn A))
        (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) B)))) (.classEq
            (synCfv (synCcom (synChnqmap1 A)
                (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
              (.cv q)) (synCec (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
                (synCuni (synCuni (.cv q)))) (synChwniso A))))) :=
  by
  have dv_cache_0001 :
    q ∉
      ((synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synC0)))).fv :=
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
    @gId
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0001 :=
    @gFveq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      B
      (synCif (.classMem B (synChwcn A)) B
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC2nd) p0000
  have p0002 :=
    @gPw1eq (synCfv (synC2nd) B)
      (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0003 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCfv (synC2nd) B) (synCfv (synC2nd)
          (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCpw1 (synCfv (synC2nd) B)) (synCpw1 (synCfv (synC2nd)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      p0001 p0002
  have p0004 :=
    @gPw1eq (synCpw1 (synCfv (synC2nd) B))
      (synCpw1 (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
  have p0005 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCpw1 (synCfv (synC2nd) B)) (synCpw1 (synCfv (synC2nd)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classEq (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synCpw1 (synCpw1
            (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
      p0003 p0004
  have p0006 :=
    @gEleq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) B)))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.cv q) p0005
  have p0008 :=
    @gFveq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      B
      (synCif (.classMem B (synChwcn A)) B
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC1st) p0000
  have p0011 :=
    @gHnwcutreleq12dndv
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) B) (synCfv (synC1st) B)
      (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0008 p0001
  have p0012 :=
    @gSieqdndv
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))
      (synChnwcutrel (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0011
  have p0013 :=
    @gCoeq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B)))
      (synCsi (synChnwcutrel (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synChnqmap1 A) p0012
  have p0014 :=
    @gFveq1d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.cv q)
      (synCcom (synChnqmap1 A)
        (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
      (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
      p0013
  have p0019 :=
    @gJca
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCfv (synC1st) B) (synCfv (synC1st)
          (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCfv (synC2nd) B) (synCfv (synC2nd)
          (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0008 p0001
  have p0020 := @gVex q
  have p0021 := @gUniex (.cv q) p0020
  have p0022 := @gUniex (synCuni (.cv q)) p0021
  have p0023 :=
    @gHnwcutcodeeq12clndv (synCuni (synCuni (.cv q))) (synCfv (synC2nd) B)
      (synCfv (synC1st) B)
      (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWa (.classEq (synCfv (synC1st) B) (synCfv (synC1st)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))) (.classEq (synCfv (synC2nd) B) (synCfv (synC2nd)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classEq (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
          (synCuni (synCuni (.cv q)))) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCuni (synCuni (.cv q)))))
      p0019 p0024
  have p0026 :=
    @gEceq1
      (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
        (synCuni (synCuni (.cv q))))
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCuni (synCuni (.cv q))))
      (synChwniso A)
  have p0027 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
          (synCuni (synCuni (.cv q)))) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCuni (synCuni (.cv q)))))
      (.classEq (synCec (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
            (synCuni (synCuni (.cv q)))) (synChwniso A)) (synCec (synChnwcutcode
            (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0025 p0026
  have p0028 :=
    @gEqeq12d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synCcom (synChnqmap1 A)
          (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B)))) (.cv q))
      (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))))))) (.cv q))
      (synCec (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
          (synCuni (synCuni (.cv q)))) (synChwniso A))
      (synCec (synChnwcutcode (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCuni (synCuni (.cv q)))) (synChwniso A))
      p0014 p0027
  have p0029 :=
    @gImbi12d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) B))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
      (.classEq (synCfv (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B)))) (.cv q))
        (synCec (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                  (synCif (.classMem B (synChwcn A)) B (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                    (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0))))))) (.cv q)) (synCec (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0006 p0028
  have p0030 := @gEqid (synC0)
  have p0031 := @gSimpr (.classEq (synC0) (synC0)) (.classMem B (synChwcn A))
  have p0032 := @gHncodecmpdefaultcnndv A
  have p0033 :=
    @gA1i
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (synWa (.classEq (synC0) (synC0)) (.neg (.classMem B (synChwcn A)))) p0032
  have p0034 :=
    @gIfclda (.classEq (synC0) (synC0)) (.classMem B (synChwcn A)) B
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A) p0031 p0033
  have p0035 := Nominal.mp p0030 p0034
  have p0036 :=
    @gHnwcutambfactorvalcodendv A
      (synCif (.classMem B (synChwcn A)) B
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      q dv_cache_0001 hyp_hnwcutambfactorvalimpclndv_1 p0035
  have p0037 :=
    @gDedth (.classMem B (synChwcn A))
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) B)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B)))) (.cv q))
          (synCec (synChnwcutcode (synCfv (synC1st) B) (synCfv (synC2nd) B)
              (synCuni (synCuni (.cv q)))) (synChwniso A))))
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))))))) (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0))))))) (.cv q)) (synCec (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCuni (synCuni (.cv q)))) (synChwniso A))))
      B (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      p0029 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorvalimpndv`. -/
@[expose]
noncomputable def gHnwcutambfactorvalimpndv (u : Var) (A : Class) (q : Var)
    (dv_A_q : q ∉ A.fv) (_dv_A_u : u ∉ A.fv) (dv_q_u : q ≠ u)
    (hyp_hnwcutambfactorvalimpndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv q)) (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (synCuni (synCuni (.cv q)))) (synChwniso A))))) :=
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
    @gHnwcutambfactorvalimpclndv A (.cv u) q dv_cache_0001 dv_cache_0002
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambordbrproxyimpndv`. -/
@[expose]
noncomputable def gHnwcutambordbrproxyimpndv (u : Var) (A : Class) (r : Var) (q : Var)
    (p : Var) (dv_A_p : p ∉ A.fv) (dv_A_q : q ∉ A.fv) (dv_A_r : r ∉ A.fv)
    (dv_A_u : u ∉ A.fv) (_dv_p_q : p ≠ q) (_dv_p_r : p ≠ r) (dv_p_u : p ≠ u)
    (_dv_q_r : q ≠ r) (dv_q_u : q ≠ u) (_dv_r_u : r ≠ u)
    (hyp_hnwcutambordbrproxyimpndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A)))
          (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
            (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
        (synWb (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
          (synWbr (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A)
                (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u))))) (.cv q))))) :=
  by
  have dv_cache_0001 : p ∉ ((synCfv (synC1st) (.cv u))).fv := by
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
    @gSimpr
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))))
  have p0001 :=
    @gPw12si2brndv (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) q p
      dv_cache_0001
  have p0002 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))))
      (synWb (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
        (synWbr (synCuni (synCuni (.cv p))) (synCfv (synC1st) (.cv u))
          (synCuni (synCuni (.cv q)))))
      p0000 p0001
  have p0003 :=
    @gA1i (.classMem A (synCvv))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      hyp_hnwcutambordbrproxyimpndv_1
  have p0004 :=
    @gSimpl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))))
  have p0005 :=
    @gSimpr (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A))
  have p0006 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0004 p0005
  have p0008 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
  have p0009 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) p0000 p0008
  have p0010 := @gPw12argcl (.cv p) (synCfv (synC2nd) (.cv u))
  have p0011 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
        (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))))
      p0009 p0010
  have p0012 :=
    @gSimpld
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
      (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))) p0011
  have p0014 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
  have p0015 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) p0000 p0014
  have p0016 := @gPw12argcl (.cv q) (synCfv (synC2nd) (.cv u))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u)))
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      p0015 p0016
  have p0018 :=
    @gSimpld
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u)))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0017
  have p0019 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
      (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))) p0012 p0018
  have p0020 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
        (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))))
      p0006 p0019
  have p0021 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
          (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u)))))
      p0003 p0020
  have p0022 :=
    @gHnwcutcodecmpbrclndv u A (synCuni (synCuni (.cv p)))
      (synCuni (synCuni (.cv q))) dv_cache_0002
  have p0023 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
            (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))))))
      (synWb (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))))
        (synWbr (synCuni (synCuni (.cv p))) (synCfv (synC1st) (.cv u))
          (synCuni (synCuni (.cv q)))))
      p0021 p0022
  have p0024 :=
    @gBicomd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))))
      (synWbr (synCuni (synCuni (.cv p))) (synCfv (synC1st) (.cv u))
        (synCuni (synCuni (.cv q))))
      p0023
  have p0025 :=
    @gBitrd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
      (synWbr (synCuni (synCuni (.cv p))) (synCfv (synC1st) (.cv u))
        (synCuni (synCuni (.cv q))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))))
      p0002 p0024
  have p0027 :=
    @gSimpl (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A))
  have p0028 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv r) (synChncodecmpset A)) p0004 p0027
  have p0038 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u))) p0006 p0012
  have p0039 := @gHnwcutcodeambientclndv u A (synCuni (synCuni (.cv p))) dv_cache_0002
  have p0040 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChwcn A))
      p0038 p0039
  have p0050 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))) p0006 p0018
  have p0051 := @gHnwcutcodeambientclndv u A (synCuni (synCuni (.cv q))) dv_cache_0002
  have p0052 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (synCuni (synCuni (.cv q))) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))) (synChwcn A))
      p0050 p0051
  have p0053 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))) (synChwcn A))
      p0040 p0052
  have p0054 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwcn A)))
      p0028 p0053
  have p0055 :=
    @gHncodecmpquotbrproxyimpclndv A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCuni (synCuni (.cv p))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCuni (synCuni (.cv q))))
      r dv_cache_0003 hyp_hnwcutambordbrproxyimpndv_1
  have p0056 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (synWa (.classMem
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv p)))) (synChwcn A)) (.classMem
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv q)))) (synChwcn A))))
      (synWb (synWbr (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv p)))) (synChwniso A))
          (synClnqord (.cv r) (synChwcn A)) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv q)))) (synChwniso A))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChncodecmpset A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q))))))
      p0054 p0055
  have p0057 :=
    @gBicomd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWbr (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))))
      p0056
  have p0058 :=
    @gBitrd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChncodecmpset A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))))
      (synWbr (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0025 p0057
  have p0065 :=
    @gHnwcutambfactorvalimpndv u A p dv_cache_0004 dv_cache_0002 dv_cache_0005
      hyp_hnwcutambordbrproxyimpndv_1
  have p0066 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv u) (synChwcn A))
      (.imp (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv p)))) (synChwniso A))))
      p0006 p0065
  have p0067 :=
    @gMpd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)))
      p0009 p0066
  have p0074 :=
    @gHnwcutambfactorvalimpndv u A q dv_cache_0006 dv_cache_0002 dv_cache_0007
      hyp_hnwcutambordbrproxyimpndv_1
  have p0075 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv u) (synChwcn A))
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv q)) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv q)))) (synChwniso A))))
      p0006 p0074
  have p0076 :=
    @gMpd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv q)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0015 p0075
  have p0077 :=
    @gBreq12d
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv p))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChwniso A))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv q))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))) (synChwniso A))
      (synClnqord (.cv r) (synChwcn A)) p0067 p0076
  have p0078 :=
    @gBicomd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWbr (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A)
            (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv q)))
      (synWbr (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0077
  have p0079 :=
    @gBitrd
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
      (synWbr (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)) (synClnqord (.cv r) (synChwcn A))
        (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      (synWbr (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A)
            (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv q)))
      p0058 p0078
  exact p0079

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorfnnoarndv`. -/
@[expose]
noncomputable def gHnwcutambfactorfnnoarndv (A : Class) (D : Class) (R : Class)
    (hyp_hnwcutambfactorfnnoarndv_1 : Nominal.NPrf (synWss D A))
    (hyp_hnwcutambfactorfnnoarndv_2 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_hnwcutambfactorfnnoarndv_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWf (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
        (synCpw1 (synCpw1 D)) (synChnord A)) :=
  by
  have p0000 := @gHnqmap1f A hyp_hnwcutambfactorfnnoarndv_3
  have p0001 := @gHnwcutrelfndv D R hyp_hnwcutambfactorfnnoarndv_2
  have p0002 := @gHwcnssbase A D hyp_hnwcutambfactorfnnoarndv_1
  have p0003 :=
    @gPm32i (synWf (synChnwcutrel R D) (synCpw1 D) (synChwcn D))
      (synWss (synChwcn D) (synChwcn A)) p0001 p0002
  have p0004 := @gFss (synCpw1 D) (synChwcn D) (synChwcn A) (synChnwcutrel R D)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gSifmap (synCpw1 D) (synChwcn A) (synChnwcutrel R D)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gPm32i (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
      (synWf (synCsi (synChnwcutrel R D)) (synCpw1 (synCpw1 D)) (synCpw1 (synChwcn A)))
      p0000 p0007
  have p0009 :=
    @gFco (synCpw1 (synCpw1 D)) (synCpw1 (synChwcn A)) (synChnord A)
      (synChnqmap1 A) (synCsi (synChnwcutrel R D))
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassinjambnoarndv`. -/
@[expose]
noncomputable def gHnwcutclassinjambnoarndv (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (hyp_hnwcutclassinjambnoarndv_1 : Nominal.NPrf (synWss D A))
    (hyp_hnwcutclassinjambnoarndv_2 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_hnwcutclassinjambnoarndv_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
            (synCec (synChnwcutcode R D C) (synChwniso A))) (.classEq B C))) :=
  by
  have p0000 :=
    @gSimpr (synWa (.classMem B D) (.classMem C D))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
        (synCec (synChnwcutcode R D C) (synChwniso A)))
  have p0001 :=
    @gSimpl (synWa (.classMem B D) (.classMem C D))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
        (synCec (synChnwcutcode R D C) (synChwniso A)))
  have p0002 := @gHwcnssbase A D hyp_hnwcutclassinjambnoarndv_1
  have p0003 := @gSimpl (.classMem B D) (.classMem C D)
  have p0004 := @gHnwcutcodecnclndv B D R hyp_hnwcutclassinjambnoarndv_2
  have p0005 :=
    @gSyl (synWa (.classMem B D) (.classMem C D)) (.classMem B D)
      (.classMem (synChnwcutcode R D B) (synChwcn D)) p0003 p0004
  have p0006 :=
    @gSseldi (synWa (.classMem B D) (.classMem C D)) (synChwcn D) (synChwcn A)
      (synChnwcutcode R D B) p0002 p0005
  have p0008 := @gSimpr (.classMem B D) (.classMem C D)
  have p0009 := @gHnwcutcodecnclndv C D R hyp_hnwcutclassinjambnoarndv_2
  have p0010 :=
    @gSyl (synWa (.classMem B D) (.classMem C D)) (.classMem C D)
      (.classMem (synChnwcutcode R D C) (synChwcn D)) p0008 p0009
  have p0011 :=
    @gSseldi (synWa (.classMem B D) (.classMem C D)) (synChwcn D) (synChwcn A)
      (synChnwcutcode R D C) p0002 p0010
  have p0012 :=
    @gJca (synWa (.classMem B D) (.classMem C D))
      (.classMem (synChnwcutcode R D B) (synChwcn A))
      (.classMem (synChnwcutcode R D C) (synChwcn A)) p0006 p0011
  have p0013 :=
    @gHwnisoclasseqbcl A (synChnwcutcode R D B) (synChnwcutcode R D C)
      hyp_hnwcutclassinjambnoarndv_3
  have p0014 :=
    @gSyl (synWa (.classMem B D) (.classMem C D))
      (synWa (.classMem (synChnwcutcode R D B) (synChwcn A))
        (.classMem (synChnwcutcode R D C) (synChwcn A)))
      (synWb (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A)))
        (synWbr (synChnwcutcode R D B) (synChwniso A) (synChnwcutcode R D C)))
      p0012 p0013
  have p0015 :=
    @gBiimpd (synWa (.classMem B D) (.classMem C D))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
        (synCec (synChnwcutcode R D C) (synChwniso A)))
      (synWbr (synChnwcutcode R D B) (synChwniso A) (synChnwcutcode R D C)) p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWa (.classMem B D) (.classMem C D))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A)))
        (synWbr (synChnwcutcode R D B) (synChwniso A) (synChnwcutcode R D C)))
      p0001 p0015
  have p0017 :=
    @gMpd
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
        (synCec (synChnwcutcode R D C) (synChwniso A)))
      (synWbr (synChnwcutcode R D B) (synChwniso A) (synChnwcutcode R D C)) p0000
      p0016
  have p0025 :=
    @gJca (synWa (.classMem B D) (.classMem C D))
      (.classMem (synChnwcutcode R D B) (synChwcn D))
      (.classMem (synChnwcutcode R D C) (synChwcn D)) p0005 p0010
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWa (.classMem B D) (.classMem C D))
      (synWa (.classMem (synChnwcutcode R D B) (synChwcn D))
        (.classMem (synChnwcutcode R D C) (synChwcn D)))
      p0001 p0025
  have p0027 := @gHwnisobaserestrcl A (synChnwcutcode R D B) (synChnwcutcode R D C) D
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWa (.classMem (synChnwcutcode R D B) (synChwcn D))
        (.classMem (synChnwcutcode R D C) (synChwcn D)))
      (.imp (synWbr (synChnwcutcode R D B) (synChwniso A) (synChnwcutcode R D C))
        (synWbr (synChnwcutcode R D B) (synChwniso D) (synChnwcutcode R D C)))
      p0026 p0027
  have p0029 :=
    @gMpd
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWbr (synChnwcutcode R D B) (synChwniso A) (synChnwcutcode R D C))
      (synWbr (synChnwcutcode R D B) (synChwniso D) (synChnwcutcode R D C)) p0017
      p0028
  have p0039 := @gBrex R D (synCwe)
  have p0040 := Nominal.mp hyp_hnwcutclassinjambnoarndv_2 p0039
  have p0041 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0040
  have p0042 :=
    @gHwnisoclasseqbcl D (synChnwcutcode R D B) (synChnwcutcode R D C) p0041
  have p0043 :=
    @gSyl
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWa (.classMem (synChnwcutcode R D B) (synChwcn D))
        (.classMem (synChnwcutcode R D C) (synChwcn D)))
      (synWb (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D C) (synChwniso D)))
        (synWbr (synChnwcutcode R D B) (synChwniso D) (synChnwcutcode R D C)))
      p0026 p0042
  have p0044 :=
    @gBiimprd
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      (synWbr (synChnwcutcode R D B) (synChwniso D) (synChnwcutcode R D C)) p0043
  have p0045 :=
    @gMpd
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWbr (synChnwcutcode R D B) (synChwniso D) (synChnwcutcode R D C))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      p0029 p0044
  have p0047 := @gHnwcutclassinjclndv B C D R hyp_hnwcutclassinjambnoarndv_2
  have p0048 :=
    @gSyl
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (synWa (.classMem B D) (.classMem C D))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))
      p0001 p0047
  have p0049 :=
    @gMpd
      (synWa (synWa (.classMem B D) (.classMem C D))
        (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
          (synCec (synChnwcutcode R D C) (synChwniso A))))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      (.classEq B C) p0045 p0048
  have p0050 :=
    @gEx (synWa (.classMem B D) (.classMem C D))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso A))
        (synCec (synChnwcutcode R D C) (synChwniso A)))
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorf1noarndv`. -/
@[expose]
noncomputable def gHnwcutambfactorf1noarndv (A : Class) (D : Class) (R : Class)
    (hyp_hnwcutambfactorf1noarndv_1 : Nominal.NPrf (synWss D A))
    (hyp_hnwcutambfactorf1noarndv_2 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_hnwcutambfactorf1noarndv_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
        (synCpw1 (synCpw1 D)) (synChnord A)) :=
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
  have dv_cache_0005 : r ∉ ((synCpw1 (synCpw1 D))).fv :=
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
  have dv_cache_0006 : q ∉ ((synWbr R (synCwe) D)).fv :=
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
  have dv_cache_0007 : r ∉ ((synWbr R (synCwe) D)).fv :=
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
  have dv_cache_0009 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
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
    q ∉ ((synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))).fv :=
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
    r ∉ ((synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))).fv :=
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
    @gHnwcutambfactorfnnoarndv A D R hyp_hnwcutambfactorf1noarndv_1
      hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0001 :=
    @gSimpl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
        (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
  have p0002 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (.cv r) (synCpw1 (synCpw1 D))))
  have p0003 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
  have p0004 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (.cv r) (synCpw1 (synCpw1 D))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0002 p0003
  have p0005 := @gPw12argcl (.cv q) D
  have p0006 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv q))) D)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @gSimprd
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0008 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0001 p0007
  have p0013 :=
    @gHnwcutambfactorvalnoarndv A D R q dv_cache_0001 dv_cache_0002
      hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2
      hyp_hnwcutambfactorf1noarndv_3
  have p0014 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0004 p0013
  have p0015 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0001 p0014
  have p0016 :=
    @gEqcomd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A)) p0015
  have p0017 :=
    @gSimpr
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
        (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
  have p0018 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A))
      (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
      (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)) p0016
      p0017
  have p0021 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
  have p0022 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (.cv r) (synCpw1 (synCpw1 D))))
      (.classMem (.cv r) (synCpw1 (synCpw1 D))) p0002 p0021
  have p0023 :=
    @gHnwcutambfactorvalnoarndv A D R r dv_cache_0003 dv_cache_0004
      hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2
      hyp_hnwcutambfactorf1noarndv_3
  have p0024 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso A)))
      p0022 p0023
  have p0025 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso A)))
      p0001 p0024
  have p0026 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A))
      (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso A)) p0018
      p0025
  have p0033 :=
    @gSimpld
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0034 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv q))) D) p0001 p0033
  have p0039 := @gPw12argcl (.cv r) D
  have p0040 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv r))) D)
        (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))))
      p0022 p0039
  have p0041 :=
    @gSimpld
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv r))) D)
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0040
  have p0042 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv r))) D) p0001 p0041
  have p0043 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synCuni (synCuni (.cv r))) D) p0034 p0042
  have p0044 :=
    @gHnwcutclassinjambnoarndv A (synCuni (synCuni (.cv q)))
      (synCuni (synCuni (.cv r))) D R hyp_hnwcutambfactorf1noarndv_1
      hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0045 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) D)
        (.classMem (synCuni (synCuni (.cv r))) D))
      (.imp (.classEq
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso A)))
        (.classEq (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r)))))
      p0043 p0044
  have p0046 :=
    @gMpd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (.classEq (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso A))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso A)))
      (.classEq (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r)))) p0026 p0045
  have p0047 :=
    @gSneqd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r))) p0046
  have p0048 :=
    @gSneqd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCsn (synCuni (synCuni (.cv r))))
      p0047
  have p0049 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))
      (synCsn (synCsn (synCuni (synCuni (.cv r))))) p0008 p0048
  have p0056 :=
    @gSimprd
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv r))) D)
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0040
  have p0057 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0001 p0056
  have p0058 :=
    @gEqcomd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r))))) p0057
  have p0059 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r))))
      (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv r))))) (.cv r) p0049 p0058
  have p0060 :=
    @gEx
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
        (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0059
  have p0061 :=
    @gRalrimivva (synWbr R (synCwe) D)
      (.imp (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
          (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
        (.classEq (.cv q) (.cv r)))
      q r (synCpw1 (synCpw1 D)) (synCpw1 (synCpw1 D)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0060
  have p0062 := Nominal.mp hyp_hnwcutambfactorf1noarndv_2 p0061
  have p0063 :=
    @gPm32i
      (synWf (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
        (synCpw1 (synCpw1 D)) (synChnord A))
      (synWral q (synCpw1 (synCpw1 D)) (synWral r (synCpw1 (synCpw1 D)) (.imp (.classEq
              (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
              (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
            (.classEq (.cv q) (.cv r)))))
      p0000 p0062
  have p0064 :=
    @gDff13 q r (synCpw1 (synCpw1 D)) (synChnord A)
      (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) dv_cache_0009
      dv_cache_0005 dv_cache_0010 dv_cache_0011 dv_cache_0008
  have p0065_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
          (synCpw1 (synCpw1 D)) (synChnord A)) (synWa
          (synWf (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
            (synCpw1 (synCpw1 D)) (synChnord A)) (synWral q (synCpw1 (synCpw1 D))
            (synWral r (synCpw1 (synCpw1 D)) (.imp (.classEq
                  (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
                  (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
                (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synCpw1 synChnord synCqs
          synWrex synCec synCima synCsn synChwcn synChwniso
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
    @gMpbir
      (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
        (synCpw1 (synCpw1 D)) (synChnord A))
      (synWa (synWf (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D)))
          (synCpw1 (synCpw1 D)) (synChnord A)) (synWral q (synCpw1 (synCpw1 D))
          (synWral r (synCpw1 (synCpw1 D)) (.imp (.classEq
                (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv q))
                (synCfv (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel R D))) (.cv r)))
              (.classEq (.cv q) (.cv r))))))
      p0063 p0065_e01_recanon
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorf1codendv`. -/
@[expose]
noncomputable def gHnwcutambfactorf1codendv (A : Class) (B : Class)
    (hyp_hnwcutambfactorf1codendv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_hnwcutambfactorf1codendv_2 : Nominal.NPrf (.classMem B (synChwcn A))) :
    Nominal.NPrf
      (synWf1 (synCcom (synChnqmap1 A)
          (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A)) :=
  by
  have p0000 := @gHwcnbaseclndv A B
  have p0001 := Nominal.mp hyp_hnwcutambfactorf1codendv_2 p0000
  have p0002 := @gHwcnweclndv A B
  have p0003 := Nominal.mp hyp_hnwcutambfactorf1codendv_2 p0002
  have p0004 :=
    @gHnwcutambfactorf1noarndv A (synCfv (synC2nd) B) (synCfv (synC1st) B) p0001
      p0003 hyp_hnwcutambfactorf1codendv_1
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorf1impclndv`. -/
@[expose]
noncomputable def gHnwcutambfactorf1impclndv (A : Class) (B : Class)
    (hyp_hnwcutambfactorf1impclndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem B (synChwcn A)) (synWf1 (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A))) :=
  by
  have p0000 :=
    @gId
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0001 :=
    @gFveq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      B
      (synCif (.classMem B (synChwcn A)) B
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC1st) p0000
  have p0003 :=
    @gFveq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      B
      (synCif (.classMem B (synChwcn A)) B
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC2nd) p0000
  have p0004 :=
    @gHnwcutreleq12dndv
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) B) (synCfv (synC1st) B)
      (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0001 p0003
  have p0005 :=
    @gSieqdndv
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))
      (synChnwcutrel (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0004
  have p0006 :=
    @gCoeq2d
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B)))
      (synCsi (synChnwcutrel (synCfv (synC1st) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synChnqmap1 A) p0005
  have p0007 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A)
      (synCcom (synChnqmap1 A)
        (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
      (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
  have p0008 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCcom (synChnqmap1 A)
          (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
        (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))))))))
      (synWb (synWf1 (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A)) (synWf1
          (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                  (synCif (.classMem B (synChwcn A)) B (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                    (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A)))
      p0006 p0007
  have p0011 :=
    @gPw1eq (synCfv (synC2nd) B)
      (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0012 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCfv (synC2nd) B) (synCfv (synC2nd)
          (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCpw1 (synCfv (synC2nd) B)) (synCpw1 (synCfv (synC2nd)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      p0003 p0011
  have p0013 :=
    @gPw1eq (synCpw1 (synCfv (synC2nd) B))
      (synCpw1 (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
  have p0014 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCpw1 (synCfv (synC2nd) B)) (synCpw1 (synCfv (synC2nd)
            (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classEq (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synCpw1 (synCpw1
            (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
      p0012 p0013
  have p0015 :=
    @gF1eq2 (synCpw1 (synCpw1 (synCfv (synC2nd) B)))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synChnord A)
      (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
  have p0016 :=
    @gSyl
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (.classEq (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synCpw1 (synCpw1
            (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))))
      (synWb (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                  (synCif (.classMem B (synChwcn A)) B (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                    (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A)) (synWf1
          (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                  (synCif (.classMem B (synChwcn A)) B (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                    (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0))))))) (synCpw1 (synCpw1 (synCfv (synC2nd)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))))) (synChnord A)))
      p0014 p0015
  have p0017 :=
    @gBitrd
      (.classEq B (synCif (.classMem B (synChwcn A)) B
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWf1 (synCcom (synChnqmap1 A)
          (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A))
      (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))))))) (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A))
      (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))))))) (synCpw1 (synCpw1 (synCfv (synC2nd)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))) (synChnord A))
      p0008 p0016
  have p0018 := @gEqid (synC0)
  have p0019 := @gSimpr (.classEq (synC0) (synC0)) (.classMem B (synChwcn A))
  have p0020 := @gHncodecmpdefaultcnndv A
  have p0021 :=
    @gA1i
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (synWa (.classEq (synC0) (synC0)) (.neg (.classMem B (synChwcn A)))) p0020
  have p0022 :=
    @gIfclda (.classEq (synC0) (synC0)) (.classMem B (synChwcn A)) B
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A) p0019 p0021
  have p0023 := Nominal.mp p0018 p0022
  have p0024 :=
    @gHnwcutambfactorf1codendv A
      (synCif (.classMem B (synChwcn A)) B
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      hyp_hnwcutambfactorf1impclndv_1 p0023
  have p0025 :=
    @gDedth (.classMem B (synChwcn A))
      (synWf1 (synCcom (synChnqmap1 A)
          (synCsi (synChnwcutrel (synCfv (synC1st) B) (synCfv (synC2nd) B))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) B))) (synChnord A))
      (synWf1 (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st)
                (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd) (synCif (.classMem B (synChwcn A)) B
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0))))))) (synCpw1 (synCpw1 (synCfv (synC2nd)
              (synCif (.classMem B (synChwcn A)) B
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))) (synChnord A))
      B (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      p0017 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorf1impndv`. -/
@[expose]
noncomputable def gHnwcutambfactorf1impndv (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv)
    (hyp_hnwcutambfactorf1impndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (synWf1 (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChnord A))) :=
  by
  have p0000 := @gHnwcutambfactorf1impclndv A (.cv u) hyp_hnwcutambfactorf1impndv_1
  exact p0000


end NFChoice.DirectNominalPrf.WPPReplay

end
