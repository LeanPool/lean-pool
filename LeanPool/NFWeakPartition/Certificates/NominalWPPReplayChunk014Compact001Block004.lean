/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppstrictcomplement`. -/
@[expose]
noncomputable def gWppstrictcomplement (A : Class) (R : Class) (e : Var) (c : Var)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_A_c : c ∉ A.fv) (_dv_A_e : e ∉ A.fv)
    (_dv_R_c : c ∉ R.fv) (_dv_R_e : e ∉ R.fv) (_dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (synWb (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
          (synWbr (.cv e) R (.cv c)))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
  have p0001 :=
    @gSimpll (synWbr R (synCwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0002 := @gWppweconnex A R
  have p0003 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr R (synCwe) A) (synWbr R (synCconnex) A) p0001 p0002
  have p0004 :=
    @gSimpr (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)
  have p0005 :=
    @gSimplr (synWbr R (synCwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0006 :=
    @gConnexd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      A R (.cv c) (.cv e) p0003 p0004 p0005
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWo (synWbr (.cv c) R (.cv e)) (synWbr (.cv e) R (.cv c))) p0000 p0006
  have p0008 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWbr (.cv c) R (.cv e))
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      p0008 p0000
  have p0012 := @gWppweref A R
  have p0013 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr R (synCwe) A) (synWbr R (synCref) A) p0001 p0012
  have p0015 :=
    @gRefd
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      A R (.cv e) p0013 p0005
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr (.cv e) R (.cv e)) p0010 p0015
  have p0018 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))) p0008 p0018
  have p0020 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWne (.cv c) (.cv e))
  have p0021 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWbr (.cv c) R (.cv e))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
              (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
          (synWbr (.cv c) R (.cv e))) (synWne (.cv c) (.cv e)))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWbr (.cv c) R (.cv e)) p0020 p0021
  have p0023 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWne (.cv c) (.cv e))
  have p0024 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
              (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
          (synWbr (.cv c) R (.cv e))) (synWne (.cv c) (.cv e)))
      (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e)) p0022 p0023
  have p0025 := @gStrictbr R e c
  have p0026 :=
    @gBiimpri (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e))) p0025
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
              (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
          (synWbr (.cv c) R (.cv e))) (synWne (.cv c) (.cv e)))
      (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) p0024 p0026
  have p0028 :=
    @gMtand
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWne (.cv c) (.cv e)) (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) p0019
      p0027
  have p0029 := @gId (synWne (.cv c) (.cv e))
  have p0030 := @gNecon1bi (synWne (.cv c) (.cv e)) (.cv c) (.cv e) p0029
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (.neg (synWne (.cv c) (.cv e))) (.classEq (.cv c) (.cv e)) p0028 p0030
  have p0032 :=
    @gBreq2d
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (.cv c) (.cv e) (.cv e) R p0031
  have p0033 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (synWbr (.cv c) R (.cv e)))
      (synWbr (.cv e) R (.cv c)) (synWbr (.cv e) R (.cv e)) p0016 p0032
  have p0034 :=
    @gEx
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWbr (.cv c) R (.cv e)) (synWbr (.cv e) R (.cv c)) p0033
  have p0035 :=
    @gIdd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWbr (.cv e) R (.cv c))
  have p0036 :=
    @gJaod
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWbr (.cv c) R (.cv e)) (synWbr (.cv e) R (.cv c)) (synWbr (.cv e) R (.cv c))
      p0034 p0035
  have p0037 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (synWo (synWbr (.cv c) R (.cv e)) (synWbr (.cv e) R (.cv c)))
      (synWbr (.cv e) R (.cv c)) p0007 p0036
  have p0038 :=
    @gEx
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))) (synWbr (.cv e) R (.cv c))
      p0037
  have p0039 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
  have p0040 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr (.cv e) R (.cv c))
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      p0039 p0040
  have p0043 := @gWppweantisym A R
  have p0044 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr R (synCwe) A) (synWbr R (synCantisym) A) p0001 p0043
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr R (synCantisym) A) p0041 p0044
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.classMem (.cv c) A) p0041 p0004
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.classMem (.cv e) A) p0041 p0005
  have p0056 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
  have p0058 :=
    @gBiimpi (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e))) p0025
  have p0059 := @gSimpl (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e))
  have p0060 :=
    @gSyl (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e)))
      (synWbr (.cv c) R (.cv e)) p0058 p0059
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) (synWbr (.cv c) R (.cv e)) p0056
      p0060
  have p0063 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr (.cv e) R (.cv c))
  have p0064 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
      (synWbr (.cv e) R (.cv c)) p0039 p0063
  have p0065 :=
    @gAntid
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      A R (.cv c) (.cv e) p0045 p0050 p0055 p0061 p0064
  have p0069 := @gSimpr (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e))
  have p0070 :=
    @gSyl (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e)))
      (synWne (.cv c) (.cv e)) p0058 p0069
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) (synWne (.cv c) (.cv e)) p0056
      p0070
  have p0072 :=
    @gPm221ddne
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))) (.cv c) (.cv e) p0065 p0071
  have p0073 :=
    @gPm201da
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (synWbr (.cv e) R (.cv c)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) p0072
  have p0074 :=
    @gEx
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (synWbr (.cv e) R (.cv c)) (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      p0073
  have p0075 :=
    @gImpbid
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))) (synWbr (.cv e) R (.cv c))
      p0038 p0074
  exact p0075

/-- Checked nominal proof certificate identified upstream as `g_wppstrictleastbridge`. -/
@[expose]
noncomputable def gWppstrictleastbridge (ph : Wff) (A : Class) (R : Class) (e : Var)
    (c : Var) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv)
    (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (synWb
          (synWral c A (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) (.neg ph)))
          (synWral c A (.imp ph (synWbr (.cv e) R (.cv c)))))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0002 : c ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_c, not_false_eq_true])
  have dv_cache_0003 : e ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_e, not_false_eq_true])
  have dv_cache_0004 : c ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_c, not_false_eq_true])
  have dv_cache_0005 : e ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_e, not_false_eq_true])
  have dv_cache_0006 : c ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show c ≠ e from (by exact dv_c_e))
  have dv_cache_0007 : c ∉ ((synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_R_c, dv_A_c, dv_c_e, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @gWppstrictcomplement A R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gImbi2d
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))) (synWbr (.cv e) R (.cv c))
      ph p0000
  have p0002 := @gCon2b (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) ph
  have p0003 := @gBiid (.imp ph (synWbr (.cv e) R (.cv c)))
  have p0004 :=
    @gN3bitr4g
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.imp ph (.neg (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (.imp ph (synWbr (.cv e) R (.cv c)))
      (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) (.neg ph))
      (.imp ph (synWbr (.cv e) R (.cv c))) p0001 p0002 p0003
  have p0005 :=
    @gRalbidva (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
      (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) (.neg ph))
      (.imp ph (synWbr (.cv e) R (.cv c))) c A dv_cache_0007 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fdminsepfpivred`. -/
@[expose]
noncomputable def gFdminsepfpivred (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv)
    (dv_D_e : e ∉ D.fv) (dv_R_e : e ∉ R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))) (synWb
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
          (.classMem (.cv e) (synCfpiv R A C D)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({ e } : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_e : c ≠ e := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0006 : e ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_e, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0008 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0009 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0010 : c ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_B, not_false_eq_true])
  have dv_cache_0011 : e ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_e, not_false_eq_true])
  have dv_cache_0012 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0013 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0014 : c ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0015 : e ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_e, not_false_eq_true])
  have dv_cache_0016 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0017 : c ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_D, not_false_eq_true])
  have dv_cache_0018 : e ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_e, not_false_eq_true])
  have dv_cache_0019 : c ∉ (R).fv :=
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
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0020 : e ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_e, not_false_eq_true])
  have dv_cache_0021 : c ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show c ≠ e from (by exact fresh_c_ne_e))
  have p0000 := @gSimpr (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))
  have p0001 :=
    @gFdminsepval0J A B C D R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0002 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (synWa (.classMem C B) (.classMem D B))
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
        (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (.neg
            (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
                (.classMem (.cv c) (synCsep2 C D)))))))
      p0000 p0001
  have p0003 := @gSimpl (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))
  have p0004 :=
    @gImnan (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (.classMem (.cv c) (synCsep2 C D))
  have p0005 :=
    @gRalbii
      (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.neg (.classMem (.cv c) (synCsep2 C D))))
      (.neg (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (.cv c) (synCsep2 C D))))
      c A p0004
  have p0006 :=
    @gRalnex
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.classMem (.cv c) (synCsep2 C D)))
      c A
  have p0007 :=
    @gBitri
      (synWral c A (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.neg (.classMem (.cv c) (synCsep2 C D)))))
      (synWral c A (.neg (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      (.neg (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      p0005 p0006
  have p0008 :=
    @gBicomi
      (synWral c A (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.neg (.classMem (.cv c) (synCsep2 C D)))))
      (.neg (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      p0007
  have p0009 :=
    @gA1i
      (synWb (.neg (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
              (.classMem (.cv c) (synCsep2 C D))))) (synWral c A
          (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.neg (.classMem (.cv c) (synCsep2 C D))))))
      (synWa (synWbr R (synCwe) A)
        (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))
      p0008
  have p0010 :=
    @gSimpl (synWbr R (synCwe) A)
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D)))
  have p0011 :=
    @gSimpr (synWbr R (synCwe) A)
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D)))
  have p0012 := @gSimpl (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))
  have p0013 :=
    @gSyl
      (synWa (synWbr R (synCwe) A)
        (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D)))
      (.classMem (.cv e) A) p0011 p0012
  have p0014 :=
    @gJca
      (synWa (synWbr R (synCwe) A)
        (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))
      (synWbr R (synCwe) A) (.classMem (.cv e) A) p0010 p0013
  have p0015 :=
    @gWppstrictleastbridge (.classMem (.cv c) (synCsep2 C D)) A R e c dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0016 :=
    @gSyl
      (synWa (synWbr R (synCwe) A)
        (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv e) A))
      (synWb (synWral c A (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.neg (.classMem (.cv c) (synCsep2 C D))))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c)))))
      p0014 p0015
  have p0017 :=
    @gBitrd
      (synWa (synWbr R (synCwe) A)
        (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))
      (.neg (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      (synWral c A (.imp (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.neg (.classMem (.cv c) (synCsep2 C D)))))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c))))
      p0009 p0016
  have p0018 :=
    @gPm532da (synWbr R (synCwe) A)
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D)))
      (.neg (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c))))
      p0017
  have p0019 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (synWbr R (synCwe) A)
      (synWb (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (.neg
            (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
                (.classMem (.cv c) (synCsep2 C D))))))
        (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (synWral c A
            (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c))))))
      p0003 p0018
  have p0020 :=
    @gBitrd (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
      (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (.neg
          (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
              (.classMem (.cv c) (synCsep2 C D))))))
      (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c)))))
      p0002 p0019
  have p0021 :=
    @gElfpiv A C D R e c dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0022 :=
    @gBicomi (.classMem (.cv e) (synCfpiv R A C D))
      (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c)))))
      p0021
  have p0023 :=
    @gA1i
      (synWb (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D)))
          (synWral c A (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c)))))
        (.classMem (.cv e) (synCfpiv R A C D)))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))) p0022
  have p0024 :=
    @gBitrd (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
      (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv e) R (.cv c)))))
      (.classMem (.cv e) (synCfpiv R A C D)) p0020 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_elfdminvalp`. -/
@[expose]
noncomputable def gElfdminvalp (A : Class) (B : Class) (C : Class) (R : Class) (d : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv)
    (dv_C_d : d ∉ C.fv) (dv_R_d : d ∉ R.fv)
    (hyp_elfdminvalp_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (.cv d) (synCfdminvalp R A B C)) (synWa (.classMem (.cv d) A)
          (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B)))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0005 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0007 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_d, not_false_eq_true])
  have dv_cache_0008 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_d, not_false_eq_true])
  have dv_cache_0009 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_d, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_d, not_false_eq_true])
  have p0000 :=
    @gFdminvalpss A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_elfdminvalp_1
  have p0001 := @gSseli (synCfdminvalp R A B C) A (.cv d) p0000
  have p0002 :=
    @gFdminvalpbr d A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0007
      dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010
      hyp_elfdminvalp_1
  have p0003 :=
    @gBiimpi (.classMem (.cv d) (synCfdminvalp R A B C))
      (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B)) p0002
  have p0004 :=
    @gJca (.classMem (.cv d) (synCfdminvalp R A B C)) (.classMem (.cv d) A)
      (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B)) p0001 p0003
  have p0005 :=
    @gSimpr (.classMem (.cv d) A)
      (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B))
  have p0007 :=
    @gBiimpri (.classMem (.cv d) (synCfdminvalp R A B C))
      (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B)) p0002
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv d) A)
        (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B)))
      (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B))
      (.classMem (.cv d) (synCfdminvalp R A B C)) p0005 p0007
  have p0009 :=
    @gImpbii (.classMem (.cv d) (synCfdminvalp R A B C))
      (synWa (.classMem (.cv d) A)
        (.classMem (synCopk (synCsn (.cv d)) C) (synCfdminsep R A B)))
      p0004 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdminvalpfpivred`. -/
@[expose]
noncomputable def gFdminvalpfpivred (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
        (.classEq (synCfdminvalp R A B (synCopk C D)) (synCfpiv R A C D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let c : Var := freshVar proofSupport 1
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d_ne_c : d ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((synCopk C D)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((synCopk C D)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (A).fv (C).fv from (by exact dv_A_C)),
                  (show Disjoint (A).fv (D).fv from (by exact dv_A_D))⟩))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv ((synCopk C D)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (B).fv (C).fv from (by exact dv_B_C)),
                  (show Disjoint (B).fv (D).fv from (by exact dv_B_D))⟩))))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint ((synCopk C D)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((synCopk C D)).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint (((C).fv) ∪ ((D).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (C).fv (R).fv from (by exact dv_C_R)),
                  (show Disjoint (D).fv (R).fv from (by exact dv_D_R))⟩))))
  have dv_cache_0009 : d ∉ ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_d_not_C, fresh_d_not_D, or_false, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0012 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0013 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0014 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0015 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0016 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0017 : d ∉ (C).fv :=
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
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0018 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0019 : d ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have dv_cache_0020 : c ∉ (A).fv :=
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
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0021 : c ∉ (C).fv :=
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
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0022 : c ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_D, not_false_eq_true])
  have dv_cache_0023 : c ∉ (R).fv :=
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
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0024 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0025 : d ∉ ((synCfdminvalp R A B (synCopk C D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_d_not_A, fresh_d_not_B, fresh_d_not_C, fresh_d_not_D, fresh_d_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((synCfpiv R A C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_C, fresh_d_not_D, fresh_d_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0027 :
    d ∉ ((synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_d_not_R,
          fresh_d_not_A, fresh_d_not_C, fresh_d_not_B, fresh_d_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gOpkex C D
  have p0001 :=
    @gElfdminvalp A B (synCopk C D) R d dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (.cv d) (synCfdminvalp R A B (synCopk C D)))
        (synWa (.classMem (.cv d) A)
          (.classMem (synCopk (synCsn (.cv d)) (synCopk C D)) (synCfdminsep R A B))))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))) p0001
  have p0003 :=
    @gFdminsepfpivred A B C D R d dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0003
      dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0007 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0010
  have p0004 :=
    @gAnbi2d (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCopk (synCsn (.cv d)) (synCopk C D)) (synCfdminsep R A B))
      (.classMem (.cv d) (synCfpiv R A C D)) (.classMem (.cv d) A) p0003
  have p0005 :=
    @gBitrd (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (.cv d) (synCfdminvalp R A B (synCopk C D)))
      (synWa (.classMem (.cv d) A)
        (.classMem (synCopk (synCsn (.cv d)) (synCopk C D)) (synCfdminsep R A B)))
      (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCfpiv R A C D))) p0002 p0004
  have p0006 := @gSimpr (.classMem (.cv d) A) (.classMem (.cv d) (synCfpiv R A C D))
  have p0007 :=
    @gElfpiv A C D R d c dv_cache_0011 dv_cache_0012 dv_cache_0003 dv_cache_0020
      dv_cache_0004 dv_cache_0015 dv_cache_0016 dv_cache_0021 dv_cache_0017 dv_cache_0018
      dv_cache_0022 dv_cache_0019 dv_cache_0023 dv_cache_0010 dv_cache_0024
  have p0008 :=
    @gBiimpi (.classMem (.cv d) (synCfpiv R A C D))
      (synWa (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 C D))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv d) R (.cv c)))))
      p0007
  have p0009 :=
    @gSimpll (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 C D))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv d) R (.cv c))))
  have p0010 :=
    @gSyl (.classMem (.cv d) (synCfpiv R A C D))
      (synWa (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 C D))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 C D)) (synWbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) A) p0008 p0009
  have p0011 := @gId (.classMem (.cv d) (synCfpiv R A C D))
  have p0012 :=
    @gJca (.classMem (.cv d) (synCfpiv R A C D)) (.classMem (.cv d) A)
      (.classMem (.cv d) (synCfpiv R A C D)) p0010 p0011
  have p0013 :=
    @gImpbii (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCfpiv R A C D)))
      (.classMem (.cv d) (synCfpiv R A C D)) p0006 p0012
  have p0014 :=
    @gA1i
      (synWb (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCfpiv R A C D)))
        (.classMem (.cv d) (synCfpiv R A C D)))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))) p0013
  have p0015 :=
    @gBitrd (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (.cv d) (synCfdminvalp R A B (synCopk C D)))
      (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCfpiv R A C D)))
      (.classMem (.cv d) (synCfpiv R A C D)) p0005 p0014
  have p0016 :=
    @gEqrdv (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))) d
      (synCfdminvalp R A B (synCopk C D)) (synCfpiv R A C D) dv_cache_0025
      dv_cache_0026 dv_cache_0027 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_fdminvalpeq4`. -/
@[expose]
noncomputable def gFdminvalpeq4 (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (_dv_A_R : Disjoint A.fv R.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (_dv_C_R : Disjoint C.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq C D) (.classEq (synCfdminvalp R A B C) (synCfdminvalp R A B D))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdminvalp R A B C))
  have p0001 :=
    @gA1i
      (.classEq (synCfdminvalp R A B C)
        (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))))
      (.classEq C D) p0000
  have p0002 :=
    (Nominal.classEqRefl (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))))
  have p0003 :=
    @gA1i
      (.classEq (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))) (synCuni
          (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)) (synC1c))))
      (.classEq C D) p0002
  have p0004 := @gSneq C D
  have p0005 :=
    @gImakeq2d (.classEq C D) (synCsn C) (synCsn D) (synCcnvk (synCfdminsep R A B))
      p0004
  have p0006 :=
    @gIneq1d (.classEq C D) (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))
      (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D)) (synC1c) p0005
  have p0007 :=
    @gUnieqd (.classEq C D)
      (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)) (synC1c))
      (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D)) (synC1c)) p0006
  have p0008 :=
    @gEqtrd (.classEq C D)
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)))
      (synCuni (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)) (synC1c)))
      (synCuni (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D)) (synC1c)))
      p0003 p0007
  have p0009 :=
    (Nominal.classEqRefl (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D))))
  have p0010 :=
    @gA1i
      (.classEq (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D))) (synCuni
          (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D)) (synC1c))))
      (.classEq C D) p0009
  have p0011 :=
    @gEqtr4d (.classEq C D)
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)))
      (synCuni (synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D)) (synC1c)))
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D))) p0008 p0010
  have p0012 :=
    @gEqtrd (.classEq C D) (synCfdminvalp R A B C)
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)))
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D))) p0001 p0011
  have p0013 := (Nominal.classEqRefl (synCfdminvalp R A B D))
  have p0014 :=
    @gA1i
      (.classEq (synCfdminvalp R A B D)
        (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D))))
      (.classEq C D) p0013
  have p0015 :=
    @gEqtr4d (.classEq C D) (synCfdminvalp R A B C)
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn D)))
      (synCfdminvalp R A B D) p0012 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fdpivinrange`. -/
@[expose]
noncomputable def gFdpivinrange (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_fdpivinrange_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivinrange_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivinrange_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
        (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_d_ne_p : d ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_d : p ≠ d := Ne.symm fresh_d_ne_p
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0008 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0010 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0011 : Disjoint (A).fv ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv ((synCopk C D)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (A).fv (C).fv from (by exact dv_A_C)),
                  (show Disjoint (A).fv (D).fv from (by exact dv_A_D))⟩))))
  have dv_cache_0012 : Disjoint (B).fv ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (B).fv ((synCopk C D)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (B).fv (C).fv from (by exact dv_B_C)),
                  (show Disjoint (B).fv (D).fv from (by exact dv_B_D))⟩))))
  have dv_cache_0013 : Disjoint ((synCopk C D)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint ((synCopk C D)).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint (((C).fv) ∪ ((D).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (C).fv (R).fv from (by exact dv_C_R)),
                  (show Disjoint (D).fv (R).fv from (by exact dv_D_R))⟩))))
  have dv_cache_0014 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0015 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0016 : Disjoint ((Class.cv p)).fv ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint ((Class.cv p)).fv ((synCopk C D)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint (({ p } : Finset Var)) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ p } : Finset Var)) ((C).fv) from
                    (Finset.disjoint_singleton_left.mpr
                      (show p ∉ (C).fv from (by exact fresh_p_not_C)))),
                  (show Disjoint (({ p } : Finset Var)) ((D).fv) from
                    (Finset.disjoint_singleton_left.mpr
                      (show p ∉ (D).fv from (by exact fresh_p_not_D))))⟩))))
  have dv_cache_0017 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0018 : p ∉ ((synCopk C D)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_p_not_C, fresh_p_not_D, or_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_p_not_B, or_false, not_false_eq_true])
  have dv_cache_0020 :
    p ∉ ((Wff.classEq (synCfdminvalp R A B (synCopk C D)) (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_A, fresh_p_not_B, fresh_p_not_C,
          fresh_p_not_D, fresh_p_not_R, fresh_p_ne_d, or_false, not_false_eq_true])
  have dv_cache_0021 : Disjoint (A).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint (A).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (A).fv from (by exact fresh_d_not_A))))))
  have dv_cache_0022 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0023 : Disjoint (B).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (show Disjoint (B).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (B).fv from (by exact fresh_d_not_B))))))
  have dv_cache_0024 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0025 : Disjoint ((Class.cv d)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (show Disjoint ((Class.cv d)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ d } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show d ∉ (R).fv from (by exact fresh_d_not_R))))))
  have dv_cache_0026 : p ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_d, not_false_eq_true])
  have dv_cache_0027 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0028 : d ∉ ((synCfpiv R A C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_C, fresh_d_not_D, fresh_d_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0029 :
    d ∉
      ((Wff.imp (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
          (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_d_not_R, fresh_d_not_A, fresh_d_not_C, fresh_d_not_B,
          fresh_d_not_D, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gFdminvalpfpivred A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @gFdminvalpex A B (synCopk C D) R dv_cache_0001 dv_cache_0011 dv_cache_0004
      dv_cache_0012 dv_cache_0007 dv_cache_0013 hyp_fdpivinrange_1 hyp_fdpivinrange_2
      hyp_fdpivinrange_3
  have p0002 :=
    @gA1i (.classMem (synCfdminvalp R A B (synCopk C D)) (synCvv))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))) p0001
  have p0003 :=
    @gEqeltrrd (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (synCfdminvalp R A B (synCopk C D)) (synCfpiv R A C D) (synCvv) p0000 p0002
  have p0004 :=
    @gSimpr (.classEq (.cv d) (synCfpiv R A C D))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
  have p0005 := @gSimpr (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))
  have p0006 := @gId (synWa (.classMem C B) (.classMem D B))
  have p0007 := @gSimpl (.classMem C B) (.classMem D B)
  have p0008 := @gElex C B
  have p0009 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem C B)
      (.classMem C (synCvv)) p0007 p0008
  have p0010 := @gSimpr (.classMem C B) (.classMem D B)
  have p0011 := @gElex D B
  have p0012 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem D B)
      (.classMem D (synCvv)) p0010 p0011
  have p0013 :=
    @gJca (synWa (.classMem C B) (.classMem D B)) (.classMem C (synCvv))
      (.classMem D (synCvv)) p0009 p0012
  have p0014 := @gOpkelxpkg C D B B (synCvv) (synCvv)
  have p0015 :=
    @gSyl (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWb (.classMem (synCopk C D) (synCxpk B B))
        (synWa (.classMem C B) (.classMem D B)))
      p0013 p0014
  have p0016 :=
    @gMpbird (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk C D) (synCxpk B B)) (synWa (.classMem C B) (.classMem D B))
      p0006 p0015
  have p0017 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (synWa (.classMem C B) (.classMem D B)) (.classMem (synCopk C D) (synCxpk B B))
      p0005 p0016
  have p0018 :=
    @gSyl
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCopk C D) (synCxpk B B)) p0004 p0017
  have p0021 :=
    @gSyl
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classEq (synCfdminvalp R A B (synCopk C D)) (synCfpiv R A C D)) p0004 p0000
  have p0022 :=
    @gSimpl (.classEq (.cv d) (synCfpiv R A C D))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
  have p0023 :=
    @gEqcomd
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (.cv d) (synCfpiv R A C D) p0022
  have p0024 :=
    @gEqtrd
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (synCfdminvalp R A B (synCopk C D)) (synCfpiv R A C D) (.cv d) p0021 p0023
  have p0025 :=
    @gJca
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (.classMem (synCopk C D) (synCxpk B B))
      (.classEq (synCfdminvalp R A B (synCopk C D)) (.cv d)) p0018 p0024
  have p0026 :=
    @gFdminvalpeq4 A B (.cv p) (synCopk C D) R dv_cache_0001 dv_cache_0014 dv_cache_0011
      dv_cache_0004 dv_cache_0015 dv_cache_0012 dv_cache_0007 dv_cache_0016 dv_cache_0017
      dv_cache_0013
  have p0027 :=
    @gEqeq1d (.classEq (.cv p) (synCopk C D)) (synCfdminvalp R A B (.cv p))
      (synCfdminvalp R A B (synCopk C D)) (.cv d) p0026
  have p0028 :=
    @gRspcev (.classEq (synCfdminvalp R A B (.cv p)) (.cv d))
      (.classEq (synCfdminvalp R A B (synCopk C D)) (.cv d)) p (synCopk C D)
      (synCxpk B B) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0027
  have p0029 :=
    @gSyl
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (synWa (.classMem (synCopk C D) (synCxpk B B))
        (.classEq (synCfdminvalp R A B (synCopk C D)) (.cv d)))
      (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) (.cv d))) p0025
      p0028
  have p0030 :=
    @gFdpivrange2br A B (.cv d) R p dv_cache_0001 dv_cache_0021 dv_cache_0004
      dv_cache_0022 dv_cache_0023 dv_cache_0007 dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 hyp_fdpivinrange_1 hyp_fdpivinrange_2 hyp_fdpivinrange_3
  have p0031 :=
    @gSylibr
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) (.cv d)))
      (.classMem (.cv d) (synCfdpivrange2 R A B)) p0029 p0030
  have p0033 :=
    @gEleq1d
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (.cv d) (synCfpiv R A C D) (synCfdpivrange2 R A B) p0022
  have p0034 :=
    @gMpbid
      (synWa (.classEq (.cv d) (synCfpiv R A C D))
        (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B))))
      (.classMem (.cv d) (synCfdpivrange2 R A B))
      (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B)) p0031 p0033
  have p0035 :=
    @gEx (.classEq (.cv d) (synCfpiv R A C D))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B)) p0034
  have p0036 :=
    @gVtocleg
      (.imp (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
        (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B)))
      d (synCfpiv R A C D) (synCvv) dv_cache_0028 dv_cache_0029 p0035
  have p0037 :=
    @gSyl (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCfpiv R A C D) (synCvv))
      (.imp (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
        (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B)))
      p0003 p0036
  have p0038 :=
    @gPm243i (synWa (synWbr R (synCwe) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (synCfpiv R A C D) (synCfdpivrange2 R A B)) p0037
  exact p0038


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elfdif`. -/
@[expose]
noncomputable def gElfdif (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (_dv_A_e : e ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_B_e : e ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (_dv_R_e : e ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_e_x : e ≠ x) (dv_e_y : e ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem (.cv e) (synCfdif R A B)) (synWa (.classMem (.cv e) A) (synWrex x B
            (synWrex y B (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪
      ({ e } : Finset Var)
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_ne_e : d ≠ e := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0013 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0014 : d ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0016 : y ∉ ((Wff.classEq (.cv d) (.cv e))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_d, (Ne.symm dv_e_y), or_false,
          not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.classEq (.cv d) (.cv e))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_d, (Ne.symm dv_e_x), or_false,
          not_false_eq_true])
  have dv_cache_0018 : d ∉ ((Class.cv e)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_e, not_false_eq_true])
  have dv_cache_0019 :
    d ∉
      ((synWrex x B (synWrex y B (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfpiv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_d_not_B, fresh_d_ne_e,
          fresh_d_not_A, fresh_d_ne_x, fresh_d_ne_y, fresh_d_not_R, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdif x y A B R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @gEleq2i (synCfdif R A B)
      (synCrab d A
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      (.cv e) p0000
  have p0002 := @gEleq1 (.cv d) (.cv e) (synCfpiv R A (.cv x) (.cv y))
  have p0003 :=
    @gRexbidv (.classEq (.cv d) (.cv e))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))) y B dv_cache_0016 p0002
  have p0004 :=
    @gRexbidv (.classEq (.cv d) (.cv e))
      (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))
      (synWrex y B (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y)))) x B dv_cache_0017
      p0003
  have p0005 :=
    @gElrab
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))
      (synWrex x B (synWrex y B (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))))) d
      (.cv e) A dv_cache_0018 dv_cache_0003 dv_cache_0019 p0004
  have p0006 :=
    @gBitri (.classMem (.cv e) (synCfdif R A B))
      (.classMem (.cv e) (synCrab d A (synWrex x B
            (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))))
      (synWa (.classMem (.cv e) A)
        (synWrex x B (synWrex y B (.classMem (.cv e) (synCfpiv R A (.cv x) (.cv y))))))
      p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fdifssunirange2x`. -/
@[expose]
noncomputable def gFdifssunirange2x (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdifssunirange2x_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdifssunirange2x_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdifssunirange2x_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A)
        (synWss (synCfdif R A B) (synCuni (synCfdpivrange2 R A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0013 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0014 : d ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0016 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0017 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0018 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0019 : Disjoint (B).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (show Disjoint (B).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (B).fv from (by exact fresh_y_not_B))))))
  have dv_cache_0020 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)];
          exact
            (show Disjoint (({ x } : Finset Var)) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ ({ y } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show x ≠ y from (by exact fresh_x_ne_y))))))))
  have dv_cache_0021 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0022 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0023 :
    x ∉ ((Wff.classMem (.cv d) (synCuni (synCfdpivrange2 R A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_d, fresh_x_not_A,
          fresh_x_not_B, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0024 :
    y ∉ ((Wff.classMem (.cv d) (synCuni (synCfdpivrange2 R A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, Finset.mem_singleton, fresh_y_ne_d, fresh_y_not_A,
          fresh_y_not_B, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((synWbr R (synCwe) A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0026 : y ∉ ((synWbr R (synCwe) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0027 : d ∉ ((synCfdif R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0028 : d ∉ ((synCuni (synCfdpivrange2 R A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0029 : d ∉ ((synWbr R (synCwe) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_d_not_R, fresh_d_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gElfdif x y A B R d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @gBiimpi (.classMem (.cv d) (synCfdif R A B))
      (synWa (.classMem (.cv d) A)
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      p0000
  have p0002 :=
    @gSimpr (.classMem (.cv d) A)
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))
  have p0003 :=
    @gSyl (.classMem (.cv d) (synCfdif R A B))
      (synWa (.classMem (.cv d) A)
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))
      p0001 p0002
  have p0004 :=
    @gA1i
      (.imp (.classMem (.cv d) (synCfdif R A B))
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      (synWbr R (synCwe) A) p0003
  have p0005 :=
    @gFdpivinrange A B (.cv x) (.cv y) R dv_cache_0001 dv_cache_0016 dv_cache_0017
      dv_cache_0002 dv_cache_0018 dv_cache_0019 dv_cache_0006 dv_cache_0020 dv_cache_0021
      dv_cache_0022 hyp_fdifssunirange2x_1 hyp_fdifssunirange2x_2 hyp_fdifssunirange2x_3
  have p0006 := @gElunii (.cv d) (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A B)
  have p0007 :=
    @gSylan2
      (synWa (synWbr R (synCwe) A) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (synCfpiv R A (.cv x) (.cv y)) (synCfdpivrange2 R A B))
      (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B))) p0005 p0006
  have p0008 :=
    @gEx (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B))) p0007
  have p0009 :=
    @gCom12 (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B))) p0008
  have p0010 :=
    @gRexlimdvva (synWbr R (synCwe) A)
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B))) x y B B dv_cache_0009
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0015 p0009
  have p0011 :=
    @gSyld (synWbr R (synCwe) A) (.classMem (.cv d) (synCfdif R A B))
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))
      (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B))) p0004 p0010
  have p0012 :=
    @gSsrdv (synWbr R (synCwe) A) d (synCfdif R A B)
      (synCuni (synCfdpivrange2 R A B)) dv_cache_0027 dv_cache_0028 dv_cache_0029 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_unirange2ssfdifx`. -/
@[expose]
noncomputable def gUnirange2ssfdifx (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_unirange2ssfdifx_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_unirange2ssfdifx_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_unirange2ssfdifx_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A)
        (synWss (synCuni (synCfdpivrange2 R A B)) (synCfdif R A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d_ne_q : d ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_d : q ≠ d := Ne.symm fresh_d_ne_q
  have fresh_d_ne_p : d ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_d : p ≠ d := Ne.symm fresh_d_ne_p
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_d_ne_c : d ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have fresh_q_ne_p : q ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have fresh_q_ne_x : q ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_q : y ≠ q := Ne.symm fresh_q_ne_y
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
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have dv_cache_0001 : q ∉ ((Class.cv d)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_d, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCfdpivrange2 R A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0003 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0004 : Disjoint (A).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (A).fv from (by exact fresh_q_not_A))))))
  have dv_cache_0005 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0006 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (B).fv from (by exact fresh_q_not_B))))))
  have dv_cache_0008 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0009 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0010 : Disjoint ((Class.cv q)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv q)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ q } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show q ∉ (R).fv from (by exact fresh_q_not_R))))))
  have dv_cache_0011 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0012 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv p)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_p, not_false_eq_true])
  have dv_cache_0015 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0016 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0017 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0019 : Disjoint (A).fv ((synCopk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (show Disjoint (A).fv ((synCopk (.cv x) (.cv y))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (A).fv from (by exact fresh_x_not_A)))))),
                  (show Disjoint ((A).fv) (((Class.cv y)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ y } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show y ∉ (A).fv from (by exact fresh_y_not_A))))))⟩))))
  have dv_cache_0020 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0021 : Disjoint (B).fv ((synCopk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint (B).fv ((synCopk (.cv x) (.cv y))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((B).fv) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show x ∉ (B).fv from (by exact fresh_x_not_B)))))),
                  (show Disjoint ((B).fv) (((Class.cv y)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((B).fv) (({ y } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show y ∉ (B).fv from (by exact fresh_y_not_B))))))⟩))))
  have dv_cache_0022 : Disjoint ((Class.cv p)).fv ((synCopk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (show Disjoint ((Class.cv p)).fv ((synCopk (.cv x) (.cv y))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show
              Disjoint (({ p } : Finset Var)) ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ p } : Finset Var)) (((Class.cv x)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ x } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ x } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ x from (by exact fresh_p_ne_x)))))))),
                  (show Disjoint (({ p } : Finset Var)) (((Class.cv y)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) (({ y } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ ({ y } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show p ≠ y from (by exact fresh_p_ne_y))))))))⟩))))
  have dv_cache_0023 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0024 : Disjoint ((synCopk (.cv x) (.cv y))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (show Disjoint ((synCopk (.cv x) (.cv y))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((((Class.cv x)).fv) ∪ (((Class.cv y)).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((Class.cv x)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ (R).fv from (by exact fresh_x_not_R)))))),
                  (show Disjoint (((Class.cv y)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ (R).fv from (by exact fresh_y_not_R))))))⟩))))
  have dv_cache_0025 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0026 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0027 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0028 : Disjoint (B).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (show Disjoint (B).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (B).fv from (by exact fresh_y_not_B))))))
  have dv_cache_0029 : Disjoint ((Class.cv x)).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (show Disjoint ((Class.cv x)).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (x),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (y)];
          exact
            (show Disjoint (({ x } : Finset Var)) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ ({ y } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show x ≠ y from (by exact fresh_x_ne_y))))))))
  have dv_cache_0030 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0031 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0032 :
    y ∉
      ((synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          Finset.mem_union, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A,
          fresh_y_ne_d, fresh_y_ne_q, fresh_y_ne_p, fresh_y_not_B, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0033 :
    x ∉
      ((synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A,
          fresh_x_ne_d, fresh_x_ne_q, fresh_x_ne_p, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0034 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0035 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0036 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0037 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0038 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0039 : d ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_y, not_false_eq_true])
  have dv_cache_0040 : c ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_R, not_false_eq_true])
  have dv_cache_0041 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0042 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0043 : x ∉ ((Wff.classMem (.cv d) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_d, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0044 : y ∉ ((Wff.classMem (.cv d) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_d, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0045 :
    y ∉
      ((synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          Finset.mem_union, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_A,
          fresh_y_ne_d, fresh_y_ne_q, fresh_y_ne_p, fresh_y_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0046 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0047 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0048 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0049 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0050 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0051 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0052 : d ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0053 : p ∉ ((Wff.classMem (.cv d) (synCfdif R A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_d, fresh_p_not_A, fresh_p_not_B, fresh_p_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0054 :
    p ∉ ((synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_R, fresh_p_not_A, fresh_p_ne_d, fresh_p_ne_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0055 : q ∉ ((Wff.classMem (.cv d) (synCfdif R A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_d, fresh_q_not_A, fresh_q_not_B, fresh_q_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0056 : q ∉ ((synWbr R (synCwe) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0057 : d ∉ ((synCuni (synCfdpivrange2 R A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0058 : d ∉ ((synCfdif R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0059 : d ∉ ((synWbr R (synCwe) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_d_not_R, fresh_d_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gEluni2 q (.cv d) (synCfdpivrange2 R A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B)))
      (synWrex q (synCfdpivrange2 R A B) (.classMem (.cv d) (.cv q))) p0000
  have p0002 :=
    @gA1i
      (.imp (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B)))
        (synWrex q (synCfdpivrange2 R A B) (.classMem (.cv d) (.cv q))))
      (synWbr R (synCwe) A) p0001
  have p0003 :=
    @gFdpivrange2br A B (.cv q) R p dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 hyp_unirange2ssfdifx_1 hyp_unirange2ssfdifx_2 hyp_unirange2ssfdifx_3
  have p0004 :=
    @gBiimpi (.classMem (.cv q) (synCfdpivrange2 R A B))
      (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) p0003
  have p0005 :=
    @gA1i
      (.imp (.classMem (.cv q) (synCfdpivrange2 R A B))
        (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))) p0004
  have p0006 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (synCxpk B B)))
      (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))
  have p0007 :=
    @gSimpr (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv p) (synCxpk B B))
  have p0008 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (synCxpk B B)))
      (.classMem (.cv p) (synCxpk B B)) p0006 p0007
  have p0009 :=
    @gElxpk2 x y (.cv p) B B dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0010 :=
    @gBiimpi (.classMem (.cv p) (synCxpk B B))
      (synWrex x B (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y))))) p0009
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv p) (synCxpk B B))
      (synWrex x B (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y))))) p0008
      p0010
  have p0012 :=
    @gSimpl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (.cv p) (synCopk (.cv x) (.cv y)))
  have p0013 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classMem (.cv y) B)
  have p0014 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv x) B)
  have p0015 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      p0013 p0014
  have p0017 :=
    @gSimpl (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv p) (synCxpk B B))
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (synCxpk B B)))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))) p0006 p0017
  have p0019 := @gSimpr (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv d) (.cv q)) p0018 p0019
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv d) (.cv q)) p0015 p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classMem (.cv d) (.cv q)) p0012 p0021
  have p0027 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (synCxpk B B)))
      (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)) p0015 p0027
  have p0029 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)) p0012 p0028
  have p0030 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (synCfdminvalp R A B (.cv p)) (.cv q) p0029
  have p0031 :=
    @gSimpr
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (.cv p) (synCopk (.cv x) (.cv y)))
  have p0032 :=
    @gFdminvalpeq4 A B (.cv p) (synCopk (.cv x) (.cv y)) R dv_cache_0003 dv_cache_0018
      dv_cache_0019 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0008 dv_cache_0022
      dv_cache_0023 dv_cache_0024
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (.classEq (.cv p) (synCopk (.cv x) (.cv y)))
      (.classEq (synCfdminvalp R A B (.cv p))
        (synCfdminvalp R A B (synCopk (.cv x) (.cv y))))
      p0031 p0032
  have p0034 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (.cv q) (synCfdminvalp R A B (.cv p))
      (synCfdminvalp R A B (synCopk (.cv x) (.cv y))) p0030 p0033
  have p0042 := @gSimpl (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))
  have p0043 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))) (synWbr R (synCwe) A)
      p0018 p0042
  have p0044 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWbr R (synCwe) A) p0015 p0043
  have p0046 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv x) B)
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classMem (.cv x) B) p0013 p0046
  have p0048 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classMem (.cv y) B)
  have p0049 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0047 p0048
  have p0050 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWbr R (synCwe) A) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0044
      p0049
  have p0051 :=
    @gFdminvalpfpivred A B (.cv x) (.cv y) R dv_cache_0003 dv_cache_0025 dv_cache_0026
      dv_cache_0005 dv_cache_0027 dv_cache_0028 dv_cache_0008 dv_cache_0029 dv_cache_0030
      dv_cache_0031
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (synWa (synWbr R (synCwe) A) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classEq (synCfdminvalp R A B (synCopk (.cv x) (.cv y)))
        (synCfpiv R A (.cv x) (.cv y)))
      p0050 p0051
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (synCfdminvalp R A B (synCopk (.cv x) (.cv y)))
        (synCfpiv R A (.cv x) (.cv y)))
      p0012 p0052
  have p0054 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (.cv q) (synCfdminvalp R A B (synCopk (.cv x) (.cv y)))
      (synCfpiv R A (.cv x) (.cv y)) p0034 p0053
  have p0055 :=
    @gEleqtrd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (synCxpk B B)))
              (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (.cv d) (.cv q) (synCfpiv R A (.cv x) (.cv y)) p0022 p0054
  have p0056 :=
    @gEx
      (synWa (synWa (synWa
            (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (synCxpk B B)))
            (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (.cv p) (synCopk (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) p0055
  have p0057 :=
    @gReximdva
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classEq (.cv p) (synCopk (.cv x) (.cv y)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) y B dv_cache_0032 p0056
  have p0058 :=
    @gReximdva
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y))))
      (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))) x B dv_cache_0033
      p0057
  have p0059 :=
    @gElfpiv A (.cv x) (.cv y) R d c dv_cache_0025 dv_cache_0026 dv_cache_0005
      dv_cache_0034 dv_cache_0035 dv_cache_0029 dv_cache_0030 dv_cache_0036 dv_cache_0037
      dv_cache_0031 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
  have p0060 :=
    @gBiimpi (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))))
        (synWral c A (.imp (.classMem (.cv c) (synCsep2 (.cv x) (.cv y)))
            (synWbr (.cv d) R (.cv c)))))
      p0059
  have p0061 :=
    @gSimpll (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y)))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 (.cv x) (.cv y)))
          (synWbr (.cv d) R (.cv c))))
  have p0062 :=
    @gSyl (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv d) A) (.classMem (.cv d) (synCsep2 (.cv x) (.cv y))))
        (synWral c A (.imp (.classMem (.cv c) (synCsep2 (.cv x) (.cv y)))
            (synWbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) A) p0060 p0061
  have p0063 :=
    @gA1i
      (.imp (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A))
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (synCxpk B B)))
          (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      p0062
  have p0064 :=
    @gRexlimdvva
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A) x y B B
      dv_cache_0016 dv_cache_0043 dv_cache_0044 dv_cache_0033 dv_cache_0045 dv_cache_0017
      p0063
  have p0065 :=
    @gSyld
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWrex x B (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y)))))
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))
      (.classMem (.cv d) A) p0058 p0064
  have p0113 :=
    @gJcad
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWrex x B (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y)))))
      (.classMem (.cv d) A)
      (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y)))))
      p0065 p0058
  have p0114 :=
    @gElfdif x y A B R d dv_cache_0003 dv_cache_0005 dv_cache_0035 dv_cache_0046
      dv_cache_0047 dv_cache_0008 dv_cache_0048 dv_cache_0015 dv_cache_0016 dv_cache_0041
      dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0017
  have p0115 :=
    @gBiimpri (.classMem (.cv d) (synCfdif R A B))
      (synWa (.classMem (.cv d) A)
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      p0114
  have p0116 :=
    @gSyl6
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWrex x B (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y)))))
      (synWa (.classMem (.cv d) A)
        (synWrex x B (synWrex y B (.classMem (.cv d) (synCfpiv R A (.cv x) (.cv y))))))
      (.classMem (.cv d) (synCfdif R A B)) p0113 p0115
  have p0117 :=
    @gMpd
      (synWa (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (synCxpk B B))) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (synWrex x B (synWrex y B (.classEq (.cv p) (synCopk (.cv x) (.cv y)))))
      (.classMem (.cv d) (synCfdif R A B)) p0011 p0116
  have p0118 :=
    @gEx
      (synWa (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (synCxpk B B)))
      (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))
      (.classMem (.cv d) (synCfdif R A B)) p0117
  have p0119 :=
    @gRexlimdva (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
      (.classEq (synCfdminvalp R A B (.cv p)) (.cv q))
      (.classMem (.cv d) (synCfdif R A B)) p (synCxpk B B) dv_cache_0053 dv_cache_0054
      p0118
  have p0120 :=
    @gSyld (synWa (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv q) (synCfdpivrange2 R A B))
      (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv d) (synCfdif R A B)) p0005 p0119
  have p0121 :=
    @gEx (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))
      (.imp (.classMem (.cv q) (synCfdpivrange2 R A B)) (.classMem (.cv d) (synCfdif R A B)))
      p0120
  have p0122 :=
    @gCom23 (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))
      (.classMem (.cv q) (synCfdpivrange2 R A B)) (.classMem (.cv d) (synCfdif R A B))
      p0121
  have p0123 :=
    @gRexlimdv (synWbr R (synCwe) A) (.classMem (.cv d) (.cv q))
      (.classMem (.cv d) (synCfdif R A B)) q (synCfdpivrange2 R A B) dv_cache_0055
      dv_cache_0056 p0122
  have p0124 :=
    @gSyld (synWbr R (synCwe) A)
      (.classMem (.cv d) (synCuni (synCfdpivrange2 R A B)))
      (synWrex q (synCfdpivrange2 R A B) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv d) (synCfdif R A B)) p0002 p0123
  have p0125 :=
    @gSsrdv (synWbr R (synCwe) A) d (synCuni (synCfdpivrange2 R A B))
      (synCfdif R A B) dv_cache_0057 dv_cache_0058 dv_cache_0059 p0124
  exact p0125


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdifequnirange2x`. -/
@[expose]
noncomputable def gFdifequnirange2x (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdifequnirange2x_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdifequnirange2x_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdifequnirange2x_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A)
        (.classEq (synCfdif R A B) (synCuni (synCfdpivrange2 R A B)))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 :=
    @gFdifssunirange2x A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdifequnirange2x_1 hyp_fdifequnirange2x_2 hyp_fdifequnirange2x_3
  have p0001 :=
    @gUnirange2ssfdifx A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdifequnirange2x_1 hyp_fdifequnirange2x_2 hyp_fdifequnirange2x_3
  have p0002 :=
    @gJca (synWbr R (synCwe) A)
      (synWss (synCfdif R A B) (synCuni (synCfdpivrange2 R A B)))
      (synWss (synCuni (synCfdpivrange2 R A B)) (synCfdif R A B)) p0000 p0001
  have p0003 := @gEqss (synCfdif R A B) (synCuni (synCfdpivrange2 R A B))
  have p0004 :=
    @gSylibr (synWbr R (synCwe) A)
      (synWa (synWss (synCfdif R A B) (synCuni (synCfdpivrange2 R A B)))
        (synWss (synCuni (synCfdpivrange2 R A B)) (synCfdif R A B)))
      (.classEq (synCfdif R A B) (synCuni (synCfdpivrange2 R A B))) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fdifex2`. -/
@[expose]
noncomputable def gFdifex2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv) (hyp_fdifex2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdifex2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdifex2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.imp (synWbr R (synCwe) A) (.classMem (synCfdif R A B) (synCvv))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 :=
    @gFdifequnirange2x A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdifex2_1
      hyp_fdifex2_2 hyp_fdifex2_3
  have p0001 :=
    @gFdpivrange2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdifex2_1
      hyp_fdifex2_2 hyp_fdifex2_3
  have p0002 := @gUniex (synCfdpivrange2 R A B) p0001
  have p0003 :=
    @gA1i (.classMem (synCuni (synCfdpivrange2 R A B)) (synCvv))
      (synWbr R (synCwe) A) p0002
  have p0004 :=
    @gEqeltrd (synWbr R (synCwe) A) (synCfdif R A B)
      (synCuni (synCfdpivrange2 R A B)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fdrowss`. -/
@[expose]
noncomputable def gFdrowss (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (synWss (synCfdrow R A B C) (synCfdif R A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((synCfdif R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdrow A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @gSsrab2 (.classMem C (.cv d)) d (synCfdif R A B) dv_cache_0011
  have p0002 :=
    @gEqsstri (synCfdrow R A B C) (synCrab d (synCfdif R A B) (.classMem C (.cv d)))
      (synCfdif R A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elfdrowg`. -/
@[expose]
noncomputable def gElfdrowg (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (synWb (.classMem D (synCfdrow R A B C))
        (synWa (.classMem D (synCfdif R A B)) (.classMem C D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : d ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have dv_cache_0012 : d ∉ ((synCfdif R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0013 : d ∉ ((Wff.classMem C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          fresh_d_not_C, fresh_d_not_D, or_false, not_false_eq_true])
  have p0000 := @gEleq2 (.cv d) D C
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdrow A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0002 :=
    @gElrab2 (.classMem C (.cv d)) (.classMem C D) d D (synCfdif R A B)
      (synCfdrow R A B C) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fdrowex2`. -/
@[expose]
noncomputable def gFdrowex2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdrowex2_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdrowex2_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdrowex2_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) A) (.classMem (synCfdrow R A B C) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_C, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((synCfdif R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
          Finset.mem_union, fresh_d_not_A, fresh_d_not_B, fresh_d_not_R, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdrow A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := (Nominal.classEqRefl (synCrab d (synCfdif R A B) (.classMem C (.cv d))))
  have p0002 :=
    @gEqtri (synCfdrow R A B C) (synCrab d (synCfdif R A B) (.classMem C (.cv d)))
      (.cab d (synWa (.classMem (.cv d) (synCfdif R A B)) (.classMem C (.cv d)))) p0000
      p0001
  have p0003 := @gInab (.classMem (.cv d) (synCfdif R A B)) (.classMem C (.cv d)) d
  have p0004 :=
    @gEqcomi
      (synCin (.cab d (.classMem (.cv d) (synCfdif R A B))) (.cab d (.classMem C (.cv d))))
      (.cab d (synWa (.classMem (.cv d) (synCfdif R A B)) (.classMem C (.cv d)))) p0003
  have p0005 :=
    @gEqtri (synCfdrow R A B C)
      (.cab d (synWa (.classMem (.cv d) (synCfdif R A B)) (.classMem C (.cv d))))
      (synCin (.cab d (.classMem (.cv d) (synCfdif R A B))) (.cab d (.classMem C (.cv d))))
      p0002 p0004
  have p0006 := @gAbid2 d (synCfdif R A B) dv_cache_0011
  have p0007 :=
    @gIneq1i (.cab d (.classMem (.cv d) (synCfdif R A B))) (synCfdif R A B)
      (.cab d (.classMem C (.cv d))) p0006
  have p0008 :=
    @gEqtri (synCfdrow R A B C)
      (synCin (.cab d (.classMem (.cv d) (synCfdif R A B))) (.cab d (.classMem C (.cv d))))
      (synCin (synCfdif R A B) (.cab d (.classMem C (.cv d)))) p0005 p0007
  have p0009 :=
    @gA1i
      (.classEq (synCfdrow R A B C) (synCin (synCfdif R A B) (.cab d (.classMem C (.cv d)))))
      (synWbr R (synCwe) A) p0008
  have p0010 :=
    @gFdifex2 A B R dv_cache_0001 dv_cache_0003 dv_cache_0006 hyp_fdrowex2_1
      hyp_fdrowex2_2 hyp_fdrowex2_3
  have p0011 := @gSetswithex d C dv_cache_0009
  have p0012 :=
    @gA1i (.classMem (.cab d (.classMem C (.cv d))) (synCvv)) (synWbr R (synCwe) A)
      p0011
  have p0013 :=
    @gJca (synWbr R (synCwe) A) (.classMem (synCfdif R A B) (synCvv))
      (.classMem (.cab d (.classMem C (.cv d))) (synCvv)) p0010 p0012
  have p0014 :=
    @gInexg (synCfdif R A B) (.cab d (.classMem C (.cv d))) (synCvv) (synCvv)
  have p0015 :=
    @gSyl (synWbr R (synCwe) A)
      (synWa (.classMem (synCfdif R A B) (synCvv))
        (.classMem (.cab d (.classMem C (.cv d))) (synCvv)))
      (.classMem (synCin (synCfdif R A B) (.cab d (.classMem C (.cv d)))) (synCvv))
      p0013 p0014
  have p0016 :=
    @gEqeltrd (synWbr R (synCwe) A) (synCfdrow R A B C)
      (synCin (synCfdif R A B) (.cab d (.classMem C (.cv d)))) (synCvv) p0009 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elfdcodeg`. -/
@[expose]
noncomputable def gElfdcodeg (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_C_x : x ∉ C.fv) (_dv_D_R : Disjoint D.fv R.fv)
    (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem D (synCvv)) (synWb (.classMem D (synCfdcode R A B C))
          (synWrex x C (.classEq D (synCfdrow R A B (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
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
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv q) D)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, dv_D_x, or_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0003 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0008 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0009 : q ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_B, not_false_eq_true])
  have dv_cache_0010 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0011 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0012 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_C, not_false_eq_true])
  have dv_cache_0013 : x ∉ (C).fv :=
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
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0014 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_R, not_false_eq_true])
  have dv_cache_0015 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0016 : q ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0017 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_D, not_false_eq_true])
  have dv_cache_0018 : q ∉ ((synWrex x C (.classEq D (synCfdrow R A B (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrow,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_q_not_C, fresh_q_not_D, fresh_q_not_A,
          fresh_q_not_B, fresh_q_ne_x, fresh_q_not_R, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gId (.classEq (.cv q) D)
  have p0001 := @gEqeq1d (.classEq (.cv q) D) (.cv q) D (synCfdrow R A B (.cv x)) p0000
  have p0002 :=
    @gRexbidv (.classEq (.cv q) D) (.classEq (.cv q) (synCfdrow R A B (.cv x)))
      (.classEq D (synCfdrow R A B (.cv x))) x C dv_cache_0001 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdcode x A B C R q
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0004 :=
    @gElab2g (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x))))
      (synWrex x C (.classEq D (synCfdrow R A B (.cv x)))) q D (synCfdcode R A B C)
      (synCvv) dv_cache_0017 dv_cache_0018 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fdcodesspw2`. -/
@[expose]
noncomputable def gFdcodesspw2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (synWss (synCfdcode R A B C) (synCpw (synCfdif R A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_q_ne_x : q ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (A).fv from (by exact fresh_q_not_A))))))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0007 : Disjoint (B).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (B).fv from (by exact fresh_q_not_B))))))
  have dv_cache_0008 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0009 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0010 : Disjoint (C).fv ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (C).fv ((Class.cv q)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ q } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show q ∉ (C).fv from (by exact fresh_q_not_C))))))
  have dv_cache_0011 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0012 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0013 : Disjoint ((Class.cv q)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint ((Class.cv q)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ q } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show q ∉ (R).fv from (by exact fresh_q_not_R))))))
  have dv_cache_0014 : x ∉ ((Class.cv q)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_q, not_false_eq_true])
  have dv_cache_0015 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0016 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0017 : Disjoint (B).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (B).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (B).fv from (by exact fresh_x_not_B))))))
  have dv_cache_0018 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0019 : x ∉ ((Wff.classMem (.cv q) (synCpw (synCfdif R A B)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, fresh_x_not_A, fresh_x_not_B, fresh_x_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((synCfdcode R A B C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdcode,
          Finset.mem_union, fresh_q_not_A, fresh_q_not_B, fresh_q_not_C, fresh_q_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((synCpw (synCfdif R A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_B, fresh_q_not_R, or_false, not_false_eq_true])
  have p0000 := @gVex q
  have p0001 :=
    @gElfdcodeg x A B C (.cv q) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gBiimpi (.classMem (.cv q) (synCfdcode R A B C))
      (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x)))) p0002
  have p0004 := @gId (.classEq (.cv q) (synCfdrow R A B (.cv x)))
  have p0005 :=
    @gFdrowss A B (.cv x) R dv_cache_0001 dv_cache_0016 dv_cache_0004 dv_cache_0017
      dv_cache_0008 dv_cache_0018
  have p0006 :=
    @gSyl6eqss (.classEq (.cv q) (synCfdrow R A B (.cv x))) (.cv q)
      (synCfdrow R A B (.cv x)) (synCfdif R A B) p0004 p0005
  have p0008 := @gElpw (.cv q) (synCfdif R A B) p0000
  have p0009 :=
    @gSylibr (.classEq (.cv q) (synCfdrow R A B (.cv x)))
      (synWss (.cv q) (synCfdif R A B)) (.classMem (.cv q) (synCpw (synCfdif R A B)))
      p0006 p0008
  have p0010 :=
    @gRexlimivw (.classEq (.cv q) (synCfdrow R A B (.cv x)))
      (.classMem (.cv q) (synCpw (synCfdif R A B))) x C dv_cache_0019 p0009
  have p0011 :=
    @gSyl (.classMem (.cv q) (synCfdcode R A B C))
      (synWrex x C (.classEq (.cv q) (synCfdrow R A B (.cv x))))
      (.classMem (.cv q) (synCpw (synCfdif R A B))) p0003 p0010
  have p0012 :=
    @gSsriv q (synCfdcode R A B C) (synCpw (synCfdif R A B)) dv_cache_0020
      dv_cache_0021 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end
