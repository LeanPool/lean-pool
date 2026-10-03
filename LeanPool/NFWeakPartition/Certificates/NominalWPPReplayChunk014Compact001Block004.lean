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

@[expose]
noncomputable def g_wppstrictcomplement (A : Class) (R : Class) (e : Var) (c : Var)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_A_c : c ∉ A.fv) (_dv_A_e : e ∉ A.fv)
    (_dv_R_c : c ∉ R.fv) (_dv_R_e : e ∉ R.fv) (_dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (syn_wb (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
          (syn_wbr (.cv e) R (.cv c)))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
  have p0001 :=
    @g_simpll (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0002 := @g_wppweconnex A R
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cconnex) A) p0001 p0002
  have p0004 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)
  have p0005 :=
    @g_simplr (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0006 :=
    @g_connexd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      A R (.cv c) (.cv e) p0003 p0004 p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wo (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c))) p0000 p0006
  have p0008 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wbr (.cv c) R (.cv e))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      p0008 p0000
  have p0012 := @g_wppweref A R
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cref) A) p0001 p0012
  have p0015 :=
    @g_refd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      A R (.cv e) p0013 p0005
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr (.cv e) R (.cv e)) p0010 p0015
  have p0018 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) p0008 p0018
  have p0020 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wne (.cv c) (.cv e))
  have p0021 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wbr (.cv c) R (.cv e))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
              (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
          (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wbr (.cv c) R (.cv e)) p0020 p0021
  have p0023 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wne (.cv c) (.cv e))
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
              (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
          (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e)))
      (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)) p0022 p0023
  have p0025 := @g_strictbr R e c
  have p0026 :=
    @g_biimpri (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0025
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
              (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
          (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e)))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0024 p0026
  have p0028 :=
    @g_mtand
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wne (.cv c) (.cv e)) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0019
      p0027
  have p0029 := @g_id (syn_wne (.cv c) (.cv e))
  have p0030 := @g_necon1bi (syn_wne (.cv c) (.cv e)) (.cv c) (.cv e) p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (.neg (syn_wne (.cv c) (.cv e))) (.classEq (.cv c) (.cv e)) p0028 p0030
  have p0032 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (.cv c) (.cv e) (.cv e) R p0031
  have p0033 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
        (syn_wbr (.cv c) R (.cv e)))
      (syn_wbr (.cv e) R (.cv c)) (syn_wbr (.cv e) R (.cv e)) p0016 p0032
  have p0034 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c)) p0033
  have p0035 :=
    @g_idd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wbr (.cv e) R (.cv c))
  have p0036 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c)) (syn_wbr (.cv e) R (.cv c))
      p0034 p0035
  have p0037 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (syn_wo (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c)))
      (syn_wbr (.cv e) R (.cv c)) p0007 p0036
  have p0038 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c))
      p0037
  have p0039 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0040 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr (.cv e) R (.cv c))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      p0039 p0040
  have p0043 := @g_wppweantisym A R
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cantisym) A) p0001 p0043
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr R (syn_cantisym) A) p0041 p0044
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.classMem (.cv c) A) p0041 p0004
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.classMem (.cv e) A) p0041 p0005
  have p0056 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0058 :=
    @g_biimpi (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0025
  have p0059 := @g_simpl (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))
  have p0060 :=
    @g_syl (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)))
      (syn_wbr (.cv c) R (.cv e)) p0058 p0059
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wbr (.cv c) R (.cv e)) p0056
      p0060
  have p0063 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr (.cv e) R (.cv c))
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
      (syn_wbr (.cv e) R (.cv c)) p0039 p0063
  have p0065 :=
    @g_antid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      A R (.cv c) (.cv e) p0045 p0050 p0055 p0061 p0064
  have p0069 := @g_simpr (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))
  have p0070 :=
    @g_syl (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)))
      (syn_wne (.cv c) (.cv e)) p0058 p0069
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wne (.cv c) (.cv e)) p0056
      p0070
  have p0072 :=
    @g_pm2_21ddne
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
            (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
        (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.cv c) (.cv e) p0065 p0071
  have p0073 :=
    @g_pm2_01da
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
          (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)))
      (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0072
  have p0074 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (syn_wbr (.cv e) R (.cv c)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
      p0073
  have p0075 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c))
      p0038 p0074
  exact p0075

@[expose]
noncomputable def g_wppstrictleastbridge (ph : Wff) (A : Class) (R : Class) (e : Var)
    (c : Var) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv)
    (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (syn_wb
          (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg ph)))
          (syn_wral c A (.imp ph (syn_wbr (.cv e) R (.cv c)))))) :=
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
  have dv_cache_0007 : c ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))).fv :=
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
    @g_wppstrictcomplement A R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_imbi2d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c))
      ph p0000
  have p0002 := @g_con2b (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) ph
  have p0003 := @g_biid (.imp ph (syn_wbr (.cv e) R (.cv c)))
  have p0004 :=
    @g_n_3bitr4g
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A))
      (.imp ph (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))))
      (.imp ph (syn_wbr (.cv e) R (.cv c)))
      (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg ph))
      (.imp ph (syn_wbr (.cv e) R (.cv c))) p0001 p0002 p0003
  have p0005 :=
    @g_ralbidva (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
      (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg ph))
      (.imp ph (syn_wbr (.cv e) R (.cv c))) c A dv_cache_0007 p0004
  exact p0005

@[expose]
noncomputable def g_fdminsepfpivred (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv)
    (dv_D_e : e ∉ D.fv) (dv_R_e : e ∉ R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (syn_wb
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
          (.classMem (.cv e) (syn_cfpiv R A C D)))) :=
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
  have p0000 := @g_simpr (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))
  have p0001 :=
    @g_fdminsepval0J A B C D R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0002 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (syn_wa (.classMem C B) (.classMem D B))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
        (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg
            (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
                (.classMem (.cv c) (syn_csep2 C D)))))))
      p0000 p0001
  have p0003 := @g_simpl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))
  have p0004 :=
    @g_imnan (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
      (.classMem (.cv c) (syn_csep2 C D))
  have p0005 :=
    @g_ralbii
      (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.neg (.classMem (.cv c) (syn_csep2 C D))))
      (.neg (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.classMem (.cv c) (syn_csep2 C D))))
      c A p0004
  have p0006 :=
    @g_ralnex
      (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
        (.classMem (.cv c) (syn_csep2 C D)))
      c A
  have p0007 :=
    @g_bitri
      (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.neg (.classMem (.cv c) (syn_csep2 C D)))))
      (syn_wral c A (.neg (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      p0005 p0006
  have p0008 :=
    @g_bicomi
      (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.neg (.classMem (.cv c) (syn_csep2 C D)))))
      (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      p0007
  have p0009 :=
    @g_a1i
      (syn_wb (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
              (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A
          (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.neg (.classMem (.cv c) (syn_csep2 C D))))))
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))
      p0008
  have p0010 :=
    @g_simpl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
  have p0011 :=
    @g_simpr (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
  have p0012 := @g_simpl (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
      (.classMem (.cv e) A) p0011 p0012
  have p0014 :=
    @g_jca
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))
      (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) p0010 p0013
  have p0015 :=
    @g_wppstrictleastbridge (.classMem (.cv c) (syn_csep2 C D)) A R e c dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0016 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))
      (syn_wb (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.neg (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))))
      p0014 p0015
  have p0017 :=
    @g_bitrd
      (syn_wa (syn_wbr R (syn_cwe) A)
        (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))))
      (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
          (.neg (.classMem (.cv c) (syn_csep2 C D)))))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))
      p0009 p0016
  have p0018 :=
    @g_pm5_32da (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
      (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
            (.classMem (.cv c) (syn_csep2 C D)))))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))
      p0017
  have p0019 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (syn_wbr R (syn_cwe) A)
      (syn_wb (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg
            (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
                (.classMem (.cv c) (syn_csep2 C D))))))
        (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A
            (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))))
      p0003 p0018
  have p0020 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
      (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg
          (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
              (.classMem (.cv c) (syn_csep2 C D))))))
      (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))))
      p0002 p0019
  have p0021 :=
    @g_elfpiv A C D R e c dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0022 :=
    @g_bicomi (.classMem (.cv e) (syn_cfpiv R A C D))
      (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))))
      p0021
  have p0023 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
          (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))))
        (.classMem (.cv e) (syn_cfpiv R A C D)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0022
  have p0024 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B))
      (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))))
      (.classMem (.cv e) (syn_cfpiv R A C D)) p0020 p0023
  exact p0024

@[expose]
noncomputable def g_elfdminvalp (A : Class) (B : Class) (C : Class) (R : Class) (d : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv)
    (dv_C_d : d ∉ C.fv) (dv_R_d : d ∉ R.fv)
    (hyp_elfdminvalp_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv d) (syn_cfdminvalp R A B C)) (syn_wa (.classMem (.cv d) A)
          (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)))) :=
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
    @g_fdminvalpss A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_elfdminvalp_1
  have p0001 := @g_sseli (syn_cfdminvalp R A B C) A (.cv d) p0000
  have p0002 :=
    @g_fdminvalpbr d A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0007
      dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010
      hyp_elfdminvalp_1
  have p0003 :=
    @g_biimpi (.classMem (.cv d) (syn_cfdminvalp R A B C))
      (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) p0002
  have p0004 :=
    @g_jca (.classMem (.cv d) (syn_cfdminvalp R A B C)) (.classMem (.cv d) A)
      (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) p0001 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv d) A)
      (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B))
  have p0007 :=
    @g_biimpri (.classMem (.cv d) (syn_cfdminvalp R A B C))
      (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) p0002
  have p0008 :=
    @g_syl
      (syn_wa (.classMem (.cv d) A)
        (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)))
      (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B))
      (.classMem (.cv d) (syn_cfdminvalp R A B C)) p0005 p0007
  have p0009 :=
    @g_impbii (.classMem (.cv d) (syn_cfdminvalp R A B C))
      (syn_wa (.classMem (.cv d) A)
        (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)))
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

@[expose]
noncomputable def g_fdminvalpfpivred (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
        (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D))) :=
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
  have dv_cache_0002 : Disjoint (A).fv ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((syn_copk C D)).fv from (by
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
  have dv_cache_0005 : Disjoint (B).fv ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv ((syn_copk C D)).fv from (by
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
  have dv_cache_0008 : Disjoint ((syn_copk C D)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((syn_copk C D)).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint (((C).fv) ∪ ((D).fv)) ((R).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (C).fv (R).fv from (by exact dv_C_R)),
                  (show Disjoint (D).fv (R).fv from (by exact dv_D_R))⟩))))
  have dv_cache_0009 : d ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0025 : d ∉ ((syn_cfdminvalp R A B (syn_copk C D))).fv :=
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
  have dv_cache_0026 : d ∉ ((syn_cfpiv R A C D)).fv :=
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
    d ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))).fv :=
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
  have p0000 := @g_opkex C D
  have p0001 :=
    @g_elfdminvalp A B (syn_copk C D) R d dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (.cv d) (syn_cfdminvalp R A B (syn_copk C D)))
        (syn_wa (.classMem (.cv d) A)
          (.classMem (syn_copk (syn_csn (.cv d)) (syn_copk C D)) (syn_cfdminsep R A B))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0001
  have p0003 :=
    @g_fdminsepfpivred A B C D R d dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0003
      dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0006 dv_cache_0007 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0010
  have p0004 :=
    @g_anbi2d (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_copk (syn_csn (.cv d)) (syn_copk C D)) (syn_cfdminsep R A B))
      (.classMem (.cv d) (syn_cfpiv R A C D)) (.classMem (.cv d) A) p0003
  have p0005 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (.cv d) (syn_cfdminvalp R A B (syn_copk C D)))
      (syn_wa (.classMem (.cv d) A)
        (.classMem (syn_copk (syn_csn (.cv d)) (syn_copk C D)) (syn_cfdminsep R A B)))
      (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))) p0002 p0004
  have p0006 := @g_simpr (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D))
  have p0007 :=
    @g_elfpiv A C D R d c dv_cache_0011 dv_cache_0012 dv_cache_0003 dv_cache_0020
      dv_cache_0004 dv_cache_0015 dv_cache_0016 dv_cache_0021 dv_cache_0017 dv_cache_0018
      dv_cache_0022 dv_cache_0019 dv_cache_0023 dv_cache_0010 dv_cache_0024
  have p0008 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A C D))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 C D))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv d) R (.cv c)))))
      p0007
  have p0009 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 C D))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv d) R (.cv c))))
  have p0010 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A C D))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 C D))) (syn_wral c A
          (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) A) p0008 p0009
  have p0011 := @g_id (.classMem (.cv d) (syn_cfpiv R A C D))
  have p0012 :=
    @g_jca (.classMem (.cv d) (syn_cfpiv R A C D)) (.classMem (.cv d) A)
      (.classMem (.cv d) (syn_cfpiv R A C D)) p0010 p0011
  have p0013 :=
    @g_impbii (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D)))
      (.classMem (.cv d) (syn_cfpiv R A C D)) p0006 p0012
  have p0014 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D)))
        (.classMem (.cv d) (syn_cfpiv R A C D)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0013
  have p0015 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (.cv d) (syn_cfdminvalp R A B (syn_copk C D)))
      (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_cfpiv R A C D)))
      (.classMem (.cv d) (syn_cfpiv R A C D)) p0005 p0014
  have p0016 :=
    @g_eqrdv (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) d
      (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D) dv_cache_0025
      dv_cache_0026 dv_cache_0027 p0015
  exact p0016

@[expose]
noncomputable def g_fdminvalpeq4 (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (_dv_A_R : Disjoint A.fv R.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (_dv_C_R : Disjoint C.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (.classEq C D) (.classEq (syn_cfdminvalp R A B C) (syn_cfdminvalp R A B D))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdminvalp R A B C))
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfdminvalp R A B C)
        (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))))
      (.classEq C D) p0000
  have p0002 :=
    (Nominal.classEqRefl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))))
  have p0003 :=
    @g_a1i
      (.classEq (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))) (syn_cuni
          (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_c1c))))
      (.classEq C D) p0002
  have p0004 := @g_sneq C D
  have p0005 :=
    @g_imakeq2d (.classEq C D) (syn_csn C) (syn_csn D) (syn_ccnvk (syn_cfdminsep R A B))
      p0004
  have p0006 :=
    @g_ineq1d (.classEq C D) (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C))
      (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c) p0005
  have p0007 :=
    @g_unieqd (.classEq C D)
      (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_c1c))
      (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c)) p0006
  have p0008 :=
    @g_eqtrd (.classEq C D)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))
      (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)) (syn_c1c)))
      (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c)))
      p0003 p0007
  have p0009 :=
    (Nominal.classEqRefl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))))
  have p0010 :=
    @g_a1i
      (.classEq (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) (syn_cuni
          (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c))))
      (.classEq C D) p0009
  have p0011 :=
    @g_eqtr4d (.classEq C D)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))
      (syn_cuni (syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)) (syn_c1c)))
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) p0008 p0010
  have p0012 :=
    @g_eqtrd (.classEq C D) (syn_cfdminvalp R A B C)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn C)))
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))) p0001 p0011
  have p0013 := (Nominal.classEqRefl (syn_cfdminvalp R A B D))
  have p0014 :=
    @g_a1i
      (.classEq (syn_cfdminvalp R A B D)
        (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D))))
      (.classEq C D) p0013
  have p0015 :=
    @g_eqtr4d (.classEq C D) (syn_cfdminvalp R A B C)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn D)))
      (syn_cfdminvalp R A B D) p0012 p0014
  exact p0015

@[expose]
noncomputable def g_fdpivinrange (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_fdpivinrange_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdpivinrange_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdpivinrange_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
        (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B))) :=
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
  have dv_cache_0011 : Disjoint (A).fv ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv ((syn_copk C D)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((A).fv) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (A).fv (C).fv from (by exact dv_A_C)),
                  (show Disjoint (A).fv (D).fv from (by exact dv_A_D))⟩))))
  have dv_cache_0012 : Disjoint (B).fv ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (B).fv ((syn_copk C D)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
          exact
            (show Disjoint ((B).fv) (((C).fv) ∪ ((D).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (B).fv (C).fv from (by exact dv_B_C)),
                  (show Disjoint (B).fv (D).fv from (by exact dv_B_D))⟩))))
  have dv_cache_0013 : Disjoint ((syn_copk C D)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint ((syn_copk C D)).fv (R).fv from (by
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
  have dv_cache_0016 : Disjoint ((Class.cv p)).fv ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (show Disjoint ((Class.cv p)).fv ((syn_copk C D)).fv from (by
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
  have dv_cache_0018 : p ∉ ((syn_copk C D)).fv :=
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
  have dv_cache_0019 : p ∉ ((syn_cxpk B B)).fv :=
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
    p ∉ ((Wff.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d))).fv :=
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
  have dv_cache_0028 : d ∉ ((syn_cfpiv R A C D)).fv :=
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
      ((Wff.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
          (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)))).fv :=
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
    @g_fdminvalpfpivred A B C D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_fdminvalpex A B (syn_copk C D) R dv_cache_0001 dv_cache_0011 dv_cache_0004
      dv_cache_0012 dv_cache_0007 dv_cache_0013 hyp_fdpivinrange_1 hyp_fdpivinrange_2
      hyp_fdpivinrange_3
  have p0002 :=
    @g_a1i (.classMem (syn_cfdminvalp R A B (syn_copk C D)) (syn_cvv))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0001
  have p0003 :=
    @g_eqeltrrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D) (syn_cvv) p0000 p0002
  have p0004 :=
    @g_simpr (.classEq (.cv d) (syn_cfpiv R A C D))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
  have p0005 := @g_simpr (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))
  have p0006 := @g_id (syn_wa (.classMem C B) (.classMem D B))
  have p0007 := @g_simpl (.classMem C B) (.classMem D B)
  have p0008 := @g_elex C B
  have p0009 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B)
      (.classMem C (syn_cvv)) p0007 p0008
  have p0010 := @g_simpr (.classMem C B) (.classMem D B)
  have p0011 := @g_elex D B
  have p0012 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B)
      (.classMem D (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_jca (syn_wa (.classMem C B) (.classMem D B)) (.classMem C (syn_cvv))
      (.classMem D (syn_cvv)) p0009 p0012
  have p0014 := @g_opkelxpkg C D B B (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wb (.classMem (syn_copk C D) (syn_cxpk B B))
        (syn_wa (.classMem C B) (.classMem D B)))
      p0013 p0014
  have p0016 :=
    @g_mpbird (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B))
      p0006 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (syn_wa (.classMem C B) (.classMem D B)) (.classMem (syn_copk C D) (syn_cxpk B B))
      p0005 p0016
  have p0018 :=
    @g_syl
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_copk C D) (syn_cxpk B B)) p0004 p0017
  have p0021 :=
    @g_syl
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D)) p0004 p0000
  have p0022 :=
    @g_simpl (.classEq (.cv d) (syn_cfpiv R A C D))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
  have p0023 :=
    @g_eqcomd
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (.cv d) (syn_cfpiv R A C D) p0022
  have p0024 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (syn_cfdminvalp R A B (syn_copk C D)) (syn_cfpiv R A C D) (.cv d) p0021 p0023
  have p0025 :=
    @g_jca
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (.classMem (syn_copk C D) (syn_cxpk B B))
      (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d)) p0018 p0024
  have p0026 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk C D) R dv_cache_0001 dv_cache_0014 dv_cache_0011
      dv_cache_0004 dv_cache_0015 dv_cache_0012 dv_cache_0007 dv_cache_0016 dv_cache_0017
      dv_cache_0013
  have p0027 :=
    @g_eqeq1d (.classEq (.cv p) (syn_copk C D)) (syn_cfdminvalp R A B (.cv p))
      (syn_cfdminvalp R A B (syn_copk C D)) (.cv d) p0026
  have p0028 :=
    @g_rspcev (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv d))
      (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d)) p (syn_copk C D)
      (syn_cxpk B B) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0027
  have p0029 :=
    @g_syl
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (syn_wa (.classMem (syn_copk C D) (syn_cxpk B B))
        (.classEq (syn_cfdminvalp R A B (syn_copk C D)) (.cv d)))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv d))) p0025
      p0028
  have p0030 :=
    @g_fdpivrange2br A B (.cv d) R p dv_cache_0001 dv_cache_0021 dv_cache_0004
      dv_cache_0022 dv_cache_0023 dv_cache_0007 dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 hyp_fdpivinrange_1 hyp_fdpivinrange_2 hyp_fdpivinrange_3
  have p0031 :=
    @g_sylibr
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv d)))
      (.classMem (.cv d) (syn_cfdpivrange2 R A B)) p0029 p0030
  have p0033 :=
    @g_eleq1d
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (.cv d) (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B) p0022
  have p0034 :=
    @g_mpbid
      (syn_wa (.classEq (.cv d) (syn_cfpiv R A C D))
        (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))))
      (.classMem (.cv d) (syn_cfdpivrange2 R A B))
      (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)) p0031 p0033
  have p0035 :=
    @g_ex (.classEq (.cv d) (syn_cfpiv R A C D))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)) p0034
  have p0036 :=
    @g_vtocleg
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
        (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)))
      d (syn_cfpiv R A C D) (syn_cvv) dv_cache_0028 dv_cache_0029 p0035
  have p0037 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_cfpiv R A C D) (syn_cvv))
      (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
        (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)))
      p0003 p0036
  have p0038 :=
    @g_pm2_43i (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (syn_cfpiv R A C D) (syn_cfdpivrange2 R A B)) p0037
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

@[expose]
noncomputable def g_elfdif (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (_dv_A_e : e ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_B_e : e ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (_dv_R_e : e ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_e_x : e ≠ x) (dv_e_y : e ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv e) (syn_cfdif R A B)) (syn_wa (.classMem (.cv e) A) (syn_wrex x B
            (syn_wrex y B (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))))))) :=
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
      ((syn_wrex x B (syn_wrex y B (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdif x y A B R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_eleq2i (syn_cfdif R A B)
      (syn_crab d A
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      (.cv e) p0000
  have p0002 := @g_eleq1 (.cv d) (.cv e) (syn_cfpiv R A (.cv x) (.cv y))
  have p0003 :=
    @g_rexbidv (.classEq (.cv d) (.cv e))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))) y B dv_cache_0016 p0002
  have p0004 :=
    @g_rexbidv (.classEq (.cv d) (.cv e))
      (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))
      (syn_wrex y B (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y)))) x B dv_cache_0017
      p0003
  have p0005 :=
    @g_elrab
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))
      (syn_wrex x B (syn_wrex y B (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))))) d
      (.cv e) A dv_cache_0018 dv_cache_0003 dv_cache_0019 p0004
  have p0006 :=
    @g_bitri (.classMem (.cv e) (syn_cfdif R A B))
      (.classMem (.cv e) (syn_crab d A (syn_wrex x B
            (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))))
      (syn_wa (.classMem (.cv e) A)
        (syn_wrex x B (syn_wrex y B (.classMem (.cv e) (syn_cfpiv R A (.cv x) (.cv y))))))
      p0001 p0005
  exact p0006

@[expose]
noncomputable def g_fdifssunirange2x (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdifssunirange2x_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdifssunirange2x_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdifssunirange2x_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A)
        (syn_wss (syn_cfdif R A B) (syn_cuni (syn_cfdpivrange2 R A B)))) :=
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
    x ∉ ((Wff.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B)))).fv :=
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
    y ∉ ((Wff.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B)))).fv :=
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
  have dv_cache_0025 : x ∉ ((syn_wbr R (syn_cwe) A)).fv :=
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
  have dv_cache_0026 : y ∉ ((syn_wbr R (syn_cwe) A)).fv :=
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
  have dv_cache_0027 : d ∉ ((syn_cfdif R A B)).fv :=
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
  have dv_cache_0028 : d ∉ ((syn_cuni (syn_cfdpivrange2 R A B))).fv :=
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
  have dv_cache_0029 : d ∉ ((syn_wbr R (syn_cwe) A)).fv :=
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
    @g_elfdif x y A B R d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_cfdif R A B))
      (syn_wa (.classMem (.cv d) A)
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      p0000
  have p0002 :=
    @g_simpr (.classMem (.cv d) A)
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))
  have p0003 :=
    @g_syl (.classMem (.cv d) (syn_cfdif R A B))
      (syn_wa (.classMem (.cv d) A)
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))
      p0001 p0002
  have p0004 :=
    @g_a1i
      (.imp (.classMem (.cv d) (syn_cfdif R A B))
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      (syn_wbr R (syn_cwe) A) p0003
  have p0005 :=
    @g_fdpivinrange A B (.cv x) (.cv y) R dv_cache_0001 dv_cache_0016 dv_cache_0017
      dv_cache_0002 dv_cache_0018 dv_cache_0019 dv_cache_0006 dv_cache_0020 dv_cache_0021
      dv_cache_0022 hyp_fdifssunirange2x_1 hyp_fdifssunirange2x_2 hyp_fdifssunirange2x_3
  have p0006 := @g_elunii (.cv d) (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A B)
  have p0007 :=
    @g_sylan2
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (syn_cfpiv R A (.cv x) (.cv y)) (syn_cfdpivrange2 R A B))
      (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) p0005 p0006
  have p0008 :=
    @g_ex (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) p0007
  have p0009 :=
    @g_com12 (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) p0008
  have p0010 :=
    @g_rexlimdvva (syn_wbr R (syn_cwe) A)
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) x y B B dv_cache_0009
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0015 p0009
  have p0011 :=
    @g_syld (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (syn_cfdif R A B))
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))
      (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B))) p0004 p0010
  have p0012 :=
    @g_ssrdv (syn_wbr R (syn_cwe) A) d (syn_cfdif R A B)
      (syn_cuni (syn_cfdpivrange2 R A B)) dv_cache_0027 dv_cache_0028 dv_cache_0029 p0011
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

@[expose]
noncomputable def g_unirange2ssfdifx (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_unirange2ssfdifx_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_unirange2ssfdifx_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_unirange2ssfdifx_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A)
        (syn_wss (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cfdif R A B))) :=
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
  have dv_cache_0002 : q ∉ ((syn_cfdpivrange2 R A B)).fv :=
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
  have dv_cache_0019 : Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (show Disjoint (A).fv ((syn_copk (.cv x) (.cv y))).fv from (by
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
  have dv_cache_0021 : Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (show Disjoint (B).fv ((syn_copk (.cv x) (.cv y))).fv from (by
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
  have dv_cache_0022 : Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (show Disjoint ((Class.cv p)).fv ((syn_copk (.cv x) (.cv y))).fv from (by
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
  have dv_cache_0024 : Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (show Disjoint ((syn_copk (.cv x) (.cv y))).fv (R).fv from (by
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
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))).fv :=
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
  have dv_cache_0053 : p ∉ ((Wff.classMem (.cv d) (syn_cfdif R A B))).fv :=
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
    p ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))).fv :=
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
  have dv_cache_0055 : q ∉ ((Wff.classMem (.cv d) (syn_cfdif R A B))).fv :=
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
  have dv_cache_0056 : q ∉ ((syn_wbr R (syn_cwe) A)).fv :=
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
  have dv_cache_0057 : d ∉ ((syn_cuni (syn_cfdpivrange2 R A B))).fv :=
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
  have dv_cache_0058 : d ∉ ((syn_cfdif R A B)).fv :=
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
  have dv_cache_0059 : d ∉ ((syn_wbr R (syn_cwe) A)).fv :=
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
  have p0000 := @g_eluni2 q (.cv d) (syn_cfdpivrange2 R A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B)))
      (syn_wrex q (syn_cfdpivrange2 R A B) (.classMem (.cv d) (.cv q))) p0000
  have p0002 :=
    @g_a1i
      (.imp (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B)))
        (syn_wrex q (syn_cfdpivrange2 R A B) (.classMem (.cv d) (.cv q))))
      (syn_wbr R (syn_cwe) A) p0001
  have p0003 :=
    @g_fdpivrange2br A B (.cv q) R p dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 hyp_unirange2ssfdifx_1 hyp_unirange2ssfdifx_2 hyp_unirange2ssfdifx_3
  have p0004 :=
    @g_biimpi (.classMem (.cv q) (syn_cfdpivrange2 R A B))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) p0003
  have p0005 :=
    @g_a1i
      (.imp (.classMem (.cv q) (syn_cfdpivrange2 R A B))
        (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0004
  have p0006 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (syn_cxpk B B)))
      (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0007 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv p) (syn_cxpk B B))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (syn_cxpk B B)))
      (.classMem (.cv p) (syn_cxpk B B)) p0006 p0007
  have p0009 :=
    @g_elxpk2 x y (.cv p) B B dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0010 :=
    @g_biimpi (.classMem (.cv p) (syn_cxpk B B))
      (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv p) (syn_cxpk B B))
      (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))) p0008
      p0010
  have p0012 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0013 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classMem (.cv y) B)
  have p0014 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv x) B)
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      p0013 p0014
  have p0017 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv p) (syn_cxpk B B))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (syn_cxpk B B)))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) p0006 p0017
  have p0019 := @g_simpr (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv d) (.cv q)) p0018 p0019
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv d) (.cv q)) p0015 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classMem (.cv d) (.cv q)) p0012 p0021
  have p0027 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (syn_cxpk B B)))
      (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) p0015 p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)) p0012 p0028
  have p0030 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (syn_cfdminvalp R A B (.cv p)) (.cv q) p0029
  have p0031 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
  have p0032 :=
    @g_fdminvalpeq4 A B (.cv p) (syn_copk (.cv x) (.cv y)) R dv_cache_0003 dv_cache_0018
      dv_cache_0019 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0008 dv_cache_0022
      dv_cache_0023 dv_cache_0024
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
      (.classEq (syn_cfdminvalp R A B (.cv p))
        (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))))
      p0031 p0032
  have p0034 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (.cv q) (syn_cfdminvalp R A B (.cv p))
      (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y))) p0030 p0033
  have p0042 := @g_simpl (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))) (syn_wbr R (syn_cwe) A)
      p0018 p0042
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wbr R (syn_cwe) A) p0015 p0043
  have p0046 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv x) B)
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classMem (.cv x) B) p0013 p0046
  have p0048 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classMem (.cv y) B)
  have p0049 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0047 p0048
  have p0050 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0044
      p0049
  have p0051 :=
    @g_fdminvalpfpivred A B (.cv x) (.cv y) R dv_cache_0003 dv_cache_0025 dv_cache_0026
      dv_cache_0005 dv_cache_0027 dv_cache_0028 dv_cache_0008 dv_cache_0029 dv_cache_0030
      dv_cache_0031
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))
        (syn_cfpiv R A (.cv x) (.cv y)))
      p0050 p0051
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))
        (syn_cfpiv R A (.cv x) (.cv y)))
      p0012 p0052
  have p0054 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (.cv q) (syn_cfdminvalp R A B (syn_copk (.cv x) (.cv y)))
      (syn_cfpiv R A (.cv x) (.cv y)) p0034 p0053
  have p0055 :=
    @g_eleqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
                (.classMem (.cv p) (syn_cxpk B B)))
              (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
          (.classMem (.cv y) B)) (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (.cv d) (.cv q) (syn_cfpiv R A (.cv x) (.cv y)) p0022 p0054
  have p0056 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
              (.classMem (.cv p) (syn_cxpk B B)))
            (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
        (.classMem (.cv y) B))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) p0055
  have p0057 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))) (.classMem (.cv x) B))
      (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) y B dv_cache_0032 p0056
  have p0058 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y))))
      (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))) x B dv_cache_0033
      p0057
  have p0059 :=
    @g_elfpiv A (.cv x) (.cv y) R d c dv_cache_0025 dv_cache_0026 dv_cache_0005
      dv_cache_0034 dv_cache_0035 dv_cache_0029 dv_cache_0030 dv_cache_0036 dv_cache_0037
      dv_cache_0031 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
  have p0060 :=
    @g_biimpi (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      p0059
  have p0061 :=
    @g_simpll (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y)))
      (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
          (syn_wbr (.cv d) R (.cv c))))
  have p0062 :=
    @g_syl (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv d) A) (.classMem (.cv d) (syn_csep2 (.cv x) (.cv y))))
        (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 (.cv x) (.cv y)))
            (syn_wbr (.cv d) R (.cv c)))))
      (.classMem (.cv d) A) p0060 p0061
  have p0063 :=
    @g_a1i
      (.imp (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
            (.classMem (.cv p) (syn_cxpk B B)))
          (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      p0062
  have p0064 :=
    @g_rexlimdvva
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))) (.classMem (.cv d) A) x y B B
      dv_cache_0016 dv_cache_0043 dv_cache_0044 dv_cache_0033 dv_cache_0045 dv_cache_0017
      p0063
  have p0065 :=
    @g_syld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))))
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))
      (.classMem (.cv d) A) p0058 p0064
  have p0113 :=
    @g_jcad
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))))
      (.classMem (.cv d) A)
      (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))
      p0065 p0058
  have p0114 :=
    @g_elfdif x y A B R d dv_cache_0003 dv_cache_0005 dv_cache_0035 dv_cache_0046
      dv_cache_0047 dv_cache_0008 dv_cache_0048 dv_cache_0015 dv_cache_0016 dv_cache_0041
      dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0017
  have p0115 :=
    @g_biimpri (.classMem (.cv d) (syn_cfdif R A B))
      (syn_wa (.classMem (.cv d) A)
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      p0114
  have p0116 :=
    @g_syl6
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))))
      (syn_wa (.classMem (.cv d) A)
        (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))))
      (.classMem (.cv d) (syn_cfdif R A B)) p0113 p0115
  have p0117 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
          (.classMem (.cv p) (syn_cxpk B B))) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (syn_wrex x B (syn_wrex y B (.classEq (.cv p) (syn_copk (.cv x) (.cv y)))))
      (.classMem (.cv d) (syn_cfdif R A B)) p0011 p0116
  have p0118 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
        (.classMem (.cv p) (syn_cxpk B B)))
      (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
      (.classMem (.cv d) (syn_cfdif R A B)) p0117
  have p0119 :=
    @g_rexlimdva (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
      (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q))
      (.classMem (.cv d) (syn_cfdif R A B)) p (syn_cxpk B B) dv_cache_0053 dv_cache_0054
      p0118
  have p0120 :=
    @g_syld (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv q) (syn_cfdpivrange2 R A B))
      (syn_wrex p (syn_cxpk B B) (.classEq (syn_cfdminvalp R A B (.cv p)) (.cv q)))
      (.classMem (.cv d) (syn_cfdif R A B)) p0005 p0119
  have p0121 :=
    @g_ex (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
      (.imp (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (.classMem (.cv d) (syn_cfdif R A B)))
      p0120
  have p0122 :=
    @g_com23 (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
      (.classMem (.cv q) (syn_cfdpivrange2 R A B)) (.classMem (.cv d) (syn_cfdif R A B))
      p0121
  have p0123 :=
    @g_rexlimdv (syn_wbr R (syn_cwe) A) (.classMem (.cv d) (.cv q))
      (.classMem (.cv d) (syn_cfdif R A B)) q (syn_cfdpivrange2 R A B) dv_cache_0055
      dv_cache_0056 p0122
  have p0124 :=
    @g_syld (syn_wbr R (syn_cwe) A)
      (.classMem (.cv d) (syn_cuni (syn_cfdpivrange2 R A B)))
      (syn_wrex q (syn_cfdpivrange2 R A B) (.classMem (.cv d) (.cv q)))
      (.classMem (.cv d) (syn_cfdif R A B)) p0002 p0123
  have p0125 :=
    @g_ssrdv (syn_wbr R (syn_cwe) A) d (syn_cuni (syn_cfdpivrange2 R A B))
      (syn_cfdif R A B) dv_cache_0057 dv_cache_0058 dv_cache_0059 p0124
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

@[expose]
noncomputable def g_fdifequnirange2x (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdifequnirange2x_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdifequnirange2x_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdifequnirange2x_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A)
        (.classEq (syn_cfdif R A B) (syn_cuni (syn_cfdpivrange2 R A B)))) :=
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
    @g_fdifssunirange2x A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdifequnirange2x_1 hyp_fdifequnirange2x_2 hyp_fdifequnirange2x_3
  have p0001 :=
    @g_unirange2ssfdifx A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_fdifequnirange2x_1 hyp_fdifequnirange2x_2 hyp_fdifequnirange2x_3
  have p0002 :=
    @g_jca (syn_wbr R (syn_cwe) A)
      (syn_wss (syn_cfdif R A B) (syn_cuni (syn_cfdpivrange2 R A B)))
      (syn_wss (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cfdif R A B)) p0000 p0001
  have p0003 := @g_eqss (syn_cfdif R A B) (syn_cuni (syn_cfdpivrange2 R A B))
  have p0004 :=
    @g_sylibr (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wss (syn_cfdif R A B) (syn_cuni (syn_cfdpivrange2 R A B)))
        (syn_wss (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cfdif R A B)))
      (.classEq (syn_cfdif R A B) (syn_cuni (syn_cfdpivrange2 R A B))) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fdifex2 (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv) (hyp_fdifex2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdifex2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdifex2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A B) (syn_cvv))) :=
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
    @g_fdifequnirange2x A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdifex2_1
      hyp_fdifex2_2 hyp_fdifex2_3
  have p0001 :=
    @g_fdpivrange2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdifex2_1
      hyp_fdifex2_2 hyp_fdifex2_3
  have p0002 := @g_uniex (syn_cfdpivrange2 R A B) p0001
  have p0003 :=
    @g_a1i (.classMem (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cvv))
      (syn_wbr R (syn_cwe) A) p0002
  have p0004 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdif R A B)
      (syn_cuni (syn_cfdpivrange2 R A B)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_fdrowss (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (syn_wss (syn_cfdrow R A B C) (syn_cfdif R A B)) :=
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
  have dv_cache_0011 : d ∉ ((syn_cfdif R A B)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrow A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @g_ssrab2 (.classMem C (.cv d)) d (syn_cfdif R A B) dv_cache_0011
  have p0002 :=
    @g_eqsstri (syn_cfdrow R A B C) (syn_crab d (syn_cfdif R A B) (.classMem C (.cv d)))
      (syn_cfdif R A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elfdrowg (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (_dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_cfdrow R A B C))
        (syn_wa (.classMem D (syn_cfdif R A B)) (.classMem C D))) :=
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
  have dv_cache_0012 : d ∉ ((syn_cfdif R A B)).fv :=
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
  have p0000 := @g_eleq2 (.cv d) D C
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrow A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0002 :=
    @g_elrab2 (.classMem C (.cv d)) (.classMem C D) d D (syn_cfdif R A B)
      (syn_cfdrow R A B C) dv_cache_0011 dv_cache_0012 dv_cache_0013 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fdrowex2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdrowex2_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdrowex2_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdrowex2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdrow R A B C) (syn_cvv))) :=
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
  have dv_cache_0011 : d ∉ ((syn_cfdif R A B)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdrow A B C R d
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := (Nominal.classEqRefl (syn_crab d (syn_cfdif R A B) (.classMem C (.cv d))))
  have p0002 :=
    @g_eqtri (syn_cfdrow R A B C) (syn_crab d (syn_cfdif R A B) (.classMem C (.cv d)))
      (.cab d (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d)))) p0000
      p0001
  have p0003 := @g_inab (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d)) d
  have p0004 :=
    @g_eqcomi
      (syn_cin (.cab d (.classMem (.cv d) (syn_cfdif R A B))) (.cab d (.classMem C (.cv d))))
      (.cab d (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d)))) p0003
  have p0005 :=
    @g_eqtri (syn_cfdrow R A B C)
      (.cab d (syn_wa (.classMem (.cv d) (syn_cfdif R A B)) (.classMem C (.cv d))))
      (syn_cin (.cab d (.classMem (.cv d) (syn_cfdif R A B))) (.cab d (.classMem C (.cv d))))
      p0002 p0004
  have p0006 := @g_abid2 d (syn_cfdif R A B) dv_cache_0011
  have p0007 :=
    @g_ineq1i (.cab d (.classMem (.cv d) (syn_cfdif R A B))) (syn_cfdif R A B)
      (.cab d (.classMem C (.cv d))) p0006
  have p0008 :=
    @g_eqtri (syn_cfdrow R A B C)
      (syn_cin (.cab d (.classMem (.cv d) (syn_cfdif R A B))) (.cab d (.classMem C (.cv d))))
      (syn_cin (syn_cfdif R A B) (.cab d (.classMem C (.cv d)))) p0005 p0007
  have p0009 :=
    @g_a1i
      (.classEq (syn_cfdrow R A B C) (syn_cin (syn_cfdif R A B) (.cab d (.classMem C (.cv d)))))
      (syn_wbr R (syn_cwe) A) p0008
  have p0010 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0003 dv_cache_0006 hyp_fdrowex2_1
      hyp_fdrowex2_2 hyp_fdrowex2_3
  have p0011 := @g_setswithex d C dv_cache_0009
  have p0012 :=
    @g_a1i (.classMem (.cab d (.classMem C (.cv d))) (syn_cvv)) (syn_wbr R (syn_cwe) A)
      p0011
  have p0013 :=
    @g_jca (syn_wbr R (syn_cwe) A) (.classMem (syn_cfdif R A B) (syn_cvv))
      (.classMem (.cab d (.classMem C (.cv d))) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_inexg (syn_cfdif R A B) (.cab d (.classMem C (.cv d))) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wbr R (syn_cwe) A)
      (syn_wa (.classMem (syn_cfdif R A B) (syn_cvv))
        (.classMem (.cab d (.classMem C (.cv d))) (syn_cvv)))
      (.classMem (syn_cin (syn_cfdif R A B) (.cab d (.classMem C (.cv d)))) (syn_cvv))
      p0013 p0014
  have p0016 :=
    @g_eqeltrd (syn_wbr R (syn_cwe) A) (syn_cfdrow R A B C)
      (syn_cin (syn_cfdif R A B) (.cab d (.classMem C (.cv d)))) (syn_cvv) p0009 p0015
  exact p0016

@[expose]
noncomputable def g_elfdcodeg (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (_dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (_dv_C_D : Disjoint C.fv D.fv)
    (dv_C_R : Disjoint C.fv R.fv) (dv_C_x : x ∉ C.fv) (_dv_D_R : Disjoint D.fv R.fv)
    (dv_D_x : x ∉ D.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cvv)) (syn_wb (.classMem D (syn_cfdcode R A B C))
          (syn_wrex x C (.classEq D (syn_cfdrow R A B (.cv x)))))) :=
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
  have dv_cache_0018 : q ∉ ((syn_wrex x C (.classEq D (syn_cfdrow R A B (.cv x))))).fv :=
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
  have p0000 := @g_id (.classEq (.cv q) D)
  have p0001 := @g_eqeq1d (.classEq (.cv q) D) (.cv q) D (syn_cfdrow R A B (.cv x)) p0000
  have p0002 :=
    @g_rexbidv (.classEq (.cv q) D) (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))
      (.classEq D (syn_cfdrow R A B (.cv x))) x C dv_cache_0001 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdcode x A B C R q
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0004 :=
    @g_elab2g (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x))))
      (syn_wrex x C (.classEq D (syn_cfdrow R A B (.cv x)))) q D (syn_cfdcode R A B C)
      (syn_cvv) dv_cache_0017 dv_cache_0018 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fdcodesspw2 (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (syn_wss (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B))) :=
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
  have dv_cache_0019 : x ∉ ((Wff.classMem (.cv q) (syn_cpw (syn_cfdif R A B)))).fv :=
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
  have dv_cache_0020 : q ∉ ((syn_cfdcode R A B C)).fv :=
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
  have dv_cache_0021 : q ∉ ((syn_cpw (syn_cfdif R A B))).fv :=
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
  have p0000 := @g_vex q
  have p0001 :=
    @g_elfdcodeg x A B C (.cv q) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_biimpi (.classMem (.cv q) (syn_cfdcode R A B C))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))) p0002
  have p0004 := @g_id (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))
  have p0005 :=
    @g_fdrowss A B (.cv x) R dv_cache_0001 dv_cache_0016 dv_cache_0004 dv_cache_0017
      dv_cache_0008 dv_cache_0018
  have p0006 :=
    @g_syl6eqss (.classEq (.cv q) (syn_cfdrow R A B (.cv x))) (.cv q)
      (syn_cfdrow R A B (.cv x)) (syn_cfdif R A B) p0004 p0005
  have p0008 := @g_elpw (.cv q) (syn_cfdif R A B) p0000
  have p0009 :=
    @g_sylibr (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))
      (syn_wss (.cv q) (syn_cfdif R A B)) (.classMem (.cv q) (syn_cpw (syn_cfdif R A B)))
      p0006 p0008
  have p0010 :=
    @g_rexlimivw (.classEq (.cv q) (syn_cfdrow R A B (.cv x)))
      (.classMem (.cv q) (syn_cpw (syn_cfdif R A B))) x C dv_cache_0019 p0009
  have p0011 :=
    @g_syl (.classMem (.cv q) (syn_cfdcode R A B C))
      (syn_wrex x C (.classEq (.cv q) (syn_cfdrow R A B (.cv x))))
      (.classMem (.cv q) (syn_cpw (syn_cfdif R A B))) p0003 p0010
  have p0012 :=
    @g_ssriv q (syn_cfdcode R A B C) (syn_cpw (syn_cfdif R A B)) dv_cache_0020
      dv_cache_0021 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end
