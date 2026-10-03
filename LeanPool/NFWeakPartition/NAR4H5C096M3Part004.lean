/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C096M3Part004Stage1


/-! NF weak partition development: NAR4H5C096M3Part004. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

@[expose]
noncomputable def nb096_wpp_refl_0023 (D : Class) (R : Class) (q : Var) :
    TReflOn
      [((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      ((syn_cen)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0024 D R q)

@[expose]
noncomputable def nominal_df_wecutcardfn (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) :
    Nominal.NPrf
      (.classEq (syn_cwecutcardfn R D) (syn_cmpt q (syn_cpw1 (syn_cpw1 D)) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb096_split_alpha_0002 D R q) (TAlphaWff.conj (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb096_alpha_dummy_000 D R) ≠ (nb096_alpha_dummy_001 D R) from (by
                          unfold nb096_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0004 D R) 0))))
                      (show q ≠ (nb096_alpha_dummy_002 D R q) from (by
                          unfold nb096_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0005 D R q) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn
                    [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                      ((nb096_alpha_dummy_000 D R), q),
                      ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
                    (syn_cpw1 (syn_cpw1 D)) (nb096_wpp_refl_0007 D R q dv_D_q)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn
        [((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] D (nb096_focused_refl_0000 D R q dv_D_q)))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((syn_cuni (Class.cv (nb096_alpha_dummy_000
        D R)))).fv) (by decide)) (freshVar_injective (((syn_cuni (Class.cv q))).fv) (by decide))
        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv)
        (by decide)) (freshVar_injective (((Class.cv q)).fv) (by decide)) (TAlphaVar.here
        _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_062 D R) from (by
          unfold
            nb096_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_064 q) from (by
          unfold
            nb096_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_061 D R) from (by
          unfold
            nb096_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_063 q) from (by
          unfold
            nb096_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_058 D R) from (by
          unfold
            nb096_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_060 q) from (by
          unfold
            nb096_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_057 D R) from (by
          unfold
            nb096_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_059 q) from (by
          unfold
            nb096_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_055 D R) from (by
          unfold
            nb096_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0054
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_056 q) from (by
          unfold
            nb096_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0055
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_052 D R) from (by
          unfold
            nb096_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_054 R q) from (by
          unfold
            nb096_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_051 D R) from (by
          unfold
            nb096_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_053 R q) from (by
          unfold
            nb096_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_049 D R) from (by
          unfold
            nb096_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0050
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_050 D R q) from (by
          unfold
            nb096_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0051
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_047 D R) from (by
          unfold
            nb096_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0048
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_048 D R q) from (by
          unfold
            nb096_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0049
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_045 D R) from (by
          unfold
            nb096_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0046
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_046 D R q) from (by
          unfold
            nb096_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0047
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_042 D R) from (by
          unfold
            nb096_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_044 D R q) from (by
          unfold
            nb096_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_041 D R) from (by
          unfold
            nb096_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_043 D R q) from (by
          unfold
            nb096_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_001 D R) from (by
          unfold
            nb096_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_002 D R q) from (by
          unfold
            nb096_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0005
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb096_split_alpha_0003 D R q))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_066 D R) from (by
          unfold
            nb096_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
          unfold
            nb096_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_065 D R) from (by
          unfold
            nb096_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold
            nb096_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_095 D R) from (by
          unfold
            nb096_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_096 R q) from (by
          unfold
            nb096_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_069 D R) from (by
          unfold
            nb096_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_070 R q) from (by
          unfold
            nb096_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (syn_cuni (syn_cuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪ ((Class.cv
        (nb096_alpha_dummy_053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D
        R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R
        q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069
        D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054
        R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D
        R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046
        D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D
        R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_051 D
        R) ≠ (nb096_alpha_dummy_066 D R) from (by
          unfold
            nb096_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
          unfold
            nb096_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_065 D R) from (by
          unfold
            nb096_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold
            nb096_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_095 D R) from (by
          unfold
            nb096_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_096 R q) from (by
          unfold
            nb096_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_069 D R) from (by
          unfold
            nb096_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_070 R q) from (by
          unfold
            nb096_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (syn_cuni (syn_cuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪ ((Class.cv
        (nb096_alpha_dummy_053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D
        R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R
        q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069
        D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054
        R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D
        R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046
        D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D
        R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
        [((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_ccnv (syn_cdif R (syn_cid)))
        (nb096_wpp_refl_0015 D R q dv_R_q))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn
        [((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] D (nb096_focused_refl_0000 D R q dv_D_q)))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((syn_cuni (Class.cv (nb096_alpha_dummy_000
        D R)))).fv) (by decide)) (freshVar_injective (((syn_cuni (Class.cv q))).fv) (by decide))
        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_000 D R))).fv)
        (by decide)) (freshVar_injective (((Class.cv q)).fv) (by decide)) (TAlphaVar.here
        _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_062 D R) from (by
          unfold
            nb096_alpha_dummy_062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_064 q) from (by
          unfold
            nb096_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_061 D R) from (by
          unfold
            nb096_alpha_dummy_061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_063 q) from (by
          unfold
            nb096_alpha_dummy_063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_058 D R) from (by
          unfold
            nb096_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_060 q) from (by
          unfold
            nb096_alpha_dummy_060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_057 D R) from (by
          unfold
            nb096_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_059 q) from (by
          unfold
            nb096_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_055 D R) from (by
          unfold
            nb096_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0054
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_056 q) from (by
          unfold
            nb096_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0055
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_052 D R) from (by
          unfold
            nb096_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_054 R q) from (by
          unfold
            nb096_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_051 D R) from (by
          unfold
            nb096_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_053 R q) from (by
          unfold
            nb096_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_049 D R) from (by
          unfold
            nb096_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0050
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_050 D R q) from (by
          unfold
            nb096_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0051
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_047 D R) from (by
          unfold
            nb096_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0048
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_048 D R q) from (by
          unfold
            nb096_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0049
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_045 D R) from (by
          unfold
            nb096_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0046
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_046 D R q) from (by
          unfold
            nb096_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0047
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_042 D R) from (by
          unfold
            nb096_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  1)))) (show q ≠ (nb096_alpha_dummy_044 D R q) from (by
          unfold
            nb096_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_041 D R) from (by
          unfold
            nb096_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_043 D R q) from (by
          unfold
            nb096_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_000 D R) ≠
        (nb096_alpha_dummy_001 D R) from (by
          unfold
            nb096_alpha_dummy_001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004
                    D
                    R)
                  0)))) (show q ≠ (nb096_alpha_dummy_002 D R q) from (by
          unfold
            nb096_alpha_dummy_002;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0005
                    D
                    R
                    q)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb096_split_alpha_0003 D R q))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_066 D R) from (by
          unfold
            nb096_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
          unfold
            nb096_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_065 D R) from (by
          unfold
            nb096_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold
            nb096_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_095 D R) from (by
          unfold
            nb096_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_096 R q) from (by
          unfold
            nb096_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_069 D R) from (by
          unfold
            nb096_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_070 R q) from (by
          unfold
            nb096_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (syn_cuni (syn_cuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪ ((Class.cv
        (nb096_alpha_dummy_053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D
        R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R
        q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069
        D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054
        R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D
        R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046
        D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D
        R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096_alpha_dummy_051 D
        R) ≠ (nb096_alpha_dummy_066 D R) from (by
          unfold
            nb096_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_068 R q) from (by
          unfold
            nb096_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_065 D R) from (by
          unfold
            nb096_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_067 R q) from (by
          unfold
            nb096_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_095 D R) from (by
          unfold
            nb096_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_096 R q) from (by
          unfold
            nb096_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096_alpha_dummy_051 D R) ≠
        (nb096_alpha_dummy_069 D R) from (by
          unfold
            nb096_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096_alpha_dummy_053 R q) ≠ (nb096_alpha_dummy_070 R q) from (by
          unfold
            nb096_alpha_dummy_070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (syn_cdif R
        (syn_cid)))).fv ∪ ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪ ((syn_csn
        (syn_cuni (syn_cuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096_alpha_dummy_052 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096_alpha_dummy_054 R q))).fv ∪ ((Class.cv
        (nb096_alpha_dummy_053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb096_alpha_dummy_097 D R), (nb096_alpha_dummy_098 R q)), ((nb096_alpha_dummy_066 D
        R), (nb096_alpha_dummy_068 R q)), ((nb096_alpha_dummy_065 D R), (nb096_alpha_dummy_067 R
        q)), ((nb096_alpha_dummy_095 D R), (nb096_alpha_dummy_096 R q)), ((nb096_alpha_dummy_069
        D R), (nb096_alpha_dummy_070 R q)), ((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054
        R q)), ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)), ((nb096_alpha_dummy_047 D
        R), (nb096_alpha_dummy_048 D R q)), ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046
        D R q)), ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)), ((nb096_alpha_dummy_001 D
        R), (nb096_alpha_dummy_002 D R q)), ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))] (syn_ccompl (syn_csn
        (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
        [((nb096_alpha_dummy_052 D R), (nb096_alpha_dummy_054 R q)),
        ((nb096_alpha_dummy_051 D R), (nb096_alpha_dummy_053 R q)),
        ((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
        (nb096_alpha_dummy_004 D R q))] (syn_ccnv (syn_cdif R (syn_cid)))
        (nb096_wpp_refl_0015 D R q dv_R_q))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.neg (nb096_split_alpha_0006 D R q))))
                          (TAlphaClass.refl_of_reflOn
                            [((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
                              ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
                              ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
                              ((nb096_alpha_dummy_000 D R), q), ((nb096_alpha_dummy_003 D R),
                                (nb096_alpha_dummy_004 D R q))]
                            (syn_cen) (nb096_wpp_refl_0023 D R q))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
