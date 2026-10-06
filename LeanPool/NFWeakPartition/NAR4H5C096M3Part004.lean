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

/-- Checked nominal proof certificate identified upstream as `nb096_wpp_refl_0023`. -/
@[expose]
noncomputable def nb096WppRefl0023 (D : Class) (R : Class) (q : Var) :
    TReflOn
      [((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      ((synCen)).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0024 D R q)

/-- Checked nominal proof certificate identified upstream as `nominal_df_wecutcardfn`. -/
@[expose]
noncomputable def nominalDfWecutcardfn (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synCwecutcardfn R D) (synCmpt q (synCpw1 (synCpw1 D)) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb096SplitAlpha0002 D R q) (TAlphaWff.conj (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (show (nb096AlphaDummy000 D R) ≠ (nb096AlphaDummy001 D R) from (by
                          unfold nb096AlphaDummy001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0004 D R) 0))))
                      (show q ≠ (nb096AlphaDummy002 D R q) from (by
                          unfold nb096AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb096_support_mem_0005 D R q) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfReflOn
                    [((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                      ((nb096AlphaDummy000 D R), q),
                      ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
                    (synCpw1 (synCpw1 D)) (nb096WppRefl0007 D R q dv_D_q)))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfReflOn
        [((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] D (nb096FocusedRefl0000 D R q dv_D_q)))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((synCuni (Class.cv (nb096AlphaDummy000
        D R)))).fv) (by decide)) (freshVar_injective (((synCuni (Class.cv q))).fv) (by decide))
        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy000 D R))).fv)
        (by decide)) (freshVar_injective (((Class.cv q)).fv) (by decide)) (TAlphaVar.here
        _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy062 D R) from (by
          unfold
            nb096AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy064 q) from (by
          unfold
            nb096AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy061 D R) from (by
          unfold
            nb096AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy063 q) from (by
          unfold
            nb096AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy058 D R) from (by
          unfold
            nb096AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy060 q) from (by
          unfold
            nb096AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy057 D R) from (by
          unfold
            nb096AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy059 q) from (by
          unfold
            nb096AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy055 D R) from (by
          unfold
            nb096AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0054
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy056 q) from (by
          unfold
            nb096AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0055
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy052 D R) from (by
          unfold
            nb096AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy054 R q) from (by
          unfold
            nb096AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy051 D R) from (by
          unfold
            nb096AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy053 R q) from (by
          unfold
            nb096AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy049 D R) from (by
          unfold
            nb096AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0050
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy050 D R q) from (by
          unfold
            nb096AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0051
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy047 D R) from (by
          unfold
            nb096AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0048
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy048 D R q) from (by
          unfold
            nb096AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0049
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy045 D R) from (by
          unfold
            nb096AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0046
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy046 D R q) from (by
          unfold
            nb096AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0047
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy042 D R) from (by
          unfold
            nb096AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy044 D R q) from (by
          unfold
            nb096AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy041 D R) from (by
          unfold
            nb096AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy043 D R q) from (by
          unfold
            nb096AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy001 D R) from (by
          unfold
            nb096AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy002 D R q) from (by
          unfold
            nb096AlphaDummy002;
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
        (nb096SplitAlpha0003 D R q))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy066 D R) from (by
          unfold
            nb096AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy068 R q) from (by
          unfold
            nb096AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy065 D R) from (by
          unfold
            nb096AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold
            nb096AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy095 D R) from (by
          unfold
            nb096AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy096 R q) from (by
          unfold
            nb096AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy069 D R) from (by
          unfold
            nb096AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy070 R q) from (by
          unfold
            nb096AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (synCuni (synCuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪ ((Class.cv
        (nb096AlphaDummy053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096SplitAlpha0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D
        R), (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R
        q)), ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069
        D R), (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R), (nb096AlphaDummy054
        R q)), ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D
        R), (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R), (nb096AlphaDummy046
        D R q)), ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D
        R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy051 D
        R) ≠ (nb096AlphaDummy066 D R) from (by
          unfold
            nb096AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy068 R q) from (by
          unfold
            nb096AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy065 D R) from (by
          unfold
            nb096AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold
            nb096AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy095 D R) from (by
          unfold
            nb096AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy096 R q) from (by
          unfold
            nb096AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy069 D R) from (by
          unfold
            nb096AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy070 R q) from (by
          unfold
            nb096AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (synCuni (synCuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪ ((Class.cv
        (nb096AlphaDummy053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096SplitAlpha0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D
        R), (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R
        q)), ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069
        D R), (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R), (nb096AlphaDummy054
        R q)), ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D
        R), (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R), (nb096AlphaDummy046
        D R q)), ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D
        R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
        [((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCcnv (synCdif R (synCid)))
        (nb096WppRefl0015 D R q dv_R_q))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfReflOn
        [((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] D (nb096FocusedRefl0000 D R q dv_D_q)))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((synCuni (Class.cv (nb096AlphaDummy000
        D R)))).fv) (by decide)) (freshVar_injective (((synCuni (Class.cv q))).fv) (by decide))
        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy000 D R))).fv)
        (by decide)) (freshVar_injective (((Class.cv q)).fv) (by decide)) (TAlphaVar.here
        _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy062 D R) from (by
          unfold
            nb096AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy064 q) from (by
          unfold
            nb096AlphaDummy064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy061 D R) from (by
          unfold
            nb096AlphaDummy061;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0058
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy063 q) from (by
          unfold
            nb096AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0059
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy058 D R) from (by
          unfold
            nb096AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy060 q) from (by
          unfold
            nb096AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy057 D R) from (by
          unfold
            nb096AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0056
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy059 q) from (by
          unfold
            nb096AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0057
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy055 D R) from (by
          unfold
            nb096AlphaDummy055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0054
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy056 q) from (by
          unfold
            nb096AlphaDummy056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0055
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy052 D R) from (by
          unfold
            nb096AlphaDummy052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy054 R q) from (by
          unfold
            nb096AlphaDummy054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy051 D R) from (by
          unfold
            nb096AlphaDummy051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0052
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy053 R q) from (by
          unfold
            nb096AlphaDummy053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0053
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy049 D R) from (by
          unfold
            nb096AlphaDummy049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0050
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy050 D R q) from (by
          unfold
            nb096AlphaDummy050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0051
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy047 D R) from (by
          unfold
            nb096AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0048
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy048 D R q) from (by
          unfold
            nb096AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0049
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy045 D R) from (by
          unfold
            nb096AlphaDummy045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0046
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy046 D R q) from (by
          unfold
            nb096AlphaDummy046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0047
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy042 D R) from (by
          unfold
            nb096AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  1)))) (show q ≠ (nb096AlphaDummy044 D R q) from (by
          unfold
            nb096AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy041 D R) from (by
          unfold
            nb096AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0044
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy043 D R q) from (by
          unfold
            nb096AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0045
                    D
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy000 D R) ≠
        (nb096AlphaDummy001 D R) from (by
          unfold
            nb096AlphaDummy001;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0004
                    D
                    R)
                  0)))) (show q ≠ (nb096AlphaDummy002 D R q) from (by
          unfold
            nb096AlphaDummy002;
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
        (nb096SplitAlpha0003 D R q))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy066 D R) from (by
          unfold
            nb096AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy068 R q) from (by
          unfold
            nb096AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy065 D R) from (by
          unfold
            nb096AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold
            nb096AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy095 D R) from (by
          unfold
            nb096AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy096 R q) from (by
          unfold
            nb096AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy069 D R) from (by
          unfold
            nb096AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy070 R q) from (by
          unfold
            nb096AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (synCuni (synCuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪ ((Class.cv
        (nb096AlphaDummy053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096SplitAlpha0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D
        R), (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R
        q)), ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069
        D R), (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R), (nb096AlphaDummy054
        R q)), ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D
        R), (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R), (nb096AlphaDummy046
        D R q)), ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D
        R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb096AlphaDummy051 D
        R) ≠ (nb096AlphaDummy066 D R) from (by
          unfold
            nb096AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  1)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy068 R q) from (by
          unfold
            nb096AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  1)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy065 D R) from (by
          unfold
            nb096AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0088
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy067 R q) from (by
          unfold
            nb096AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0090
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy095 D R) from (by
          unfold
            nb096AlphaDummy095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0092
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy096 R q) from (by
          unfold
            nb096AlphaDummy096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0093
                    R
                    q)
                  0)))) (TAlphaVar.there (show (nb096AlphaDummy051 D R) ≠
        (nb096AlphaDummy069 D R) from (by
          unfold
            nb096AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0089
                    D
                    R)
                  0)))) (show (nb096AlphaDummy053 R q) ≠ (nb096AlphaDummy070 R q) from (by
          unfold
            nb096AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb096_support_mem_0091
                    R
                    q)
                  0)))) (TAlphaVar.there (freshVar_injective (((synCcnv (synCdif R
        (synCid)))).fv ∪ ((synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D
        R)))))).fv) (by
          decide)) (freshVar_injective (((synCcnv (synCdif R (synCid)))).fv ∪ ((synCsn
        (synCuni (synCuni (Class.cv q))))).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb096AlphaDummy052 D R))).fv ∪
        ((Class.cv (nb096AlphaDummy051 D R))).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb096AlphaDummy054 R q))).fv ∪ ((Class.cv
        (nb096AlphaDummy053 R q))).fv) (by
          decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb096SplitAlpha0004 D R q))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb096AlphaDummy097 D R), (nb096AlphaDummy098 R q)), ((nb096AlphaDummy066 D
        R), (nb096AlphaDummy068 R q)), ((nb096AlphaDummy065 D R), (nb096AlphaDummy067 R
        q)), ((nb096AlphaDummy095 D R), (nb096AlphaDummy096 R q)), ((nb096AlphaDummy069
        D R), (nb096AlphaDummy070 R q)), ((nb096AlphaDummy052 D R), (nb096AlphaDummy054
        R q)), ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)), ((nb096AlphaDummy047 D
        R), (nb096AlphaDummy048 D R q)), ((nb096AlphaDummy045 D R), (nb096AlphaDummy046
        D R q)), ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)), ((nb096AlphaDummy001 D
        R), (nb096AlphaDummy002 D R q)), ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))] (synCcompl (synCsn
        (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.reflOfReflOn
        [((nb096AlphaDummy052 D R), (nb096AlphaDummy054 R q)),
        ((nb096AlphaDummy051 D R), (nb096AlphaDummy053 R q)),
        ((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
        (nb096AlphaDummy004 D R q))] (synCcnv (synCdif R (synCid)))
        (nb096WppRefl0015 D R q dv_R_q))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.neg (nb096SplitAlpha0006 D R q))))
                          (TAlphaClass.reflOfReflOn
                            [((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
                              ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
                              ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
                              ((nb096AlphaDummy000 D R), q), ((nb096AlphaDummy003 D R),
                                (nb096AlphaDummy004 D R q))]
                            (synCen) (nb096WppRefl0023 D R q))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
