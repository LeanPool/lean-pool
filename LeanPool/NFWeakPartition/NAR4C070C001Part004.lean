/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C070C001Part004Stage1


/-! NF weak partition development: NAR4C070C001Part004. -/


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

/-- Checked nominal proof certificate identified upstream as `nb070_wpp_refl_0010`. -/
@[expose]
noncomputable def nb070WppRefl0010 (x : Var) (A : Class) (b : Var) :
    TReflOn
      [((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
        ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
        ((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
        ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
        ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      ((synCen)).fv :=
  TEnvFresh.reflOn (nb070_compact_envfresh_0010 x A b)

/-- Checked nominal proof certificate identified upstream as `nb070_split_alpha_0006`. -/
@[expose]
noncomputable def nb070SplitAlpha0006 (x : Var) (A : Class) (b : Var)
    (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_b_x : b ≠ x) :
    TAlphaWff
      [((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
        ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
      (Wff.imp (Wff.objMem (nb070AlphaDummy004 A) (nb070AlphaDummy005 A)) (Wff.neg
          (Wff.classMem (Class.cv (nb070AlphaDummy005 A))
            (Class.cab (nb070AlphaDummy002 A) (Wff.classEq
                (Class.cab (nb070AlphaDummy000 A)
                  (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                    (synWrex (nb070AlphaDummy001 A) A
                      (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                        (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
                (synCsn (Class.cv (nb070AlphaDummy002 A))))))))
      (Wff.imp (Wff.objMem (nb070AlphaDummy006 x A b) (nb070AlphaDummy007 x A b)) (Wff.neg
          (Wff.classMem (Class.cv (nb070AlphaDummy007 x A b))
            (Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
                  (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                      (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
                (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))))) :=
  (TAlphaWff.imp (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
          (((Class.cab (nb070AlphaDummy002 A) (Wff.classEq
                (Class.cab (nb070AlphaDummy000 A)
                  (synWa (Wff.classMem (Class.cv (nb070AlphaDummy000 A)) (synCncs))
                    (synWrex (nb070AlphaDummy001 A) A
                      (Wff.classEq (Class.cv (nb070AlphaDummy000 A))
                        (synCnc (synCpw1 (Class.cv (nb070AlphaDummy001 A))))))))
                (synCsn (Class.cv (nb070AlphaDummy002 A)))))).fv) (by decide))
        (freshVar_injective (((Class.cab (nb070AlphaDummy003 x A b) (Wff.classEq (Class.cab b
                  (synWa (Wff.classMem (Class.cv b) (synCncs)) (synWrex x A
                      (Wff.classEq (Class.cv b) (synCnc (synCpw1 (Class.cv x)))))))
                (synCsn (Class.cv (nb070AlphaDummy003 x A b)))))).fv) (by decide))
        (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfReflOn [((nb070AlphaDummy000 A), b),
                      ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                      ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                      ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                    (synCncs) (nb070WppRefl0000 x A b))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfReflOn
                        [((nb070AlphaDummy001 A), x), ((nb070AlphaDummy000 A), b),
                          ((nb070AlphaDummy002 A), (nb070AlphaDummy003 x A b)),
                          ((nb070AlphaDummy005 A), (nb070AlphaDummy007 x A b)),
                          ((nb070AlphaDummy004 A), (nb070AlphaDummy006 x A b))]
                        A (nb070WppRefl0001 x A b dv_A_b dv_A_x))) (TAlphaWff.classEq
                      (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_b_x
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg
                                      (TAlphaWff.neg (nb070SplitAlpha0000 x A b)))))))
                            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb070AlphaDummy009 A) ≠ (nb070AlphaDummy025 A) from (by
          unfold
            nb070AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  1)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy027 x) from (by
          unfold
            nb070AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  1)))) (TAlphaVar.there (show (nb070AlphaDummy009 A) ≠
        (nb070AlphaDummy024 A) from (by
          unfold
            nb070AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  0)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy026 x) from (by
          unfold
            nb070AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  0)))) (TAlphaVar.there (show (nb070AlphaDummy009 A) ≠
        (nb070AlphaDummy030 A) from (by
          unfold
            nb070AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0022
                    A)
                  0)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy031 x) from (by
          unfold
            nb070AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0023
                    x)
                  0)))) (TAlphaVar.there (show (nb070AlphaDummy009 A) ≠
        (nb070AlphaDummy028 A) from (by
          unfold
            nb070AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0019
                    A)
                  0)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy029 x) from (by
          unfold
            nb070AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0021
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb070SplitAlpha0002 x A b)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb070AlphaDummy009 A) ≠ (nb070AlphaDummy025 A) from (by
          unfold
            nb070AlphaDummy025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  1)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy027 x) from (by
          unfold
            nb070AlphaDummy027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  1)))) (TAlphaVar.there (show (nb070AlphaDummy009 A) ≠
        (nb070AlphaDummy024 A) from (by
          unfold
            nb070AlphaDummy024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0018
                    A)
                  0)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy026 x) from (by
          unfold
            nb070AlphaDummy026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0020
                    x)
                  0)))) (TAlphaVar.there (show (nb070AlphaDummy009 A) ≠
        (nb070AlphaDummy030 A) from (by
          unfold
            nb070AlphaDummy030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0022
                    A)
                  0)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy031 x) from (by
          unfold
            nb070AlphaDummy031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0023
                    x)
                  0)))) (TAlphaVar.there (show (nb070AlphaDummy009 A) ≠
        (nb070AlphaDummy028 A) from (by
          unfold
            nb070AlphaDummy028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0019
                    A)
                  0)))) (show (nb070AlphaDummy011 x) ≠ (nb070AlphaDummy029 x) from (by
          unfold
            nb070AlphaDummy029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb070_support_mem_0021
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb070SplitAlpha0002 x A b)))))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb070SplitAlpha0005 x A b)))))))) (TAlphaClass.reflOfReflOn
                                [((nb070AlphaDummy009 A), (nb070AlphaDummy011 x)),
                                  ((nb070AlphaDummy008 A), (nb070AlphaDummy010 x)),
                                  ((nb070AlphaDummy001 A), x),
                                  ((nb070AlphaDummy000 A), b), ((nb070AlphaDummy002 A),
                                    (nb070AlphaDummy003 x A b)), ((nb070AlphaDummy005 A),
                                    (nb070AlphaDummy007 x A b)), ((nb070AlphaDummy004 A),
                                    (nb070AlphaDummy006 x A b))]
                                (synCen) (nb070WppRefl0010 x A b))))))))))) (TAlphaClass.cab
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb070AlphaDummy002 A) ≠ (nb070AlphaDummy060 A) from (by
                        unfold nb070AlphaDummy060;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0056 A) 0))))
                    (show (nb070AlphaDummy003 x A b) ≠ (nb070AlphaDummy061 x A b) from (by
                        unfold nb070AlphaDummy061;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb070_support_mem_0057 x A b) 0))))
                    (TAlphaVar.here _ _ _))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_tc`. -/
@[expose]
noncomputable def nominalDfTc (x : Var) (A : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_b_x : b ≠ x) :
    Nominal.NPrf
      (.classEq (synCtc A) (synCio b (synWa (.classMem (.cv b) (synCncs))
            (synWrex x A (.classEq (.cv b) (synCnc (synCpw1 (.cv x)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex
          (TAlphaWff.neg (nb070SplitAlpha0006 x A b dv_A_b dv_A_x dv_b_x))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
