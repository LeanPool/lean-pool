/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C071C001Block003

/-! NF weak partition development: NAR4C071C001Part007. -/


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

/-- Checked nominal proof certificate identified upstream as `nb071_split_alpha_0011`. -/
@[expose]
noncomputable def nb071SplitAlpha0011 (x : Var) :
    TAlphaWff
      [((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
        ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
        ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
        ((nb071AlphaDummy000), x),
        ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy042))
          (synCuni (Class.cv (nb071AlphaDummy000)))) (Wff.neg
          (Wff.classEq (Class.cv (nb071AlphaDummy041))
            (synCnc (synCpw1 (Class.cv (nb071AlphaDummy042)))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071AlphaDummy044 x)) (synCuni (Class.cv x)))
        (Wff.neg (Wff.classEq (Class.cv (nb071AlphaDummy043 x))
            (synCnc (synCpw1 (Class.cv (nb071AlphaDummy044 x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb071AlphaDummy000))).fv) (by decide))
                (freshVar_injective (((Class.cv x)).fv) (by decide)) (TAlphaVar.here _ _ _))
              (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy052) from
                    (by
                      unfold nb071AlphaDummy052;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0050) 1))))
                  (show x ≠ (nb071AlphaDummy054 x) from (by
                      unfold nb071AlphaDummy054;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0051 x) 1))))
                  (TAlphaVar.there (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy051) from
                      (by
                        unfold nb071AlphaDummy051;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0050) 0))))
                    (show x ≠ (nb071AlphaDummy053 x) from (by
                        unfold nb071AlphaDummy053;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0051 x) 0)))) (TAlphaVar.there
                      (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy042) from (by
                          unfold nb071AlphaDummy042;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0044) 1))))
                      (show x ≠ (nb071AlphaDummy044 x) from (by
                          unfold nb071AlphaDummy044;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0047 x) 1))))
                      (TAlphaVar.there
                        (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy041) from (by
                            unfold nb071AlphaDummy041;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0044) 0))))
                        (show x ≠ (nb071AlphaDummy043 x) from (by
                            unfold nb071AlphaDummy043;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0047 x) 0))))
                        (TAlphaVar.there
                          (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy045) from (by
                              unfold nb071AlphaDummy045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0045) 0))))
                          (show x ≠ (nb071AlphaDummy046 x) from (by
                              unfold nb071AlphaDummy046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0048 x) 0))))
                          (TAlphaVar.there
                            (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy048) from (by
                                unfold nb071AlphaDummy048;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0046) 1))))
                            (show x ≠ (nb071AlphaDummy050 x) from (by
                                unfold nb071AlphaDummy050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0049 x) 1))))
                            (TAlphaVar.there
                              (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy047) from (by
                                  unfold nb071AlphaDummy047;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0046) 0))))
                              (show x ≠ (nb071AlphaDummy049 x) from (by
                                  unfold nb071AlphaDummy049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy001) from (by
                                    unfold nb071AlphaDummy001;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0004) 0))))
                                (show x ≠ (nb071AlphaDummy002 x) from (by
                                    unfold nb071AlphaDummy002;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0005 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((synCuni (Class.cv (nb071AlphaDummy000)))).fv)
              (by decide)) (freshVar_injective (((synCuni (Class.cv x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb071SplitAlpha0005 x)))))))
              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy072) from (by
          unfold nb071AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 1)))) (show (nb071AlphaDummy058 x) ≠
        (nb071AlphaDummy074 x) from (by
          unfold nb071AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 1)))) (TAlphaVar.there (show
        (nb071AlphaDummy056) ≠ (nb071AlphaDummy071) from (by
          unfold nb071AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 0)))) (show (nb071AlphaDummy058 x) ≠
        (nb071AlphaDummy073 x) from (by
          unfold nb071AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy056) ≠ (nb071AlphaDummy077) from (by
          unfold nb071AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0074) 0)))) (show (nb071AlphaDummy058 x) ≠
        (nb071AlphaDummy078 x) from (by
          unfold nb071AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0075 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy075)
        from (by
          unfold nb071AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0071)
                  0)))) (show (nb071AlphaDummy058 x) ≠ (nb071AlphaDummy076 x) from (by
          unfold nb071AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0073 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb071AlphaDummy056))).fv ∪
        ((Class.cv (nb071AlphaDummy055))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb071SplitAlpha0007 x)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy072) from (by
          unfold nb071AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 1)))) (show (nb071AlphaDummy058 x) ≠
        (nb071AlphaDummy074 x) from (by
          unfold nb071AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 1)))) (TAlphaVar.there (show
        (nb071AlphaDummy056) ≠ (nb071AlphaDummy071) from (by
          unfold nb071AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 0)))) (show (nb071AlphaDummy058 x) ≠
        (nb071AlphaDummy073 x) from (by
          unfold nb071AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 0)))) (TAlphaVar.there (show
        (nb071AlphaDummy056) ≠ (nb071AlphaDummy077) from (by
          unfold nb071AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0074) 0)))) (show (nb071AlphaDummy058 x) ≠
        (nb071AlphaDummy078 x) from (by
          unfold nb071AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0075 x)
                  0)))) (TAlphaVar.there (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy075)
        from (by
          unfold nb071AlphaDummy075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0071)
                  0)))) (show (nb071AlphaDummy058 x) ≠ (nb071AlphaDummy076 x) from (by
          unfold nb071AlphaDummy076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0073 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb071AlphaDummy056))).fv ∪
        ((Class.cv (nb071AlphaDummy055))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb071SplitAlpha0007 x)))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb071SplitAlpha0010 x))))))))
                (TAlphaClass.reflOfReflOn
                  [((nb071AlphaDummy056), (nb071AlphaDummy058 x)),
                    ((nb071AlphaDummy055), (nb071AlphaDummy057 x)),
                    ((nb071AlphaDummy042), (nb071AlphaDummy044 x)),
                    ((nb071AlphaDummy041), (nb071AlphaDummy043 x)),
                    ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                    ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                    ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                    ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                    ((nb071AlphaDummy000), x),
                    ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                  (synCen) (nb071WppRefl0017 x)))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_tcfn`. -/
@[expose]
noncomputable def nominalDfTcfn (x : Var) :
    Nominal.NPrf
      (.classEq (synCtcfn) (synCmpt x (synC1c) (synCtc (synCuni (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb071SplitAlpha0004 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb071AlphaDummy000) ≠ (nb071AlphaDummy001) from (by
                          unfold nb071AlphaDummy001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0004) 0))))
                      (show x ≠ (nb071AlphaDummy002 x) from (by
                          unfold nb071AlphaDummy002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0005 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                      ((nb071AlphaDummy000), x),
                      ((nb071AlphaDummy003), (nb071AlphaDummy004 x))]
                    (synC1c) (by simp only [fv_syn_c1c])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                            (freshVar_injective (((Class.cab (nb071AlphaDummy045)
                                  (Wff.classEq (Class.cab (nb071AlphaDummy041) (synWa
                                        (Wff.classMem (Class.cv (nb071AlphaDummy041))
        (synCncs)) (synWrex (nb071AlphaDummy042)
        (synCuni (Class.cv (nb071AlphaDummy000)))
        (Wff.classEq (Class.cv (nb071AlphaDummy041)) (synCnc (synCpw1
        (Class.cv (nb071AlphaDummy042))))))))
                                    (synCsn (Class.cv (nb071AlphaDummy045)))))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cab (nb071AlphaDummy046 x) (Wff.classEq
                                    (Class.cab (nb071AlphaDummy043 x) (synWa
                                        (Wff.classMem (Class.cv (nb071AlphaDummy043 x))
        (synCncs)) (synWrex (nb071AlphaDummy044 x) (synCuni (Class.cv x)) (Wff.classEq
        (Class.cv (nb071AlphaDummy043 x)) (synCnc (synCpw1
        (Class.cv (nb071AlphaDummy044 x))))))))
                                    (synCsn (Class.cv (nb071AlphaDummy046 x)))))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfReflOn [((nb071AlphaDummy041),
        (nb071AlphaDummy043 x)), ((nb071AlphaDummy045), (nb071AlphaDummy046 x)),
                                        ((nb071AlphaDummy048), (nb071AlphaDummy050 x)),
                                        ((nb071AlphaDummy047), (nb071AlphaDummy049 x)),
                                        ((nb071AlphaDummy001), (nb071AlphaDummy002 x)),
                                        ((nb071AlphaDummy000), x), ((nb071AlphaDummy003),
        (nb071AlphaDummy004 x))] (synCncs) (nb071WppRefl0008 x))) (TAlphaWff.ex
                                    (TAlphaWff.neg (nb071SplitAlpha0011 x)))))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb071AlphaDummy045) ≠ (nb071AlphaDummy107) from
                                        (by
                                          unfold nb071AlphaDummy107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0108)
                                                  0)))) (show (nb071AlphaDummy046 x) ≠
        (nb071AlphaDummy108 x) from (by
                                          unfold nb071AlphaDummy108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0109 x) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
