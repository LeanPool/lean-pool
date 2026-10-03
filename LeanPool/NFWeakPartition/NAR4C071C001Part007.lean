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

@[expose]
noncomputable def nb071_split_alpha_0011 (x : Var) :
    TAlphaWff
      [((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
        ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
        ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
        ((nb071_alpha_dummy_000), x),
        ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_042))
          (syn_cuni (Class.cv (nb071_alpha_dummy_000)))) (Wff.neg
          (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
            (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))
      (Wff.imp (Wff.classMem (Class.cv (nb071_alpha_dummy_044 x)) (syn_cuni (Class.cv x)))
        (Wff.neg (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
            (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv) (by decide))
                (freshVar_injective (((Class.cv x)).fv) (by decide)) (TAlphaVar.here _ _ _))
              (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_052) from
                    (by
                      unfold nb071_alpha_dummy_052;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0050) 1))))
                  (show x ≠ (nb071_alpha_dummy_054 x) from (by
                      unfold nb071_alpha_dummy_054;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0051 x) 1))))
                  (TAlphaVar.there (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_051) from
                      (by
                        unfold nb071_alpha_dummy_051;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0050) 0))))
                    (show x ≠ (nb071_alpha_dummy_053 x) from (by
                        unfold nb071_alpha_dummy_053;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb071_support_mem_0051 x) 0)))) (TAlphaVar.there
                      (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_042) from (by
                          unfold nb071_alpha_dummy_042;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0044) 1))))
                      (show x ≠ (nb071_alpha_dummy_044 x) from (by
                          unfold nb071_alpha_dummy_044;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0047 x) 1))))
                      (TAlphaVar.there
                        (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_041) from (by
                            unfold nb071_alpha_dummy_041;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0044) 0))))
                        (show x ≠ (nb071_alpha_dummy_043 x) from (by
                            unfold nb071_alpha_dummy_043;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb071_support_mem_0047 x) 0))))
                        (TAlphaVar.there
                          (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_045) from (by
                              unfold nb071_alpha_dummy_045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0045) 0))))
                          (show x ≠ (nb071_alpha_dummy_046 x) from (by
                              unfold nb071_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb071_support_mem_0048 x) 0))))
                          (TAlphaVar.there
                            (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_048) from (by
                                unfold nb071_alpha_dummy_048;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0046) 1))))
                            (show x ≠ (nb071_alpha_dummy_050 x) from (by
                                unfold nb071_alpha_dummy_050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb071_support_mem_0049 x) 1))))
                            (TAlphaVar.there
                              (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_047) from (by
                                  unfold nb071_alpha_dummy_047;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0046) 0))))
                              (show x ≠ (nb071_alpha_dummy_049 x) from (by
                                  unfold nb071_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb071_support_mem_0049 x) 0))))
                              (TAlphaVar.there
                                (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_001) from (by
                                    unfold nb071_alpha_dummy_001;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0004) 0))))
                                (show x ≠ (nb071_alpha_dummy_002 x) from (by
                                    unfold nb071_alpha_dummy_002;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb071_support_mem_0005 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv)
              (by decide)) (freshVar_injective (((syn_cuni (Class.cv x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0005 x)))))))
              (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_072) from (by
          unfold nb071_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 1)))) (show (nb071_alpha_dummy_058 x) ≠
        (nb071_alpha_dummy_074 x) from (by
          unfold nb071_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 1)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_071) from (by
          unfold nb071_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 0)))) (show (nb071_alpha_dummy_058 x) ≠
        (nb071_alpha_dummy_073 x) from (by
          unfold nb071_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_077) from (by
          unfold nb071_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0074) 0)))) (show (nb071_alpha_dummy_058 x) ≠
        (nb071_alpha_dummy_078 x) from (by
          unfold nb071_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0075 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_075)
        from (by
          unfold nb071_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0071)
                  0)))) (show (nb071_alpha_dummy_058 x) ≠ (nb071_alpha_dummy_076 x) from (by
          unfold nb071_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0073 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_056))).fv ∪
        ((Class.cv (nb071_alpha_dummy_055))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb071_split_alpha_0007 x)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_072) from (by
          unfold nb071_alpha_dummy_072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 1)))) (show (nb071_alpha_dummy_058 x) ≠
        (nb071_alpha_dummy_074 x) from (by
          unfold nb071_alpha_dummy_074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 1)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_071) from (by
          unfold nb071_alpha_dummy_071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0070) 0)))) (show (nb071_alpha_dummy_058 x) ≠
        (nb071_alpha_dummy_073 x) from (by
          unfold nb071_alpha_dummy_073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0072 x) 0)))) (TAlphaVar.there (show
        (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_077) from (by
          unfold nb071_alpha_dummy_077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0074) 0)))) (show (nb071_alpha_dummy_058 x) ≠
        (nb071_alpha_dummy_078 x) from (by
          unfold nb071_alpha_dummy_078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0075 x)
                  0)))) (TAlphaVar.there (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_075)
        from (by
          unfold nb071_alpha_dummy_075;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0071)
                  0)))) (show (nb071_alpha_dummy_058 x) ≠ (nb071_alpha_dummy_076 x) from (by
          unfold nb071_alpha_dummy_076;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb071_support_mem_0073 x)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb071_alpha_dummy_056))).fv ∪
        ((Class.cv (nb071_alpha_dummy_055))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb071_split_alpha_0007 x)))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb071_split_alpha_0010 x))))))))
                (TAlphaClass.refl_of_reflOn
                  [((nb071_alpha_dummy_056), (nb071_alpha_dummy_058 x)),
                    ((nb071_alpha_dummy_055), (nb071_alpha_dummy_057 x)),
                    ((nb071_alpha_dummy_042), (nb071_alpha_dummy_044 x)),
                    ((nb071_alpha_dummy_041), (nb071_alpha_dummy_043 x)),
                    ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                    ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                    ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                    ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                    ((nb071_alpha_dummy_000), x),
                    ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                  (syn_cen) (nb071_wpp_refl_0017 x)))))))))

@[expose]
noncomputable def nominal_df_tcfn (x : Var) :
    Nominal.NPrf
      (.classEq (syn_ctcfn) (syn_cmpt x (syn_c1c) (syn_ctc (syn_cuni (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb071_split_alpha_0004 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_001) from (by
                          unfold nb071_alpha_dummy_001;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0004) 0))))
                      (show x ≠ (nb071_alpha_dummy_002 x) from (by
                          unfold nb071_alpha_dummy_002;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb071_support_mem_0005 x) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                      ((nb071_alpha_dummy_000), x),
                      ((nb071_alpha_dummy_003), (nb071_alpha_dummy_004 x))]
                    (syn_c1c) (by simp only [fv_syn_c1c])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                            (freshVar_injective (((Class.cab (nb071_alpha_dummy_045)
                                  (Wff.classEq (Class.cab (nb071_alpha_dummy_041) (syn_wa
                                        (Wff.classMem (Class.cv (nb071_alpha_dummy_041))
        (syn_cncs)) (syn_wrex (nb071_alpha_dummy_042)
        (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
        (Wff.classEq (Class.cv (nb071_alpha_dummy_041)) (syn_cnc (syn_cpw1
        (Class.cv (nb071_alpha_dummy_042))))))))
                                    (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq
                                    (Class.cab (nb071_alpha_dummy_043 x) (syn_wa
                                        (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x))
        (syn_cncs)) (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x)) (Wff.classEq
        (Class.cv (nb071_alpha_dummy_043 x)) (syn_cnc (syn_cpw1
        (Class.cv (nb071_alpha_dummy_044 x))))))))
                                    (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_reflOn [((nb071_alpha_dummy_041),
        (nb071_alpha_dummy_043 x)), ((nb071_alpha_dummy_045), (nb071_alpha_dummy_046 x)),
                                        ((nb071_alpha_dummy_048), (nb071_alpha_dummy_050 x)),
                                        ((nb071_alpha_dummy_047), (nb071_alpha_dummy_049 x)),
                                        ((nb071_alpha_dummy_001), (nb071_alpha_dummy_002 x)),
                                        ((nb071_alpha_dummy_000), x), ((nb071_alpha_dummy_003),
        (nb071_alpha_dummy_004 x))] (syn_cncs) (nb071_wpp_refl_0008 x))) (TAlphaWff.ex
                                    (TAlphaWff.neg (nb071_split_alpha_0011 x)))))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb071_alpha_dummy_045) ≠ (nb071_alpha_dummy_107) from
                                        (by
                                          unfold nb071_alpha_dummy_107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb071_support_mem_0108)
                                                  0)))) (show (nb071_alpha_dummy_046 x) ≠
        (nb071_alpha_dummy_108 x) from (by
                                          unfold nb071_alpha_dummy_108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb071_support_mem_0109 x) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
