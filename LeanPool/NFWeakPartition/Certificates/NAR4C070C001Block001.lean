/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C070C001Part002Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C070C001Part002`. -/


section

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
noncomputable def nb070_power_variable_occurrence (x : Var) (A : Class) (b : Var) :
    TAlphaClass
      [((nb070_alpha_dummy_022 A), (nb070_alpha_dummy_023 x)),
        ((nb070_alpha_dummy_020 A), (nb070_alpha_dummy_021 x)),
        ((nb070_alpha_dummy_018 A), (nb070_alpha_dummy_019 x)),
        ((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)),
        ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)),
        ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Class.cv (nb070_alpha_dummy_001 A)) (Class.cv x) :=
  by
  have freshness0 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_022 A) :=
    by
    unfold nb070_alpha_dummy_022
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0016 A) 0))
  have freshness1 : x ≠ (nb070_alpha_dummy_023 x) :=
    by
    unfold nb070_alpha_dummy_023
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0017 x) 0))
  have freshness2 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_020 A) :=
    by
    unfold nb070_alpha_dummy_020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0014 A) 0))
  have freshness3 : x ≠ (nb070_alpha_dummy_021 x) :=
    by
    unfold nb070_alpha_dummy_021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0015 x) 0))
  have freshness4 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_018 A) :=
    by
    unfold nb070_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0012 A) 0))
  have freshness5 : x ≠ (nb070_alpha_dummy_019 x) :=
    by
    unfold nb070_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0013 x) 0))
  have freshness6 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_016 A) :=
    by
    unfold nb070_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0010 A) 0))
  have freshness7 : x ≠ (nb070_alpha_dummy_017 x) :=
    by
    unfold nb070_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0011 x) 0))
  have freshness8 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_014 A) :=
    by
    unfold nb070_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0008 A) 0))
  have freshness9 : x ≠ (nb070_alpha_dummy_015 x) :=
    by
    unfold nb070_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0009 x) 0))
  have freshness10 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_012 A) :=
    by
    unfold nb070_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0006 A) 0))
  have freshness11 : x ≠ (nb070_alpha_dummy_013 x) :=
    by
    unfold nb070_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0007 x) 0))
  have freshness12 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_009 A) :=
    by
    unfold nb070_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 1))
  have freshness13 : x ≠ (nb070_alpha_dummy_011 x) :=
    by
    unfold nb070_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 1))
  have freshness14 : (nb070_alpha_dummy_001 A) ≠ (nb070_alpha_dummy_008 A) :=
    by
    unfold nb070_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0004 A) 0))
  have freshness15 : x ≠ (nb070_alpha_dummy_010 x) :=
    by
    unfold nb070_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0005 x) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15 (TAlphaVar.here _ _ _))))))))))

@[expose]
noncomputable def nb070_split_alpha_0000 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)),
        ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_014 A))
          (syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb070_alpha_dummy_014 A))
            (syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c)))))
      (Wff.imp (Wff.classMem (Class.cv (nb070_alpha_dummy_015 x))
          (syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (nb070_alpha_dummy_015 x))
            (syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0002 A) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0003 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (nb070_power_variable_occurrence x A b))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0002 A) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0003 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (nb070_power_variable_occurrence x A b)))))))))
                  (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_closed
                [((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)),
                  ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)),
                  ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)),
                  ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                  ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                  ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                  ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                  ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                  ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                (syn_c1c) (by simp only [fv_syn_c1c]))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (nb070_power_variable_occurrence x A b))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0002 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0003 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0000 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb070_support_mem_0001 x) 0)) (TAlphaVar.here _ _ _)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (nb070_power_variable_occurrence x A b)))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb070_alpha_dummy_016 A), (nb070_alpha_dummy_017 x)),
                    ((nb070_alpha_dummy_014 A), (nb070_alpha_dummy_015 x)),
                    ((nb070_alpha_dummy_012 A), (nb070_alpha_dummy_013 x)),
                    ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                    ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                    ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                    ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                    ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                    ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                  (syn_c1c) (by simp only [fv_syn_c1c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C070C001Part003`. -/


section

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
noncomputable def nb070_split_alpha_0001 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)),
        ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)),
        ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)),
        ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
        ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
        ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
        ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
        ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
        ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)),
        ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070_alpha_dummy_038 A))
            (syn_cun (Class.cv (nb070_alpha_dummy_039 A))
              (Class.cv (nb070_alpha_dummy_040 A))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070_alpha_dummy_041 x))
            (syn_cun (Class.cv (nb070_alpha_dummy_042 x))
              (Class.cv (nb070_alpha_dummy_043 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)),
          ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)),
          ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)),
          ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
          ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
          ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
          ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
          ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
          ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)),
          ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
          ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
          ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
          ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
          ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
          ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
          ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_050 A) from (by
                                unfold nb070_alpha_dummy_050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_051 x) from (by
                                unfold nb070_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_050 A) from (by
                                unfold nb070_alpha_dummy_050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_051 x) from (by
                                unfold nb070_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_052 A) from (by
                                unfold nb070_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_053 x) from (by
                                unfold nb070_alpha_dummy_053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_052 A) from (by
                                unfold nb070_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_053 x) from (by
                                unfold nb070_alpha_dummy_053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb070_split_alpha_0002 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
        ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
        ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)),
        ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
        (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))
      (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
        (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪
            ((Class.cv (nb070_alpha_dummy_008 A))).fv) (by decide)) (freshVar_injective
          (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪
            ((Class.cv (nb070_alpha_dummy_010 x))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb070_alpha_dummy_025 A) ≠ (nb070_alpha_dummy_032 A) from
                  (by
                    unfold nb070_alpha_dummy_032;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 0))))
                (show (nb070_alpha_dummy_027 x) ≠ (nb070_alpha_dummy_034 x) from (by
                    unfold nb070_alpha_dummy_034;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 0))))
                (TAlphaVar.there
                  (show (nb070_alpha_dummy_025 A) ≠ (nb070_alpha_dummy_033 A) from (by
                      unfold nb070_alpha_dummy_033;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0024 A) 1))))
                  (show (nb070_alpha_dummy_027 x) ≠ (nb070_alpha_dummy_035 x) from (by
                      unfold nb070_alpha_dummy_035;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb070_support_mem_0025 x) 1))))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb070_alpha_dummy_025 A))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb070_alpha_dummy_027 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_039 A) from
                                    (by
                                      unfold nb070_alpha_dummy_039;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0028 A)
                                              1)))) (show
                                    (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_042 x) from
                                    (by
                                      unfold nb070_alpha_dummy_042;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb070_support_mem_0029 x)
                                              1)))) (TAlphaVar.there (show
                                      (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_038 A) from
                                      (by
                                        unfold nb070_alpha_dummy_038;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb070_support_mem_0028 A)
                                                0)))) (show (nb070_alpha_dummy_034 x) ≠
                                        (nb070_alpha_dummy_041 x) from (by
                                        unfold nb070_alpha_dummy_041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb070_support_mem_0029 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A)
                                        from (by
                                          unfold nb070_alpha_dummy_036;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb070_support_mem_0026 A) 0)))) (show
                                        (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x)
                                        from (by
                                          unfold nb070_alpha_dummy_037;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb070_support_mem_0027 x) 0))))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb070_alpha_dummy_040 A),
                                        (nb070_alpha_dummy_043 x)), ((nb070_alpha_dummy_039 A),
                                        (nb070_alpha_dummy_042 x)), ((nb070_alpha_dummy_038 A),
                                        (nb070_alpha_dummy_041 x)), ((nb070_alpha_dummy_036 A),
                                        (nb070_alpha_dummy_037 x)), ((nb070_alpha_dummy_032 A),
                                        (nb070_alpha_dummy_034 x)), ((nb070_alpha_dummy_033 A),
                                        (nb070_alpha_dummy_035 x)), ((nb070_alpha_dummy_025 A),
                                        (nb070_alpha_dummy_027 x)), ((nb070_alpha_dummy_024 A),
                                        (nb070_alpha_dummy_026 x)), ((nb070_alpha_dummy_030 A),
                                        (nb070_alpha_dummy_031 x)), ((nb070_alpha_dummy_028 A),
                                        (nb070_alpha_dummy_029 x)), ((nb070_alpha_dummy_009 A),
                                        (nb070_alpha_dummy_011 x)), ((nb070_alpha_dummy_008 A),
                                        (nb070_alpha_dummy_010 x)),
                                      ((nb070_alpha_dummy_001 A), x),
                                      ((nb070_alpha_dummy_000 A), b),
                                      ((nb070_alpha_dummy_002 A),
                                        (nb070_alpha_dummy_003 x A b)),
                                      ((nb070_alpha_dummy_005 A),
                                        (nb070_alpha_dummy_007 x A b)),
                                      ((nb070_alpha_dummy_004 A),
                                        (nb070_alpha_dummy_006 x A b))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb070_split_alpha_0001 x A b))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from (by
                              unfold nb070_alpha_dummy_036;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                          (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from (by
                              unfold nb070_alpha_dummy_037;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
                          ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
                          ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
                          ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                          ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                          ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)),
                          ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                          ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                          ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                          ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                          ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                          ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                          ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from (by
                            unfold nb070_alpha_dummy_036;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                        (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from (by
                            unfold nb070_alpha_dummy_037;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (show (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_036 A) from (by
                              unfold nb070_alpha_dummy_036;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0026 A) 0))))
                          (show (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_037 x) from (by
                              unfold nb070_alpha_dummy_037;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0027 x) 0))))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
                          ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
                          ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
                          ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
                          ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
                          ((nb070_alpha_dummy_030 A), (nb070_alpha_dummy_031 x)),
                          ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
                          ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
                          ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
                          ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
                          ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
                          ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
                          ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb070_split_alpha_0003 (x : Var) (A : Class) (b : Var) :
    TAlphaWff
      [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)),
        ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)),
        ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)),
        ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
        ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
        ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
        ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)),
        ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
        ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
        ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
        ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
        ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
        ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
        ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
        ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
        ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
        ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
        ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070_alpha_dummy_038 A))
            (syn_cun (Class.cv (nb070_alpha_dummy_039 A))
              (Class.cv (nb070_alpha_dummy_040 A))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb070_alpha_dummy_041 x))
            (syn_cun (Class.cv (nb070_alpha_dummy_042 x))
              (Class.cv (nb070_alpha_dummy_043 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0032 A) 0))))
                          (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0033 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0030 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0031 x) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_046 A) from (by
                              unfold nb070_alpha_dummy_046;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0036 A) 0))))
                          (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_047 x) from (by
                              unfold nb070_alpha_dummy_047;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb070_support_mem_0037 x) 0))))
                          (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_044 A) from (by
                                unfold nb070_alpha_dummy_044;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0034 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_045 x) from (by
                                unfold nb070_alpha_dummy_045;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0035 x) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb070_alpha_dummy_040 A), (nb070_alpha_dummy_043 x)),
          ((nb070_alpha_dummy_039 A), (nb070_alpha_dummy_042 x)),
          ((nb070_alpha_dummy_038 A), (nb070_alpha_dummy_041 x)),
          ((nb070_alpha_dummy_036 A), (nb070_alpha_dummy_037 x)),
          ((nb070_alpha_dummy_032 A), (nb070_alpha_dummy_034 x)),
          ((nb070_alpha_dummy_033 A), (nb070_alpha_dummy_035 x)),
          ((nb070_alpha_dummy_058 A), (nb070_alpha_dummy_059 x)),
          ((nb070_alpha_dummy_056 A), (nb070_alpha_dummy_057 x)),
          ((nb070_alpha_dummy_025 A), (nb070_alpha_dummy_027 x)),
          ((nb070_alpha_dummy_024 A), (nb070_alpha_dummy_026 x)),
          ((nb070_alpha_dummy_054 A), (nb070_alpha_dummy_055 x)),
          ((nb070_alpha_dummy_028 A), (nb070_alpha_dummy_029 x)),
          ((nb070_alpha_dummy_009 A), (nb070_alpha_dummy_011 x)),
          ((nb070_alpha_dummy_008 A), (nb070_alpha_dummy_010 x)),
          ((nb070_alpha_dummy_001 A), x), ((nb070_alpha_dummy_000 A), b),
          ((nb070_alpha_dummy_002 A), (nb070_alpha_dummy_003 x A b)),
          ((nb070_alpha_dummy_005 A), (nb070_alpha_dummy_007 x A b)),
          ((nb070_alpha_dummy_004 A), (nb070_alpha_dummy_006 x A b))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_050 A) from (by
                                unfold nb070_alpha_dummy_050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_051 x) from (by
                                unfold nb070_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_050 A) from (by
                                unfold nb070_alpha_dummy_050;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0040 A) 0))))
                            (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_051 x) from (by
                                unfold nb070_alpha_dummy_051;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0041 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0038 A) 0))))
                              (show (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0039 x) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_052 A) from (by
                                unfold nb070_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_053 x) from (by
                                unfold nb070_alpha_dummy_053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_052 A) from (by
                                unfold nb070_alpha_dummy_052;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0044 A) 0))))
                            (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_053 x) from (by
                                unfold nb070_alpha_dummy_053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb070_support_mem_0045 x) 0))))
                            (TAlphaVar.there
                              (show (nb070_alpha_dummy_040 A) ≠ (nb070_alpha_dummy_048 A) from
                                (by
                                  unfold nb070_alpha_dummy_048;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0042 A) 0))))
                              (show (nb070_alpha_dummy_043 x) ≠ (nb070_alpha_dummy_049 x) from
                                (by
                                  unfold nb070_alpha_dummy_049;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb070_support_mem_0043 x) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
