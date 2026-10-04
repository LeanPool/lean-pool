/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C076C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C076C001Part008`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0002`. -/
@[expose]
noncomputable def nb076SplitAlpha0002 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_m_n : m ≠ n) :
    TAlphaWff
      [((nb076AlphaDummy015), (nb076AlphaDummy016 g m n a b)),
        ((nb076AlphaDummy013), (nb076AlphaDummy014 g m n a b)),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy015))
          (Class.cab (nb076AlphaDummy009) (synWrex (nb076AlphaDummy010)
              (synCop (Class.cv (nb076AlphaDummy003)) (Class.cv (nb076AlphaDummy004)))
              (Wff.classEq (Class.cv (nb076AlphaDummy009))
                (synCphi (Class.cv (nb076AlphaDummy010))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy015)) (Class.cab (nb076AlphaDummy009)
              (synWrex (nb076AlphaDummy010) (synCop (Class.cv (nb076AlphaDummy003))
                  (Class.cv (nb076AlphaDummy004)))
                (Wff.classEq (Class.cv (nb076AlphaDummy009))
                  (synCphi (Class.cv (nb076AlphaDummy010)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy016 g m n a b))
          (Class.cab (nb076AlphaDummy011 g m n a b)
            (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb076AlphaDummy016 g m n a b))
            (Class.cab (nb076AlphaDummy011 g m n a b)
              (synWrex (nb076AlphaDummy012 g m n a b) (synCop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
                  (synCphi (Class.cv (nb076AlphaDummy012 g m n a b))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg
                          (TAlphaWff.neg (nb076SplitAlpha0000 g m n a b dv_m_n)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb076AlphaDummy004) ≠
        (nb076AlphaDummy018) from (by
          unfold nb076AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076AlphaDummy020 m n) from (by
          unfold nb076AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 0)))) (TAlphaVar.there (show
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy047) from (by
          unfold nb076AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076AlphaDummy048 m n) from (by
          unfold nb076AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy021)
        from (by
          unfold nb076AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051) 0)))) (show n ≠ (nb076AlphaDummy022 m n) from (by
          unfold nb076AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy010)
        from (by
          unfold nb076AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076AlphaDummy012 g m n a b) from (by
          unfold nb076AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g m
                    n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy009)
        from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy015)
        from (by
          unfold nb076AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076AlphaDummy016 g m n a b) from (by
          unfold nb076AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy013)
        from (by
          unfold nb076AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076AlphaDummy014 g m n a b) from (by
          unfold nb076AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy005)
        from (by
          unfold
            nb076AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076AlphaDummy006 g m n a b) from (by
          unfold
            nb076AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv)
        (by decide)) (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076SplitAlpha0001 g m n a b)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb076AlphaDummy004) ≠
        (nb076AlphaDummy018) from (by
          unfold nb076AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076AlphaDummy020 m n) from (by
          unfold nb076AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 0)))) (TAlphaVar.there (show
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy047) from (by
          unfold nb076AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076AlphaDummy048 m n) from (by
          unfold nb076AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy021)
        from (by
          unfold nb076AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051) 0)))) (show n ≠ (nb076AlphaDummy022 m n) from (by
          unfold nb076AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy010)
        from (by
          unfold nb076AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076AlphaDummy012 g m n a b) from (by
          unfold nb076AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g m
                    n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy009)
        from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy015)
        from (by
          unfold nb076AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076AlphaDummy016 g m n a b) from (by
          unfold nb076AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy013)
        from (by
          unfold nb076AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076AlphaDummy014 g m n a b) from (by
          unfold nb076AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy005)
        from (by
          unfold
            nb076AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076AlphaDummy006 g m n a b) from (by
          unfold
            nb076AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076AlphaDummy003))).fv ∪ ((Class.cv (nb076AlphaDummy004))).fv)
        (by decide)) (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076SplitAlpha0001 g m n a b))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((synCop (Class.cv (nb076AlphaDummy003))
                          (Class.cv (nb076AlphaDummy004)))).fv ∪
                      ((Class.cv (nb076AlphaDummy005))).fv) (by decide)) (freshVar_injective
                    (((synCop (Class.cv m) (Class.cv n))).fv ∪
                      ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb076AlphaDummy010) ≠ (nb076AlphaDummy053) from (by
                              unfold nb076AlphaDummy053;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0060) 0)))) (show
                            (nb076AlphaDummy012 g m n a b) ≠
                              (nb076AlphaDummy055 g m n a b) from (by
                              unfold nb076AlphaDummy055;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb076_support_mem_0061 g m n a b)
                                      0)))) (TAlphaVar.there
                            (show (nb076AlphaDummy010) ≠ (nb076AlphaDummy054) from (by
                                unfold nb076AlphaDummy054;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0060) 1)))) (show
                              (nb076AlphaDummy012 g m n a b) ≠
                                (nb076AlphaDummy056 g m n a b) from (by
                                unfold nb076AlphaDummy056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0061 g m n a b)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb076AlphaDummy010))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy060) from (by
          unfold nb076AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 1)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy063 g m n a b) from (by
          unfold nb076AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy059)
        from (by
          unfold nb076AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy062 g m n a b) from (by
          unfold nb076AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy067)
        from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy067)
        from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy071) from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072
        g m n a b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy071)
        from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072
        g m n a b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074
        g m n a b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074
        g m n a b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from (by
                                        unfold nb076AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0062)
                                                0)))) (show (nb076AlphaDummy055 g m n a b) ≠
                                        (nb076AlphaDummy058 g m n a b) from (by
                                        unfold nb076AlphaDummy058;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0063 g m n a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy057), (nb076AlphaDummy058 g m n a b)),
                                    ((nb076AlphaDummy053),
                                      (nb076AlphaDummy055 g m n a b)),
                                    ((nb076AlphaDummy054),
                                      (nb076AlphaDummy056 g m n a b)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from
                                    (by
                                      unfold nb076AlphaDummy057;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb076_support_mem_0062)
                                              0)))) (show (nb076AlphaDummy055 g m n a b) ≠
                                      (nb076AlphaDummy058 g m n a b) from (by
                                      unfold nb076AlphaDummy058;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb076_support_mem_0063 g m n a b) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from (by
                                        unfold nb076AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0062)
                                                0)))) (show (nb076AlphaDummy055 g m n a b) ≠
                                        (nb076AlphaDummy058 g m n a b) from (by
                                        unfold nb076AlphaDummy058;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0063 g m n a b) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb076AlphaDummy057), (nb076AlphaDummy058 g m n a b)),
                                    ((nb076AlphaDummy053),
                                      (nb076AlphaDummy055 g m n a b)),
                                    ((nb076AlphaDummy054),
                                      (nb076AlphaDummy056 g m n a b)),
                                    ((nb076AlphaDummy010),
                                      (nb076AlphaDummy012 g m n a b)),
                                    ((nb076AlphaDummy009),
                                      (nb076AlphaDummy011 g m n a b)),
                                    ((nb076AlphaDummy015),
                                      (nb076AlphaDummy016 g m n a b)),
                                    ((nb076AlphaDummy013),
                                      (nb076AlphaDummy014 g m n a b)),
                                    ((nb076AlphaDummy005),
                                      (nb076AlphaDummy006 g m n a b)),
                                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                                    ((nb076AlphaDummy007),
                                      (nb076AlphaDummy008 g m n a b))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb076SplitAlpha0000 g m n a b dv_m_n)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy018) from (by
          unfold nb076AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076AlphaDummy020 m n) from (by
          unfold nb076AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy047)
        from (by
          unfold nb076AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076AlphaDummy048 m n) from (by
          unfold nb076AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy021)
        from (by
          unfold nb076AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051)
                  0)))) (show n ≠ (nb076AlphaDummy022 m n) from (by
          unfold nb076AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy010)
        from (by
          unfold nb076AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076AlphaDummy012 g m n a b) from (by
          unfold nb076AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy009)
        from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy015)
        from (by
          unfold nb076AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076AlphaDummy016 g m n a b) from (by
          unfold nb076AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy013)
        from (by
          unfold
            nb076AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076AlphaDummy014 g m n a b) from (by
          unfold
            nb076AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy005)
        from (by
          unfold
            nb076AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076AlphaDummy006 g m n a b) from (by
          unfold
            nb076AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy003))).fv ∪
        ((Class.cv (nb076AlphaDummy004))).fv) (by decide)) (freshVar_injective
        (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076SplitAlpha0001 g m n a b)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy018) from (by
          unfold nb076AlphaDummy018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 1)))) (show n ≠ (nb076AlphaDummy020 m n) from (by
          unfold nb076AlphaDummy020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n) 1)))) (TAlphaVar.there (show
        (nb076AlphaDummy004) ≠ (nb076AlphaDummy017) from (by
          unfold nb076AlphaDummy017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0050) 0)))) (show n ≠ (nb076AlphaDummy019 m n) from (by
          unfold nb076AlphaDummy019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0052 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy047)
        from (by
          unfold nb076AlphaDummy047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0054) 0)))) (show n ≠ (nb076AlphaDummy048 m n) from (by
          unfold nb076AlphaDummy048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0055 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy021)
        from (by
          unfold nb076AlphaDummy021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0051)
                  0)))) (show n ≠ (nb076AlphaDummy022 m n) from (by
          unfold nb076AlphaDummy022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0053 m n)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy010)
        from (by
          unfold nb076AlphaDummy010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  1)))) (show n ≠ (nb076AlphaDummy012 g m n a b) from (by
          unfold nb076AlphaDummy012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046 g
                    m n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy009)
        from (by
          unfold nb076AlphaDummy009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0044)
                  0)))) (show n ≠ (nb076AlphaDummy011 g m n a b) from (by
          unfold nb076AlphaDummy011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0046
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy015)
        from (by
          unfold nb076AlphaDummy015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0048)
                  0)))) (show n ≠ (nb076AlphaDummy016 g m n a b) from (by
          unfold nb076AlphaDummy016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0049
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy013)
        from (by
          unfold
            nb076AlphaDummy013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0045)
                  0)))) (show n ≠ (nb076AlphaDummy014 g m n a b) from (by
          unfold
            nb076AlphaDummy014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0047
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy004) ≠ (nb076AlphaDummy005)
        from (by
          unfold
            nb076AlphaDummy005;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0042)
                  0)))) (show n ≠ (nb076AlphaDummy006 g m n a b) from (by
          unfold
            nb076AlphaDummy006;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0043
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy003))).fv ∪
        ((Class.cv (nb076AlphaDummy004))).fv) (by decide)) (freshVar_injective
        (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb076SplitAlpha0001 g m n a b))))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((synCop (Class.cv (nb076AlphaDummy003))
                            (Class.cv (nb076AlphaDummy004)))).fv ∪
                        ((Class.cv (nb076AlphaDummy005))).fv) (by decide))
                    (freshVar_injective (((synCop (Class.cv m) (Class.cv n))).fv ∪
                        ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb076AlphaDummy010) ≠ (nb076AlphaDummy053) from (by
                                unfold nb076AlphaDummy053;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0060) 0)))) (show
                              (nb076AlphaDummy012 g m n a b) ≠
                                (nb076AlphaDummy055 g m n a b) from (by
                                unfold nb076AlphaDummy055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb076_support_mem_0061 g m n a b)
                                        0)))) (TAlphaVar.there
                              (show (nb076AlphaDummy010) ≠ (nb076AlphaDummy054) from (by
                                  unfold nb076AlphaDummy054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb076_support_mem_0060) 1)))) (show
                                (nb076AlphaDummy012 g m n a b) ≠
                                  (nb076AlphaDummy056 g m n a b) from (by
                                  unfold nb076AlphaDummy056;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb076_support_mem_0061 g m n a b) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb076AlphaDummy010))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb076AlphaDummy012 g m n a b))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb076AlphaDummy053) ≠ (nb076AlphaDummy060) from (by
          unfold nb076AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 1)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy063 g m n a b) from (by
          unfold nb076AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n a
                    b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy059)
        from (by
          unfold nb076AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy062 g m n a b) from (by
          unfold nb076AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065 g m n
                    a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062)
                  0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m
                    n a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy067)
        from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy067)
        from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068
        g m n a b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066
        g m n a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy015),
        (nb076AlphaDummy016 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy071) from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072
        g m n a b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy071)
        from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072
        g m n a b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g m n
                    a b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074
        g m n a b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074
        g m n a b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g m n a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070
        g m n a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g m n
                    a b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from
                                        (by
                                          unfold nb076AlphaDummy057;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0062)
                                                  0)))) (show
                                        (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
                                          unfold nb076AlphaDummy058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0063 g m n a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy057),
                                        (nb076AlphaDummy058 g m n a b)),
                                      ((nb076AlphaDummy053),
                                        (nb076AlphaDummy055 g m n a b)),
                                      ((nb076AlphaDummy054),
                                        (nb076AlphaDummy056 g m n a b)),
                                      ((nb076AlphaDummy010),
                                        (nb076AlphaDummy012 g m n a b)),
                                      ((nb076AlphaDummy009),
                                        (nb076AlphaDummy011 g m n a b)),
                                      ((nb076AlphaDummy015),
                                        (nb076AlphaDummy016 g m n a b)),
                                      ((nb076AlphaDummy013),
                                        (nb076AlphaDummy014 g m n a b)),
                                      ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from (by
                                        unfold nb076AlphaDummy057;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0062)
                                                0)))) (show (nb076AlphaDummy055 g m n a b) ≠
                                        (nb076AlphaDummy058 g m n a b) from (by
                                        unfold nb076AlphaDummy058;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0063 g m n a b) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from
                                        (by
                                          unfold nb076AlphaDummy057;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0062)
                                                  0)))) (show
                                        (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
                                          unfold nb076AlphaDummy058;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0063 g m n a b) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb076AlphaDummy057),
                                        (nb076AlphaDummy058 g m n a b)),
                                      ((nb076AlphaDummy053),
                                        (nb076AlphaDummy055 g m n a b)),
                                      ((nb076AlphaDummy054),
                                        (nb076AlphaDummy056 g m n a b)),
                                      ((nb076AlphaDummy010),
                                        (nb076AlphaDummy012 g m n a b)),
                                      ((nb076AlphaDummy009),
                                        (nb076AlphaDummy011 g m n a b)),
                                      ((nb076AlphaDummy015),
                                        (nb076AlphaDummy016 g m n a b)),
                                      ((nb076AlphaDummy013),
                                        (nb076AlphaDummy014 g m n a b)),
                                      ((nb076AlphaDummy005),
                                        (nb076AlphaDummy006 g m n a b)),
                                      ((nb076AlphaDummy004), n),
                                      ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
                                        (nb076AlphaDummy008 g m n a b))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part009`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb076_split_alpha_0003`. -/
@[expose]
noncomputable def nb076SplitAlpha0003 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) :
    TAlphaWff
      [((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)),
        ((nb076AlphaDummy009), (nb076AlphaDummy011 g m n a b)),
        ((nb076AlphaDummy075), (nb076AlphaDummy076 g m n a b)),
        ((nb076AlphaDummy013), (nb076AlphaDummy014 g m n a b)),
        ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy010))
          (Class.cv (nb076AlphaDummy005))) (Wff.neg
          (Wff.classEq (Class.cv (nb076AlphaDummy009))
            (synCun (synCphi (Class.cv (nb076AlphaDummy010))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb076AlphaDummy012 g m n a b))
          (Class.cv (nb076AlphaDummy006 g m n a b))) (Wff.neg
          (Wff.classEq (Class.cv (nb076AlphaDummy011 g m n a b))
            (synCun (synCphi (Class.cv (nb076AlphaDummy012 g m n a b)))
              (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy010) from (by
              unfold nb076AlphaDummy010;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))))
          (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy012 g m n a b) from (by
              unfold nb076AlphaDummy012;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))))
          (TAlphaVar.there (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy009) from (by
                unfold nb076AlphaDummy009;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))))
            (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy011 g m n a b) from (by
                unfold nb076AlphaDummy011;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0)))) (TAlphaVar.there
              (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy075) from (by
                  unfold nb076AlphaDummy075;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0086) 0))))
              (show (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy076 g m n a b) from
                (by
                  unfold nb076AlphaDummy076;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb076_support_mem_0087 g m n a b) 0))))
              (TAlphaVar.there (show (nb076AlphaDummy005) ≠ (nb076AlphaDummy013) from (by
                    unfold nb076AlphaDummy013;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0083) 0)))) (show
                  (nb076AlphaDummy006 g m n a b) ≠ (nb076AlphaDummy014 g m n a b) from (by
                    unfold nb076AlphaDummy014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb076_support_mem_0085 g m n a b) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((synCop (Class.cv (nb076AlphaDummy003))
                    (Class.cv (nb076AlphaDummy004)))).fv ∪
                ((Class.cv (nb076AlphaDummy005))).fv) (by decide)) (freshVar_injective
              (((synCop (Class.cv m) (Class.cv n))).fv ∪
                ((Class.cv (nb076AlphaDummy006 g m n a b))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy010) ≠ (nb076AlphaDummy053) from (by
                                        unfold nb076AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0060)
                                                0)))) (show (nb076AlphaDummy012 g m n a b) ≠
                                        (nb076AlphaDummy055 g m n a b) from (by
                                        unfold nb076AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0061 g m n a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076AlphaDummy010) ≠ (nb076AlphaDummy054) from
                                        (by
                                          unfold nb076AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0060)
                                                  1)))) (show
                                        (nb076AlphaDummy012 g m n a b) ≠
        (nb076AlphaDummy056 g m n a b) from (by
                                          unfold nb076AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0061 g m n a b) 1))))
                                      (TAlphaVar.there (show (nb076AlphaDummy010) ≠
        (nb076AlphaDummy079) from (by
          unfold nb076AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0090) 0)))) (show (nb076AlphaDummy012 g m n a b) ≠
        (nb076AlphaDummy080 g m n a b) from (by
          unfold nb076AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0091 g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy010) ≠ (nb076AlphaDummy077)
        from (by
          unfold nb076AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0088) 0)))) (show (nb076AlphaDummy012 g m n a b) ≠
        (nb076AlphaDummy078 g m n a b) from (by
          unfold nb076AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0089 g m n a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb076AlphaDummy010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb076AlphaDummy012 g m n a b))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy060) from (by
          unfold nb076AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  1)))) (show (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy063 g m n a
        b) from (by
          unfold nb076AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy059)
        from (by
          unfold nb076AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  0)))) (show (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy062 g m n a
        b) from (by
          unfold nb076AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold
            nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062)
                  0)))) (show (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy058 g m n
        a b) from (by
          unfold
            nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a
        b))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n
        a b))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055
        g m n a b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy071) from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072 g m n a
        b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy071) from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072 g m n a
        b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074 g m n a
        b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074 g m n a
        b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy057), (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy057), (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb076AlphaDummy010) ≠ (nb076AlphaDummy053) from (by
                                        unfold nb076AlphaDummy053;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb076_support_mem_0060)
                                                0)))) (show (nb076AlphaDummy012 g m n a b) ≠
                                        (nb076AlphaDummy055 g m n a b) from (by
                                        unfold nb076AlphaDummy055;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb076_support_mem_0061 g m n a b) 0))))
                                    (TAlphaVar.there (show
                                        (nb076AlphaDummy010) ≠ (nb076AlphaDummy054) from
                                        (by
                                          unfold nb076AlphaDummy054;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb076_support_mem_0060)
                                                  1)))) (show
                                        (nb076AlphaDummy012 g m n a b) ≠
        (nb076AlphaDummy056 g m n a b) from (by
                                          unfold nb076AlphaDummy056;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb076_support_mem_0061 g m n a b) 1))))
                                      (TAlphaVar.there (show (nb076AlphaDummy010) ≠
        (nb076AlphaDummy079) from (by
          unfold nb076AlphaDummy079;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0090) 0)))) (show (nb076AlphaDummy012 g m n a b) ≠
        (nb076AlphaDummy080 g m n a b) from (by
          unfold nb076AlphaDummy080;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0091 g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy010) ≠ (nb076AlphaDummy077)
        from (by
          unfold nb076AlphaDummy077;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0088) 0)))) (show (nb076AlphaDummy012 g m n a b) ≠
        (nb076AlphaDummy078 g m n a b) from (by
          unfold nb076AlphaDummy078;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0089 g m n a b)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb076AlphaDummy010))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb076AlphaDummy012 g m n a b))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy060) from (by
          unfold nb076AlphaDummy060;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  1)))) (show (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy063 g m n a
        b) from (by
          unfold nb076AlphaDummy063;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  1)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy059)
        from (by
          unfold nb076AlphaDummy059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0064)
                  0)))) (show (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy062 g m n a
        b) from (by
          unfold nb076AlphaDummy062;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0065
                    g m n a b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold
            nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062)
                  0)))) (show (nb076AlphaDummy055 g m n a b) ≠ (nb076AlphaDummy058 g m n
        a b) from (by
          unfold
            nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063
                    g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a
        b))] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0068)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0069
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0066)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0067
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy067) from (by
          unfold
            nb076AlphaDummy067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0072)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy068 g m n a
        b) from (by
          unfold
            nb076AlphaDummy068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0073
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy065)
        from (by
          unfold
            nb076AlphaDummy065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0070)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy066 g m n
        a b) from (by
          unfold
            nb076AlphaDummy066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0071
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy061), (nb076AlphaDummy064 g m n a b)), ((nb076AlphaDummy060),
        (nb076AlphaDummy063 g m n a b)), ((nb076AlphaDummy059),
        (nb076AlphaDummy062 g m n a b)), ((nb076AlphaDummy057),
        (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n
        a b))] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb076AlphaDummy053))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055
        g m n a b))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy071) from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072 g m n a
        b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy060) ≠
        (nb076AlphaDummy071) from (by
          unfold
            nb076AlphaDummy071;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0076)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy072 g m n a
        b) from (by
          unfold
            nb076AlphaDummy072;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0077
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy060) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0074)
                  0)))) (show (nb076AlphaDummy063 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0075
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb076AlphaDummy053))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb076AlphaDummy055 g m n a b))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074 g m n a
        b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy061) ≠
        (nb076AlphaDummy073) from (by
          unfold
            nb076AlphaDummy073;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0080)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy074 g m n a
        b) from (by
          unfold
            nb076AlphaDummy074;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0081
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.there (show (nb076AlphaDummy061) ≠ (nb076AlphaDummy069)
        from (by
          unfold
            nb076AlphaDummy069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0078)
                  0)))) (show (nb076AlphaDummy064 g m n a b) ≠ (nb076AlphaDummy070 g m n
        a b) from (by
          unfold
            nb076AlphaDummy070;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0079
                    g
                    m
                    n
                    a
                    b)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy057), (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057) from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a b)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb076AlphaDummy053) ≠ (nb076AlphaDummy057)
        from (by
          unfold nb076AlphaDummy057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0062) 0)))) (show (nb076AlphaDummy055 g m n a b) ≠
        (nb076AlphaDummy058 g m n a b) from (by
          unfold nb076AlphaDummy058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb076_support_mem_0063 g m n a
                    b)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
        [((nb076AlphaDummy057), (nb076AlphaDummy058 g m n a b)), ((nb076AlphaDummy053),
        (nb076AlphaDummy055 g m n a b)), ((nb076AlphaDummy054),
        (nb076AlphaDummy056 g m n a b)), ((nb076AlphaDummy079),
        (nb076AlphaDummy080 g m n a b)), ((nb076AlphaDummy077),
        (nb076AlphaDummy078 g m n a b)), ((nb076AlphaDummy010),
        (nb076AlphaDummy012 g m n a b)), ((nb076AlphaDummy009),
        (nb076AlphaDummy011 g m n a b)), ((nb076AlphaDummy075),
        (nb076AlphaDummy076 g m n a b)), ((nb076AlphaDummy013),
        (nb076AlphaDummy014 g m n a b)), ((nb076AlphaDummy005),
        (nb076AlphaDummy006 g m n a b)), ((nb076AlphaDummy004), n),
        ((nb076AlphaDummy003), m), ((nb076AlphaDummy007),
        (nb076AlphaDummy008 g m n a b))] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb076AlphaDummy077), (nb076AlphaDummy078 g m n a b)),
                    ((nb076AlphaDummy010), (nb076AlphaDummy012 g m n a b)),
                    ((nb076AlphaDummy009), (nb076AlphaDummy011 g m n a b)),
                    ((nb076AlphaDummy075), (nb076AlphaDummy076 g m n a b)),
                    ((nb076AlphaDummy013), (nb076AlphaDummy014 g m n a b)),
                    ((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
                    ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
                    ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb076_wpp_notmem_0198 : (nb076AlphaDummy005) ∉ ((synCncs)).fv := by
  simpa only [nb076AlphaDummy005, fv_syn_cncs] using (nb076_compact_fv_empty_0028)

theorem nb076_wpp_notmem_0199 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy006 g m n a b) ∉ ((synCncs)).fv := by
  simpa only [nb076AlphaDummy006, fv_syn_cncs] using
    (nb076_compact_fv_empty_0029 g m n a b)

theorem nb076_wpp_notmem_0200 : (nb076AlphaDummy004) ∉ ((synCncs)).fv := by
  simpa only [nb076AlphaDummy004, fv_syn_cncs] using (nb076_compact_fv_empty_0030)

theorem nb076_wpp_notmem_0201 (n : Var) : n ∉ ((synCncs)).fv := by
  simpa only [fv_syn_cncs] using (nb076_compact_fv_empty_0031 n)

theorem nb076_wpp_notmem_0202 : (nb076AlphaDummy003) ∉ ((synCncs)).fv := by
  simpa only [nb076AlphaDummy003, fv_syn_cncs] using (nb076_compact_fv_empty_0032)

theorem nb076_wpp_notmem_0203 (m : Var) : m ∉ ((synCncs)).fv := by
  simpa only [fv_syn_cncs] using (nb076_compact_fv_empty_0033 m)

theorem nb076_wpp_notmem_0204 : (nb076AlphaDummy007) ∉ ((synCncs)).fv := by
  simpa only [nb076AlphaDummy007, fv_syn_cncs] using (nb076_compact_fv_empty_0034)

theorem nb076_wpp_notmem_0205 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076AlphaDummy008 g m n a b) ∉ ((synCncs)).fv := by
  simpa only [nb076AlphaDummy008, fv_syn_cncs] using
    (nb076_compact_fv_empty_0035 g m n a b)

theorem nb076_compact_envfresh_0014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TEnvFresh
      [((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      ((synCncs)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb076AlphaDummy005) (nb076AlphaDummy006 g m n a b)
      (nb076_wpp_notmem_0198) (nb076_wpp_notmem_0199 g m n a b)
      (TEnvFresh.consFresh (nb076AlphaDummy004) n (nb076_wpp_notmem_0200)
        (nb076_wpp_notmem_0201 n)
        (TEnvFresh.consFresh (nb076AlphaDummy003) m (nb076_wpp_notmem_0202)
          (nb076_wpp_notmem_0203 m)
          (TEnvFresh.consFresh (nb076AlphaDummy007) (nb076AlphaDummy008 g m n a b)
            (nb076_wpp_notmem_0204) (nb076_wpp_notmem_0205 g m n a b)
            (TEnvFresh.nil ((synCncs)).fv)))))

/-- Checked nominal proof certificate identified upstream as `nb076_wpp_refl_0014`. -/
@[expose]
noncomputable def nb076WppRefl0014 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    TReflOn
      [((nb076AlphaDummy005), (nb076AlphaDummy006 g m n a b)),
        ((nb076AlphaDummy004), n), ((nb076AlphaDummy003), m),
        ((nb076AlphaDummy007), (nb076AlphaDummy008 g m n a b))]
      ((synCncs)).fv :=
  TEnvFresh.reflOn (nb076_compact_envfresh_0014 g m n a b)

theorem nb076_compact_fv_empty_0080 : (nb076AlphaDummy002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0081 (g : Var) : g ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0082 : (nb076AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0083 (b : Var) : b ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0084 : (nb076AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb076_compact_fv_empty_0085 (a : Var) : a ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
