/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.Presentation
public import LeanPool.SmallUndecidableGroups.Borisov.Construction
public import Mathlib.Tactic.Group

/-!
# Compression

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

open CommutatorLemmas

namespace Host
namespace Compression

/-- The seven Borisov generators, viewed in the nine-generator alphabet used
immediately before the ordered Tietze eliminations. -/
def oldGenerator : Fin 7 → OldGen :=
  ![.d, .e, .s1, .s2, .c, .t, .k]

/-- The word substituted for each of Borisov's seven generators by the
compression. -/
def generatorWord (i : Fin 7) : HostWord :=
  tau (oldGenerator i)

/-- Substitute the ordered words `tau` into a word on Borisov's seven
generators. -/
def word (w : Borisov.BorisovWord) : HostWord :=
  Word.substitute generatorWord w

@[simp]
theorem word_generator (i : Fin 7) :
    word (Word.generator i) = generatorWord i := by
  simp [word, Word.substitute, Word.generator]

@[simp]
theorem word_mul (u v : Borisov.BorisovWord) :
    word (Word.mul u v) = Word.mul (word u) (word v) :=
  Word.substitute_append generatorWord u v

@[simp]
theorem word_inverse (u : Borisov.BorisovWord) :
    word (Word.inverse u) = Word.inverse (word u) := by
  simpa [word, Word.inverse, FreeGroup.invRev, List.map_reverse] using
    Word.substitute_invRev generatorWord u

@[simp]
theorem word_product (ws : List Borisov.BorisovWord) :
    word (Word.product ws) = Word.product (ws.map word) :=
  Word.substitute_flatten generatorWord ws

@[simp]
theorem word_commutator (u v : Borisov.BorisovWord) :
    word (Word.commutator u v) = Word.commutator (word u) (word v) := by
  simp [Word.commutator]

@[simp]
theorem word_positive (Q : List (Fin 2)) :
    word (Borisov.positiveWord Q) = positiveWord Q := by
  induction Q with
  | nil => rfl
  | cons i Q ih =>
      change word
          (Word.mul (if i = 0 then Borisov.s1Word else Borisov.s2Word)
            (Borisov.positiveWord Q)) = _
      rw [word_mul, ih]
      fin_cases i <;>
        rfl

@[simp]
theorem word_testWord (Q : List (Fin 2)) :
    word (Borisov.testWord Q) = testWord Q := by
  simp [Borisov.testWord, testWord, generatorWord,
    oldGenerator, Borisov.tWord, Borisov.kWord, tau]

/-- Evaluation commutes with the ordered word substitution. -/
theorem eval_word {G : Type*} [Group G] (x : Fin 3 → G)
    (u : Borisov.BorisovWord) :
    Word.eval x (word u) =
      Word.eval (fun i => Word.eval x (generatorWord i)) u :=
  Word.eval_substitute x generatorWord u

private theorem commute_inv_left {G : Type*} [Group G]
    {a b : G} (h : a * b = b * a) : a⁻¹ * b = b * a⁻¹ :=
  (Commute.inv_left_iff.mpr h).eq

private theorem commute_conjugate_of_commute {G : Type*} [Group G]
    {a b y : G} (hab : a * b = b * a) (hyb : y * b = b * y) :
    (y⁻¹ * a * y) * b = b * (y⁻¹ * a * y) := by
  have hab' : Commute a b := hab
  have hyb' : Commute y b := hyb
  have hfix : y⁻¹ * b * y = b := hyb'.inv_mul_cancel
  have hconj : Commute (y⁻¹ * a * y) b := by
    simpa [hfix] using hab'.conj y⁻¹
  exact hconj.eq

private theorem conjugate_pow {G : Type*} [Group G]
    (y a : G) (n : ℕ) :
    (y⁻¹ * a * y) ^ n = y⁻¹ * a ^ n * y := by
  simpa using (conj_pow (a := y⁻¹) (b := a) (i := n))

/-- The relations removed by the ordered Tietze eliminations follow from the
surviving relations in any group. -/
private theorem transported_relations {G : Type*} [Group G]
    (D E S R C T K Y Z : G)
    (hTdef : T = Z⁻¹ * D * Z) (hCdef : C = Z⁻¹ * T * Z)
    (hYdef : Y = Z⁻¹ * C * Z) (hEdef : E = Y⁻¹ * D⁻¹ * Y)
    (hKdef : K = Y⁻¹ * T * Y) (hRdef : R = Y⁻¹ * S⁻¹ * Y)
    (hSd : S⁻¹ * D ^ 4 * S = D) (hSe : S⁻¹ * E * S = E ^ 4)
    (hSc : S⁻¹ * C⁻¹ * S * C = 1) (hDt : D⁻¹ * T⁻¹ * D * T = 1)
    (hYe : Y⁻¹ * E * Y = D) :
    R⁻¹ * D ^ 4 * R = D ∧ R⁻¹ * E * R = E ^ 4 ∧
      R * C = C * R ∧ K * C = C * K ∧ K * E = E * K ∧
      T⁻¹ * C⁻¹ * T * C = 1 := by
  have hTc : T⁻¹ * C⁻¹ * T * C = 1 := by
    rw [hTdef, hCdef]
    calc
      (Z⁻¹ * D * Z)⁻¹ * (Z⁻¹ * T * Z)⁻¹ *
          (Z⁻¹ * D * Z) * (Z⁻¹ * T * Z) =
        Z⁻¹ * (D⁻¹ * T⁻¹ * D * T) * Z := by group
      _ = 1 := by rw [hDt]; simp
  have hCy : C⁻¹ * Y⁻¹ * C * Y = 1 := by
    rw [hCdef, hYdef]
    calc
      (Z⁻¹ * T * Z)⁻¹ * (Z⁻¹ * C * Z)⁻¹ *
          (Z⁻¹ * T * Z) * (Z⁻¹ * C * Z) =
        Z⁻¹ * (T⁻¹ * C⁻¹ * T * C) * Z := by group
      _ = 1 := by rw [hTc]; simp
  have hDTcomm : D * T = T * D := (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mp hDt
  have hTCcomm : T * C = C * T := (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mp hTc
  have hCYcomm : C * Y = Y * C := (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mp hCy
  have hSCcomm : S * C = C * S := (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mp hSc
  have hSeBack : S * E ^ 4 * S⁻¹ = E := by
    calc
      S * E ^ 4 * S⁻¹ = S * (S⁻¹ * E * S) * S⁻¹ := by rw [hSe]
      _ = E := by group
  have hSdBack : S * D * S⁻¹ = D ^ 4 := by
    calc
      S * D * S⁻¹ = S * (S⁻¹ * D ^ 4 * S) * S⁻¹ := by rw [hSd]
      _ = D ^ 4 := by group
  have hSdInv : S * D⁻¹ * S⁻¹ = (D⁻¹) ^ 4 := by
    calc
      S * D⁻¹ * S⁻¹ = (S * D * S⁻¹)⁻¹ := by group
      _ = (D ^ 4)⁻¹ := by rw [hSdBack]
      _ = (D⁻¹) ^ 4 := by group
  have hRd : R⁻¹ * D ^ 4 * R = D := by
    rw [hRdef, ← hYe]
    calc
      (Y⁻¹ * S⁻¹ * Y)⁻¹ * (Y⁻¹ * E * Y) ^ 4 *
          (Y⁻¹ * S⁻¹ * Y) =
        Y⁻¹ * (S * E ^ 4 * S⁻¹) * Y := by
          rw [conjugate_pow]
          group
      _ = Y⁻¹ * E * Y := by rw [hSeBack]
  have hRe : R⁻¹ * E * R = E ^ 4 := by
    rw [hRdef, hEdef]
    calc
      (Y⁻¹ * S⁻¹ * Y)⁻¹ * (Y⁻¹ * D⁻¹ * Y) *
          (Y⁻¹ * S⁻¹ * Y) =
        Y⁻¹ * (S * D⁻¹ * S⁻¹) * Y := by group
      _ = Y⁻¹ * (D⁻¹) ^ 4 * Y := by rw [hSdInv]
      _ = (Y⁻¹ * D⁻¹ * Y) ^ 4 := (conjugate_pow Y D⁻¹ 4).symm
  have hRCC : R * C = C * R := by
    rw [hRdef]
    exact commute_conjugate_of_commute (commute_inv_left hSCcomm) hCYcomm.symm
  have hKCC : K * C = C * K := by
    rw [hKdef]
    exact commute_conjugate_of_commute hTCcomm hCYcomm.symm
  have hTDinv : T * D⁻¹ = D⁻¹ * T :=
    (commute_inv_left hDTcomm).symm
  have hKEcomm : K * E = E * K := by
    rw [hKdef, hEdef]
    calc
      (Y⁻¹ * T * Y) * (Y⁻¹ * D⁻¹ * Y) =
          Y⁻¹ * (T * D⁻¹) * Y := by group
      _ = Y⁻¹ * (D⁻¹ * T) * Y := by rw [hTDinv]
      _ = (Y⁻¹ * D⁻¹ * Y) * (Y⁻¹ * T * Y) := by group
  exact ⟨hRd, hRe, hRCC, hKCC, hKEcomm, hTc⟩

/-- Every Borisov relator is satisfied after applying the ordered
compression into the three-generator host. -/
theorem relator_eq_one (datum : Thue.StandingDatum) (i : Fin 14) :
    Word.eval
        (fun j => Word.eval
          (fun k : Fin 3 =>
            (PresentedGroup.of k : (presentationOf datum).Group))
          (generatorWord j))
        ((Borisov.presentation datum).relator i) = 1 := by
  let x : Fin 3 → (presentationOf datum).Group :=
    fun i => PresentedGroup.of i
  let D := Word.eval x dWord
  let E := Word.eval x eWord
  let S := Word.eval x sWord
  let R := Word.eval x s2Word
  let C := Word.eval x cWord
  let T := Word.eval x tWord
  let K := Word.eval x kWord
  let Y := Word.eval x yWord
  let Z := Word.eval x zWord
  have hrel (i : Fin 9) :
      Word.eval x ((presentationOf datum).relator i) = 1 :=
    (presentationOf datum).relator_eq_one i
  have h0raw := hrel (0 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 0) = 1 at h0raw
  simp only [rho, oldSurvivingRelator, Fin.isValue, Matrix.cons_val_zero,
    OldWord.evaluate_relation, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, OldWord.evaluate_pow,
    List.map_nil, Word.eval_relation, Word.eval_product, Word.eval_inverse, Word.eval_pow,
    List.prod_cons, List.prod_nil, mul_one] at h0raw
  have hSd : S⁻¹ * D ^ 4 * S = D := by
    apply eq_of_mul_inv_eq_one
    calc
      (S⁻¹ * D ^ 4 * S) * D⁻¹ = S⁻¹ * (D ^ 4 * S) * D⁻¹ := by group
      _ = 1 := h0raw
  have h1raw := hrel (1 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 1) = 1 at h1raw
  simp only [rho, oldSurvivingRelator, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    OldWord.evaluate_relation, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, List.map_nil,
    OldWord.evaluate_pow, Word.eval_relation, Word.eval_product, Word.eval_inverse,
    Word.eval_pow] at h1raw
  have hSe : S⁻¹ * E * S = E ^ 4 := by
    apply eq_of_mul_inv_eq_one
    calc
      (S⁻¹ * E * S) * (E ^ 4)⁻¹ = S⁻¹ * (E * S) * (E ^ 4)⁻¹ := by group
      _ = 1 := h1raw
  have h2raw := hrel (2 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 2) = 1 at h2raw
  simp only [rho, oldSurvivingRelator, Fin.isValue, Matrix.cons_val,
    OldWord.evaluate_commutator, OldWord.evaluate_generator, tau, Word.eval_commutator] at h2raw
  have hSc : S⁻¹ * C⁻¹ * S * C = 1 := by
    calc
      S⁻¹ * C⁻¹ * S * C = S⁻¹ * (C⁻¹ * S) * C := by group
      _ = 1 := h2raw
  have h6raw := hrel (6 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 6) = 1 at h6raw
  simp only [rho, oldSurvivingRelator, Fin.isValue, Matrix.cons_val,
    OldWord.evaluate_commutator, OldWord.evaluate_generator, tau, Word.eval_commutator] at h6raw
  have hDt : D⁻¹ * T⁻¹ * D * T = 1 := by
    calc
      D⁻¹ * T⁻¹ * D * T = D⁻¹ * (T⁻¹ * D) * T := by group
      _ = 1 := h6raw
  have h8raw := hrel (8 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 8) = 1 at h8raw
  simp only [rho, oldSurvivingRelator, Fin.isValue, Matrix.cons_val, OldWord.evaluate_relation,
    OldWord.evaluate_product, List.map_cons, OldWord.evaluate_inverse,
    OldWord.evaluate_generator, tau, List.map_nil, Word.eval_relation, Word.eval_product,
    Word.eval_inverse, List.prod_cons, List.prod_nil, mul_one] at h8raw
  have hYe : Y⁻¹ * E * Y = D := by
    apply eq_of_mul_inv_eq_one
    calc
      (Y⁻¹ * E * Y) * D⁻¹ = Y⁻¹ * (E * Y) * D⁻¹ := by group
      _ = 1 := h8raw
  have hTdef : T = Z⁻¹ * D * Z := by
    simp [T, Z, D, tWord, Word.eval_product, mul_assoc]
  have hCdef : C = Z⁻¹ * T * Z := by
    simp [C, Z, T, cWord, tWord, Word.eval_product, mul_assoc]
  have hYdef : Y = Z⁻¹ * C * Z := by
    simp [Y, Z, C, yWord, cWord, tWord, Word.eval_product, mul_assoc]
  have hEdef : E = Y⁻¹ * D⁻¹ * Y := by
    simp [E, Y, D, eWord, yWord, cWord, tWord, Word.eval_product, mul_assoc]
  have hKdef : K = Y⁻¹ * T * Y := by
    simp [K, Y, T, kWord, yWord, cWord, tWord, Word.eval_product, mul_assoc]
  have hRdef : R = Y⁻¹ * S⁻¹ * Y := by
    simp [R, Y, S, s2Word, yWord, cWord, tWord, Word.eval_product, mul_assoc]
  obtain ⟨hRd, hRe, hRCC, hKCC, hKEcomm, hTc⟩ :=
    transported_relations D E S R C T K Y Z
      hTdef hCdef hYdef hEdef hKdef hRdef hSd hSe hSc hDt hYe
  have hDTcomm : D * T = T * D := (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mp hDt
  have h3raw := hrel (3 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 3) = 1 at h3raw
  simp only [rho, oldSurvivingRelator, oldSimulationRelator, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_add, Nat.one_mod, Nat.reduceAdd, Nat.mod_succ, Matrix.cons_val,
    OldWord.evaluate_relation, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, OldWord.evaluate_pow,
    OldWord.evaluate_positive, List.map_nil, Word.eval_relation, Word.eval_product,
    Word.eval_inverse, Word.eval_pow, pow_one, Word.eval_substitutePositive, List.prod_cons,
    List.prod_nil, mul_one, mul_inv_rev] at h3raw
  have h4raw := hrel (4 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 4) = 1 at h4raw
  simp only [rho, oldSurvivingRelator, oldSimulationRelator, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_add, Nat.one_mod, Nat.reduceAdd, Nat.mod_succ, Matrix.cons_val,
    OldWord.evaluate_relation, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, OldWord.evaluate_pow,
    OldWord.evaluate_positive, List.map_nil, Word.eval_relation, Word.eval_product,
    Word.eval_inverse, Word.eval_pow, Word.eval_substitutePositive, List.prod_cons,
    List.prod_nil, mul_one, mul_inv_rev] at h4raw
  have h5raw := hrel (5 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 5) = 1 at h5raw
  simp only [rho, oldSurvivingRelator, oldSimulationRelator, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, zero_add, Nat.one_mod, Nat.reduceAdd, Nat.mod_succ, Matrix.cons_val,
    OldWord.evaluate_relation, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_generator, tau, OldWord.evaluate_pow,
    OldWord.evaluate_positive, List.map_nil, Word.eval_relation, Word.eval_product,
    Word.eval_inverse, Word.eval_pow, Word.eval_substitutePositive, List.prod_cons,
    List.prod_nil, mul_one, mul_inv_rev] at h5raw
  have h7raw := hrel (7 : Fin 9)
  change Word.eval x (rho datum.F datum.E datum.P 7) = 1 at h7raw
  simp only [rho, oldSurvivingRelator, Fin.isValue, Matrix.cons_val,
    OldWord.evaluate_commutator, OldWord.evaluate_product, List.map_cons,
    OldWord.evaluate_inverse, OldWord.evaluate_positive, tau, OldWord.evaluate_generator,
    List.map_nil, Word.eval_commutator, Word.eval_product, Word.eval_inverse,
    Word.eval_substitutePositive] at h7raw
  let U : (presentationOf datum).Group :=
    (datum.P.map fun j => if j = 0 then S else R).prod
  have hPK : (U⁻¹ * T * U) * K = K * (U⁻¹ * T * U) := by
    apply (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mp
    simpa [U, mul_assoc] using h7raw
  have hKP : K⁻¹ * (U⁻¹ * T * U)⁻¹ * K * (U⁻¹ * T * U) = 1 :=
    (inverse_commutator_eq_one_iff_mul_eq_mul _ _).mpr hPK.symm
  let b : Fin 7 → (presentationOf datum).Group :=
    fun j => Word.eval x (generatorWord j)
  have hb : b = ![D, E, S, R, C, T, K] := by
    funext j
    fin_cases j <;> rfl
  change Word.eval b ((Borisov.presentation datum).relator i) = 1
  rw [hb]
  fin_cases i
  · simpa [Borisov.presentation, Borisov.sDRelator,
      Borisov.dWord, Borisov.s1Word, Word.eval_product] using h0raw
  · simpa [Borisov.presentation, Borisov.sERelator,
      Borisov.eWord, Borisov.s1Word, Word.eval_product] using h1raw
  · simpa [Borisov.presentation, Borisov.sDRelator,
      Borisov.dWord, Borisov.s2Word, Word.eval_product, mul_assoc] using
      (mul_inv_eq_one.mpr hRd)
  · simpa [Borisov.presentation, Borisov.sERelator,
      Borisov.eWord, Borisov.s2Word, Word.eval_product, mul_assoc] using
      (mul_inv_eq_one.mpr hRe)
  · simpa [Borisov.presentation, Borisov.s1Word, Borisov.cWord,
      Word.eval_product] using hSc
  · simpa [Borisov.presentation, Borisov.s2Word, Borisov.cWord,
      Word.eval_product] using ((inverse_commutator_eq_one_iff_mul_eq_mul _ _).mpr hRCC)
  · simpa [Borisov.presentation, Borisov.simulationRelator,
      Borisov.dWord, Borisov.eWord, Borisov.s1Word, Borisov.s2Word,
      Borisov.cWord, Borisov.positiveWord, Word.eval_product] using h3raw
  · simpa [Borisov.presentation, Borisov.simulationRelator,
      Borisov.dWord, Borisov.eWord, Borisov.s1Word, Borisov.s2Word,
      Borisov.cWord, Borisov.positiveWord, Word.eval_product] using h4raw
  · simpa [Borisov.presentation, Borisov.simulationRelator,
      Borisov.dWord, Borisov.eWord, Borisov.s1Word, Borisov.s2Word,
      Borisov.cWord, Borisov.positiveWord, Word.eval_product] using h5raw
  · simpa [Borisov.presentation, Borisov.tWord, Borisov.cWord,
      Word.eval_product] using hTc
  · simpa [Borisov.presentation, Borisov.tWord, Borisov.dWord,
      Word.eval_product] using ((inverse_commutator_eq_one_iff_mul_eq_mul _ _).mpr hDTcomm.symm)
  · simpa [Borisov.presentation, Borisov.kWord, Borisov.cWord,
      Word.eval_product] using ((inverse_commutator_eq_one_iff_mul_eq_mul _ _).mpr hKCC)
  · simpa [Borisov.presentation, Borisov.kWord, Borisov.eWord,
      Word.eval_product] using ((inverse_commutator_eq_one_iff_mul_eq_mul _ _).mpr hKEcomm)
  · simpa [Borisov.presentation, Borisov.pWord, Borisov.kWord,
      Borisov.tWord, Borisov.s1Word, Borisov.s2Word,
      Borisov.positiveWord, U, Word.eval_product, mul_assoc] using hKP

/-- The homomorphism from Borisov's group into the compressed host, induced
by the ordered substitution. -/
def hom (datum : Thue.StandingDatum) :
    (Borisov.presentation datum).Group →* (presentationOf datum).Group :=
  (Borisov.presentation datum).homOfRelators
    (fun i => Word.eval
      (fun k : Fin 3 =>
        (PresentedGroup.of k : (presentationOf datum).Group))
      (generatorWord i))
    (relator_eq_one datum)

@[simp]
theorem hom_of (datum : Thue.StandingDatum) (i : Fin 7) :
    hom datum (PresentedGroup.of i) =
      (presentationOf datum).evalWord (generatorWord i) :=
  (Borisov.presentation datum).homOfRelators_of _ _ i

/-- The compression homomorphism evaluates a Borisov word by first applying
the syntactic substitution. -/
theorem hom_evalWord (datum : Thue.StandingDatum)
    (u : Borisov.BorisovWord) :
    hom datum ((Borisov.presentation datum).evalWord u) =
      (presentationOf datum).evalWord (word u) := by
  calc
    hom datum ((Borisov.presentation datum).evalWord u) =
        Word.eval
          (fun i => Word.eval
            (PresentedGroup.of : Fin 3 → (presentationOf datum).Group)
            (generatorWord i)) u :=
      (Borisov.presentation datum).homOfRelators_evalWord _ _ u
    _ = (presentationOf datum).evalWord (word u) := by
      rw [FP.evalWord, eval_word]

/-- The elementary direction of preservation: any Borisov word which is one
remains one after compression. -/
theorem wordProblem_word_of_wordProblem (datum : Thue.StandingDatum)
    (u : Borisov.BorisovWord)
    (hu : (Borisov.presentation datum).wordProblem u) :
    (presentationOf datum).wordProblem (word u) := by
  rw [FP.wordProblem_iff_evalWord_eq_one] at hu ⊢
  rw [← hom_evalWord datum u, hu, map_one]

/-- The precise normal-form obligation.  In the paper this follows
because the two successive HNN extensions are proper, so the original
Borisov group embeds in the final host; the six following Tietze eliminations
are isomorphisms. -/
def Injective (datum : Thue.StandingDatum) : Prop :=
  Function.Injective (hom datum)

/-- Injectivity of the compression homomorphism gives reflection of the word
problem. -/
theorem wordProblem_of_wordProblem_word
    (datum : Thue.StandingDatum) (hinj : Injective datum)
    (u : Borisov.BorisovWord)
    (hu : (presentationOf datum).wordProblem (word u)) :
    (Borisov.presentation datum).wordProblem u := by
  rw [FP.wordProblem_iff_evalWord_eq_one] at hu ⊢
  apply hinj
  rw [hom_evalWord, hu, map_one]

theorem wordProblem_iff_wordProblem_word
    (datum : Thue.StandingDatum) (hinj : Injective datum)
    (u : Borisov.BorisovWord) :
    (Borisov.presentation datum).wordProblem u ↔
      (presentationOf datum).wordProblem (word u) := by
  constructor
  · exact wordProblem_word_of_wordProblem datum u
  · exact wordProblem_of_wordProblem_word datum hinj u

theorem testWord_iff (datum : Thue.StandingDatum)
    (hinj : Injective datum) (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) ↔
      (presentationOf datum).wordProblem (testWord Q) := by
  simpa only [word_testWord] using
    wordProblem_iff_wordProblem_word datum hinj (Borisov.testWord Q)

end Compression
end Host
end Undecidability
