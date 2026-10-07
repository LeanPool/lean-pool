/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.GroupTheory.MultipleHNN.FlatUniqueness
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.CoefficientShapes
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.InputsBridge

/-!
# Positivity in Borisov's coefficient normal form

The full flat-signature uniqueness theorem compares the literal expansion of
a rank-five word with the positive flat representative of `d^f Q e^r`.
Consequently every displayed rank-five letter has positive sign.  This is the
positivity half of Borisov's page-771 coefficient parser.
-/

@[expose] public section

namespace Undecidability
namespace BorisovCoefficientSignComparison

open BorisovHNNModel
open BorisovCStage
open BorisovAssertionIV
open BorisovAssertionIVBoundary
open BorisovG0HNN
open BorisovG0NormalForm
open BorisovInputsBridge
open MultipleHNNFlatUniqueness
open BorisovCoefficientShapes

noncomputable section

/-- A reduced word in the flattened two-stable-letter HNN model. -/
abbrev FlatWord := MultipleHNNFlat.ReducedWord A0 B0

/-- The literal flat reduced word for `d^f Q e^r`, where `Q` is a positive
word in the two stable letters. -/
def positiveCoefficientWord (Q : List (Fin 2)) (f r : ℤ) : FlatWord :=
  if hQ : Q = [] then
    { head := d ^ f * e ^ r
      toList := []
      chain := List.isChain_nil }
  else
    { head := d ^ f
      toList := run Q hQ 1 (e ^ r)
      chain := run_chain Q hQ 1 (e ^ r) }

@[simp] theorem positiveCoefficientWord_signature
    (Q : List (Fin 2)) (f r : ℤ) :
    MultipleHNNFlat.signature A0 B0 (positiveCoefficientWord Q f r) =
      Q.map (fun beta ↦ (beta, (1 : ℤˣ))) := by
  by_cases hQ : Q = []
  · simp [positiveCoefficientWord, hQ, MultipleHNNFlat.signature]
  · simp only [positiveCoefficientWord, hQ, ↓reduceDIte,
      MultipleHNNFlat.signature]
    unfold run
    rw [List.map_append, List.map_map, List.map_singleton]
    change Q.dropLast.map (fun beta ↦ (beta, (1 : ℤˣ))) ++
        [(Q.getLast hQ, (1 : ℤˣ))] =
      Q.map (fun beta ↦ (beta, (1 : ℤˣ)))
    have hsplit := congrArg
      (List.map (fun beta ↦ (beta, (1 : ℤˣ))))
      (List.dropLast_append_getLast hQ)
    simpa [List.map_append] using hsplit

theorem positiveCoefficientWord_eval
    (Q : List (Fin 2)) (f r : ℤ) :
    MultipleHNNFlat.eval A0 B0 phi0 (positiveCoefficientWord Q f r) =
      d3 ^ f * positive3 Q * e3 ^ r := by
  change MultipleHNNFlat.eval A0 B0 phi0
      (positiveCoefficientWord Q f r) =
    hnnD ^ f * modelPositive Q * hnnE ^ r
  by_cases hQ : Q = []
  · subst Q
    simp [positiveCoefficientWord, MultipleHNNFlat.eval, map_mul, map_zpow,
      modelPositive, Thue.evalPositive]
    rfl
  · simp only [positiveCoefficientWord, hQ, ↓reduceDIte,
      MultipleHNNFlat.eval]
    rw [run_eval Q hQ 1 (e ^ r), stableProduct_one]
    simp [map_zpow, mul_assoc]
    rfl

/-! ## Positivity extracted from signature equality -/

theorem allPositive_iff_forall_sign (letters : List (Basis × Bool)) :
    AllPositive letters ↔ ∀ x ∈ letters, x.2 = true := by
  induction letters with
  | nil => simp [AllPositive]
  | cons x xs ih => simp [AllPositive, ih]

theorem factorRun_has_own_sign
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (x : Basis × Bool)
    (lastCoeff : BorisovHNNModel.Base) :
    ∃ s ∈ factorRun rules hne x lastCoeff,
      s.sign = signedUnit x.2 := by
  let s := (factorRun rules hne x lastCoeff).head
    (factorRun_ne_nil rules hne x lastCoeff)
  refine ⟨s, List.head_mem (factorRun_ne_nil rules hne x lastCoeff), ?_⟩
  exact factorRun_head_sign rules hne x lastCoeff

theorem expansionTail_has_factor_sign
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (letters : List (Basis × Bool))
    (x : Basis × Bool) (hx : x ∈ letters) :
    ∃ s ∈ expansionTail rules hne letters,
      s.sign = signedUnit x.2 := by
  induction letters with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mem_cons] at hx
      rw [expansionTail]
      rcases hx with rfl | hx
      · rcases factorRun_has_own_sign rules hne x
          (suffix x * nextPrefix ys) with ⟨s, hs, hsign⟩
        exact ⟨s, List.mem_append_left _ hs, hsign⟩
      · rcases ih hx with ⟨s, hs, hsign⟩
        exact ⟨s, List.mem_append_right _ hs, hsign⟩

/-- If a literal rank-five expansion has the same signature as a positive
stable word, every displayed rank-five letter is positive. -/
theorem allPositive_of_expansion_signature
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (letters : List (Basis × Bool))
    (hreduced : letters.IsChain
      (fun x y ↦ x.1 = y.1 → x.2 = y.2))
    (Q : List (Fin 2))
    (hsignature :
      MultipleHNNFlat.signature A0 B0
          (expansionWord rules hne letters hreduced) =
        Q.map (fun beta ↦ (beta, (1 : ℤˣ)))) :
    AllPositive letters := by
  rw [allPositive_iff_forall_sign]
  intro x hx
  rcases expansionTail_has_factor_sign rules hne letters x hx with
    ⟨s, hs, hsSign⟩
  have hpair : (s.color, s.sign) ∈
      MultipleHNNFlat.signature A0 B0
        (expansionWord rules hne letters hreduced) :=
    List.mem_map.2 ⟨s, by simpa [expansionWord] using hs, rfl⟩
  rw [hsignature] at hpair
  rcases List.mem_map.1 hpair with ⟨beta, _, hp⟩
  have hsOne : s.sign = 1 := (congrArg Prod.snd hp).symm
  rw [hsSign] at hsOne
  cases hxsign : x.2
  · simp [signedUnit, hxsign] at hsOne
  · rfl

/-- Signature comparison supplies the complete positivity half of Borisov's
page-771 coefficient parser for the source basis. -/
theorem u_allPositive_of_coefficient_eq
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) (f r : ℤ)
    (w : FreeGroup Basis)
    (heval : uLift datum w = d3 ^ f * positive3 Q * e3 ^ r) :
    AllPositive w.toWord := by
  have hflat : MultipleHNNFlat.eval A0 B0 phi0 (uExpansion datum w) =
      MultipleHNNFlat.eval A0 B0 phi0 (positiveCoefficientWord Q f r) := by
    rw [uExpansion_eval, positiveCoefficientWord_eval,
      ← g0Equiv_apply, g0Equiv_uLift, heval]
  have hsig := signature_eq_of_eval_eq A0 B0 phi0
    (uExpansion datum w) (positiveCoefficientWord Q f r) hflat
  rw [positiveCoefficientWord_signature] at hsig
  exact allPositive_of_expansion_signature datum.F datum.F_nonempty w.toWord
    (FreeGroup.isReduced_toWord (x := w)) Q (by
      simpa [uExpansion] using hsig)

/-- Target-basis counterpart of `u_allPositive_of_coefficient_eq`. -/
theorem v_allPositive_of_coefficient_eq
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) (f r : ℤ)
    (w : FreeGroup Basis)
    (heval : vLift datum w = d3 ^ f * positive3 Q * e3 ^ r) :
    AllPositive w.toWord := by
  have hflat : MultipleHNNFlat.eval A0 B0 phi0 (vExpansion datum w) =
      MultipleHNNFlat.eval A0 B0 phi0 (positiveCoefficientWord Q f r) := by
    rw [vExpansion_eval, positiveCoefficientWord_eval,
      ← g0Equiv_apply, g0Equiv_vLift, heval]
  have hsig := signature_eq_of_eval_eq A0 B0 phi0
    (vExpansion datum w) (positiveCoefficientWord Q f r) hflat
  rw [positiveCoefficientWord_signature] at hsig
  exact allPositive_of_expansion_signature datum.E datum.E_nonempty w.toWord
    (FreeGroup.isReduced_toWord (x := w)) Q (by
      simpa [vExpansion] using hsig)

end

end BorisovCoefficientSignComparison
end Undecidability
