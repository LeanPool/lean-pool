/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.AssertionIV

/-!
# Borisov's Assertion V

This file proves the support statement called Assertion V in Borisov's
normal-form argument.  A reduced word in the displayed rank-five basis is
expanded literally in the two stable letters.  Flat Britton normal form then
detects every stable-letter color which occurs in that expansion.
-/

@[expose] public section

namespace Undecidability
namespace BorisovAssertionV

open BorisovHNNModel
open BorisovIntersections
open BorisovG0HNN
open BorisovG0NormalForm
open BorisovAssertionIV
open BorisovAssertionIVBoundary

noncomputable section

/-! ## Literal color support -/

theorem run_color_map (colors : List (Fin 2)) (hne : colors ≠ [])
    (u : ℤˣ) (lastCoeff : BorisovHNNModel.Base) :
    (run colors hne u lastCoeff).map
        MultipleHNNFlat.Syllable.color = colors := by
  unfold run
  rw [List.map_append, List.map_map, List.map_singleton]
  have hdrop : colors.dropLast.map
      (MultipleHNNFlat.Syllable.color ∘ fun color =>
        ({ color := color, sign := u, coeff := 1 } : FlatSyllable)) =
      colors.dropLast := by
    conv_rhs => rw [← List.map_id' colors.dropLast]
    apply List.map_congr_left
    intro color _
    rfl
  rw [hdrop]
  exact List.dropLast_append_getLast hne

theorem run_contains_color (colors : List (Fin 2)) (hne : colors ≠ [])
    (u : ℤˣ) (lastCoeff : BorisovHNNModel.Base) {color : Fin 2}
    (hcolor : color ∈ colors) :
    ∃ s ∈ run colors hne u lastCoeff, s.color = color := by
  have hmapped : color ∈
      (run colors hne u lastCoeff).map
        MultipleHNNFlat.Syllable.color := by
    rw [run_color_map]
    exact hcolor
  simpa only [List.mem_map] using hmapped

theorem factorRun_contains_color
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (x : Basis × Bool) (lastCoeff : BorisovHNNModel.Base)
    {color : Fin 2}
    (hcolor : color ∈ factorColors rules x) :
    ∃ s ∈ factorRun rules hne x lastCoeff, s.color = color :=
  run_contains_color _ _ _ _ hcolor

theorem expansionTail_contains_color
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (letters : List (Basis × Bool)) (x : Basis × Bool)
    (hx : x ∈ letters) {color : Fin 2}
    (hcolor : color ∈ factorColors rules x) :
    ∃ s ∈ expansionTail rules hne letters, s.color = color := by
  induction letters with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mem_cons] at hx
      rw [expansionTail]
      rcases hx with rfl | hx
      · rcases factorRun_contains_color rules hne x
          (suffix x * nextPrefix ys) hcolor with ⟨s, hs, hc⟩
        exact ⟨s, List.mem_append_left _ hs, hc⟩
      · rcases ih hx with ⟨s, hs, hc⟩
        exact ⟨s, List.mem_append_right _ hs, hc⟩

theorem expansionTail_contains_of_usesStable
    (rules : Fin 3 → List (Fin 2)) (hne : ∀ i, rules i ≠ [])
    (hsupport : ∀ i, Thue.ContainsBoth (rules i))
    (w : FreeGroup Basis) (gamma : Fin 2)
    (huses : UsesStable w gamma) :
    ∃ s ∈ expansionTail rules hne w.toWord, s.color = gamma := by
  rcases huses with ⟨⟨q, sign⟩, hletter, hq⟩
  apply expansionTail_contains_color rules hne w.toWord (q, sign) hletter
  cases q with
  | inl beta =>
      change beta = gamma at hq
      subst beta
      cases sign <;> simp [factorColors]
  | inr i =>
      have hgamma : gamma ∈ rules i := by
        fin_cases gamma
        · exact (hsupport i).1
        · exact (hsupport i).2
      cases sign <;> simpa [factorColors] using hgamma

theorem uExpansion_contains_of_usesStable
    (datum : Thue.StandingDatum) (w : FreeGroup Basis) (gamma : Fin 2)
    (huses : UsesStable w gamma) :
    ∃ s ∈ (uExpansion datum w).toList, s.color = gamma := by
  simpa [uExpansion, expansionWord] using
    expansionTail_contains_of_usesStable datum.F datum.F_nonempty
      datum.F_support w gamma huses

theorem vExpansion_contains_of_usesStable
    (datum : Thue.StandingDatum) (w : FreeGroup Basis) (gamma : Fin 2)
    (huses : UsesStable w gamma) :
    ∃ s ∈ (vExpansion datum w).toList, s.color = gamma := by
  simpa [vExpansion, expansionWord] using
    expansionTail_contains_of_usesStable datum.E datum.E_nonempty
      datum.E_support w gamma huses

/-- A basis expansion with its evaluation, reducedness, and stable-letter occurrence properties. -/
structure ExpansionWitness where
  /-- The group-valued basis being expanded. -/
  basis : Basis → G0
  /-- The flat expansion assigned to each free basis word. -/
  word : FreeGroup Basis → FlatWord
  contains : ∀ w gamma, UsesStable w gamma →
    ∃ s ∈ (word w).toList, s.color = gamma
  eval : ∀ w, MultipleHNNFlat.eval A0 B0 phi0 (word w) =
    toHNN (FreeGroup.lift basis w)

/-- The expansion witness for the left-rule basis. -/
def uWitness (datum : Thue.StandingDatum) : ExpansionWitness where
  basis := uBasis datum
  word := uExpansion datum
  contains := uExpansion_contains_of_usesStable datum
  eval := uExpansion_eval datum

/-- The expansion witness for the right-rule basis. -/
def vWitness (datum : Thue.StandingDatum) : ExpansionWitness where
  basis := vBasis datum
  word := vExpansion datum
  contains := vExpansion_contains_of_usesStable datum
  eval := vExpansion_eval datum

/-! ## The base subgroup -/

theorem toHNN_mem_base_of_mem_DE {x : G0} (hx : x ∈ DE) :
    toHNN x ∈
      MonoidHom.range (MultipleHNN.baseEmbedding A0 B0 phi0) := by
  let H := (MonoidHom.range
    (MultipleHNN.baseEmbedding A0 B0 phi0)).comap toHNN
  have hle : DE ≤ H := by
    unfold DE
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨BorisovHNNModel.d, rfl⟩
    · exact ⟨BorisovHNNModel.e, rfl⟩
  exact hle hx

private theorem not_usesStable_of_mem_DE
    (M : ExpansionWitness) (w : FreeGroup Basis)
    (hmem : FreeGroup.lift M.basis w ∈ DE)
    (gamma : Fin 2) : ¬ UsesStable w gamma := by
  intro huses
  have hnonempty : (M.word w).toList ≠ [] := by
    intro hempty
    rcases M.contains w gamma huses with ⟨s, hs, _⟩
    simp [hempty] at hs
  have hnot := MultipleHNNFlat.eval_not_mem_base A0 B0 phi0
    (M.word w) hnonempty
  apply hnot
  rw [M.eval]
  exact toHNN_mem_base_of_mem_DE hmem

/-! ## The subgroup `J 0` -/

private theorem not_uses_one_of_mem_J_zero
    (M : ExpansionWitness) (w : FreeGroup Basis)
    (hmem : FreeGroup.lift M.basis w ∈ J 0) :
    ¬ UsesStable w 1 := by
  intro huses
  have hcolor := M.contains w 1 huses
  have hnot := MultipleHNNFlat.eval_not_mem_stageOne_of_contains_color_one
    A0 B0 phi0 (M.word w) hcolor
  apply hnot
  rw [M.eval]
  exact toHNN_mem_stageOne_of_mem_J_zero hmem

/-! ## Swapping the two stable letters -/

/-- The endomorphism of the concrete HNN model induced by interchanging the
two symmetric stable generators of the presentation. -/
def swapHNN : MultipleHNN.Extension A0 B0 phi0 →*
    MultipleHNN.Extension A0 B0 phi0 :=
  swappedToHNN.comp fromHNN

@[simp] theorem swapHNN_toHNN (x : G0) :
    swapHNN (toHNN x) = swappedToHNN x := by
  have h := DFunLike.congr_fun fromHNN_comp_toHNN x
  change fromHNN (toHNN x) = x at h
  change swappedToHNN (fromHNN (toHNN x)) = swappedToHNN x
  rw [h]

@[simp] theorem swapHNN_hnnD : swapHNN hnnD = hnnD := by
  change swappedToHNN (fromHNN hnnD) = hnnD
  rw [fromHNN_hnnD, presentedD_eq_of, swappedToHNN_of]
  rfl

@[simp] theorem swapHNN_hnnE : swapHNN hnnE = hnnE := by
  change swappedToHNN (fromHNN hnnE) = hnnE
  rw [fromHNN_hnnE, presentedE_eq_of, swappedToHNN_of]
  rfl

@[simp] theorem swapHNN_hnnS1 : swapHNN hnnS1 = hnnS2 := by
  change swappedToHNN (fromHNN hnnS1) = hnnS2
  rw [fromHNN_hnnS1, presentedS1_eq_of, swappedToHNN_of]
  rfl

@[simp] theorem swapHNN_hnnS2 : swapHNN hnnS2 = hnnS1 := by
  change swappedToHNN (fromHNN hnnS2) = hnnS1
  rw [fromHNN_hnnS2, presentedS2_eq_of, swappedToHNN_of]
  rfl

private theorem swapHNN_comp_baseToG0HNN :
    swapHNN.comp baseToG0HNN = baseToG0HNN := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · change swapHNN hnnD = hnnD
    exact swapHNN_hnnD
  · change swapHNN hnnE = hnnE
    exact swapHNN_hnnE

theorem swapHNN_baseEmbedding (g : BorisovHNNModel.Base) :
    swapHNN (MultipleHNN.baseEmbedding A0 B0 phi0 g) =
      MultipleHNN.baseEmbedding A0 B0 phi0 g := by
  change swapHNN (baseToG0HNN g) = baseToG0HNN g
  exact DFunLike.congr_fun swapHNN_comp_baseToG0HNN g

/-- Exchange the two stable-letter colors. -/
def swapColor : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

theorem swapColor_injective : Function.Injective swapColor := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp [swapColor] at h ⊢

@[simp] theorem swapHNN_stableLetter (color : Fin 2) :
    swapHNN (MultipleHNNFlat.stableLetter A0 B0 phi0 color) =
      MultipleHNNFlat.stableLetter A0 B0 phi0 (swapColor color) := by
  fin_cases color
  · exact swapHNN_hnnS1
  · exact swapHNN_hnnS2

/-- Exchange the stable-letter color of a syllable while retaining its sign and coefficient. -/
def swapSyllable (s : FlatSyllable) : FlatSyllable where
  color := swapColor s.color
  sign := s.sign
  coeff := s.coeff

/-- Exchange the two stable-letter colors throughout a flat word. -/
def swapFlatWord (w : FlatWord) : FlatWord where
  head := w.head
  toList := w.toList.map swapSyllable
  chain := by
    rw [List.isChain_map]
    apply w.chain.imp
    intro a b hab hcolor hmem
    exact hab (swapColor_injective hcolor) hmem

theorem swapFlatWord_eval (w : FlatWord) :
    MultipleHNNFlat.eval A0 B0 phi0 (swapFlatWord w) =
      swapHNN (MultipleHNNFlat.eval A0 B0 phi0 w) := by
  unfold MultipleHNNFlat.eval
  simp only [swapFlatWord]
  rw [map_mul, swapHNN_baseEmbedding, map_list_prod]
  simp only [List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro s _
  simp only [Function.comp_apply, swapSyllable, map_mul, map_zpow,
    swapHNN_stableLetter, swapHNN_baseEmbedding]

theorem swapFlatWord_contains_one_of_contains_zero (w : FlatWord)
    (hzero : ∃ s ∈ w.toList, s.color = 0) :
    ∃ s ∈ (swapFlatWord w).toList, s.color = 1 := by
  rcases hzero with ⟨s, hs, hcolor⟩
  refine ⟨swapSyllable s, ?_, ?_⟩
  · change swapSyllable s ∈ w.toList.map swapSyllable
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  · simp [swapSyllable, swapColor, hcolor]

private theorem swappedExpansion_eval (M : ExpansionWitness)
    (w : FreeGroup Basis) :
    MultipleHNNFlat.eval A0 B0 phi0
        (swapFlatWord (M.word w)) =
      swappedToHNN (FreeGroup.lift M.basis w) := by
  rw [swapFlatWord_eval, M.eval, swapHNN_toHNN]

/-! ## The subgroup `J 1` -/

private theorem not_uses_zero_of_mem_J_one
    (M : ExpansionWitness) (w : FreeGroup Basis)
    (hmem : FreeGroup.lift M.basis w ∈ J 1) :
    ¬ UsesStable w 0 := by
  intro huses
  have hzero := M.contains w 0 huses
  have hone := swapFlatWord_contains_one_of_contains_zero
    (M.word w) hzero
  have hnot := MultipleHNNFlat.eval_not_mem_stageOne_of_contains_color_one
    A0 B0 phi0 (swapFlatWord (M.word w)) hone
  apply hnot
  rw [swappedExpansion_eval]
  exact swappedToHNN_mem_stageOne_of_mem_J_one hmem

/-! ## Assertion V -/

private theorem not_uses_of_mem_J
    (M : ExpansionWitness) (w : FreeGroup Basis) (beta gamma : Fin 2)
    (hmem : FreeGroup.lift M.basis w ∈ J beta) (hne : gamma ≠ beta) :
    ¬ UsesStable w gamma := by
  fin_cases beta <;> fin_cases gamma
  · exact (hne rfl).elim
  · exact not_uses_one_of_mem_J_zero M w hmem
  · exact not_uses_zero_of_mem_J_one M w hmem
  · exact (hne rfl).elim

/-- Borisov's Assertion V, for any proof of Assertion IV.  The argument is
independent of the particular proof object supplied for Assertion IV. -/
theorem assertionV (datum : Thue.StandingDatum) (hIV : AssertionIV datum) :
    AssertionV datum hIV := by
  exact
    { u_mem_J := not_uses_of_mem_J (uWitness datum)
      v_mem_J := not_uses_of_mem_J (vWitness datum)
      u_mem_DE := not_usesStable_of_mem_DE (uWitness datum)
      v_mem_DE := not_usesStable_of_mem_DE (vWitness datum) }

/-- The canonical unconditional package, using the proved Assertion IV. -/
theorem assertionV_canonical (datum : Thue.StandingDatum) :
    AssertionV datum (BorisovAssertionIV.assertionIV datum) :=
  assertionV datum (BorisovAssertionIV.assertionIV datum)

end

end BorisovAssertionV
end Undecidability

/-!
# Borisov's subgroup-intersection lemma

This file packages Borisov's Assertions IV and V into the four subgroup
intersections used in Lemma 3.5 of the paper.
-/

namespace Undecidability
namespace BorisovLemmaFourTwo

open BorisovIntersections

/-- Lemma 3.5 of the paper for the canonical first-stage presentation `G₀`. -/
theorem lemma4_2 (datum : Thue.StandingDatum) :
    (∀ beta : Fin 2,
      Uc datum ⊓ J beta = stableCyclic beta ∧
      Vc datum ⊓ J beta = stableCyclic beta) ∧
    Uc datum ⊓ DE = ⊥ ∧ Vc datum ⊓ DE = ⊥ :=
  BorisovIntersections.lemma4_2 datum
    (BorisovAssertionIV.assertionIV datum)
    (BorisovAssertionV.assertionV_canonical datum)

end BorisovLemmaFourTwo
end Undecidability
