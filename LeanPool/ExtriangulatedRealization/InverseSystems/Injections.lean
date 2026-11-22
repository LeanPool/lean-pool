/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Criterion.TheoremB
public import LeanPool.ExtriangulatedRealization.InverseSystems.Linearization
public import LeanPool.ExtriangulatedRealization.InverseSystems.Omega1

/-!
# Example 4.2: injections of countable ordinals into `ℕ`

For a countable ordinal `i`, let `S_i` be the set of injections `[0, i) ↪ ℕ` whose image misses
infinitely many numbers, with restriction as transition maps (Bergman, Wofsey). Restriction is
surjective: enumerate the missed numbers, send the countably many new points injectively to the
even positions of this enumeration, and the odd positions stay missed. A compatible family
would give an injection `ω₁ ↪ ℕ`, so `lim S = ∅`, while `S_0` is a single point. By Lemma 4.1 and
Theorem B, `C(k^(S))` has no triangulated embedding.
-/

@[expose] public section

namespace ExtriangulatedRealization

namespace Injections

open CategoryTheory Opposite Statement Omega1

universe u v' u'

/-- Injections `[0, i) ↪ ℕ` missing infinitely many numbers. -/
def Inj (i : Omega1.{u}) : Type u :=
  {f : Set.Iio i → ℕ // Function.Injective f ∧ (Set.range f)ᶜ.Infinite}

/-- Restriction of an injection to a smaller initial segment. -/
def res {a b : Omega1.{u}} (h : a ≤ b) (f : Inj b) : Inj a :=
  ⟨fun ξ => f.1 ⟨ξ.1, lt_of_lt_of_le ξ.2 h⟩,
    fun ξ η hξη => Subtype.ext (Subtype.mk.inj (f.2.1 hξη)),
    f.2.2.mono (Set.compl_subset_compl.mpr (by rintro _ ⟨ξ, rfl⟩; exact ⟨_, rfl⟩))⟩

/-- The inverse system of Example 4.2. -/
def system : (Omega1.{u})ᵒᵖ ⥤ Type u where
  obj i := Inj i.unop
  map h := TypeCat.ofHom (res (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma system_map_apply {a b : Omega1.{u}} (h : a ≤ b) (f : system.obj (op b)) :
    system.map (homOfLE h).op f = res h f := rfl

/-- The transition maps of Example 4.2 are surjective. -/
lemma system_map_surjective {a b : Omega1.{u}} (h : a ≤ b) :
    Function.Surjective (system.map (homOfLE h).op) := by
  classical
  intro f
  let φ := Set.Infinite.natEmbedding _ f.2.2
  have := (countable_Iio b).to_subtype
  obtain ⟨ι, hι⟩ := Countable.exists_injective_nat (Set.Iio b)
  let g : Set.Iio b → ℕ := fun ξ =>
    if hξ : ξ.1 < a then f.1 ⟨ξ.1, hξ⟩ else (φ (2 * ι ξ) : ℕ)
  have hφ : ∀ n, (φ n : ℕ) ∉ Set.range f.1 := fun n => (φ n).2
  have hφinj : ∀ m n, (φ m : ℕ) = φ n → m = n := fun m n hmn =>
    φ.injective (Subtype.ext hmn)
  have hginj : Function.Injective g := by
    intro ξ η hξη
    by_cases hξ : ξ.1 < a <;> by_cases hη : η.1 < a <;>
      simp only [g, hξ, hη, ↓reduceDIte] at hξη
    · exact Subtype.ext (Subtype.mk.inj (f.2.1 hξη))
    · exact absurd ⟨_, hξη⟩ (hφ _)
    · exact absurd ⟨_, hξη.symm⟩ (hφ _)
    · exact hι (by have := hφinj _ _ hξη; omega)
  have hodd : Set.range (fun n => (φ (2 * n + 1) : ℕ)) ⊆ (Set.range g)ᶜ := by
    rintro _ ⟨n, rfl⟩ ⟨ξ, hξ⟩
    by_cases hξa : ξ.1 < a <;> simp only [g, hξa, ↓reduceDIte] at hξ
    · exact hφ _ ⟨_, hξ⟩
    · have := hφinj _ _ hξ
      omega
  have hinf : (Set.range g)ᶜ.Infinite :=
    (Set.infinite_range_of_injective fun m n hmn => by
      have := hφinj _ _ hmn
      omega).mono hodd
  refine ⟨⟨g, hginj, hinf⟩, Subtype.ext (funext fun ξ => ?_)⟩
  exact dite_eq_left (show ξ.1 < a from ξ.2)

/-- A compatible family of injections would give an injection `ω₁ ↪ ℕ`. -/
theorem system_no_branch :
    ¬ ∃ s : ∀ i, system.obj (op i), ∀ {a b : Omega1.{u}} (h : a ≤ b),
      system.map (homOfLE h).op (s b) = s a := by
  rintro ⟨s, hs⟩
  choose up hup using Omega1.exists_gt.{u}
  have hval : ∀ {a b : Omega1.{u}} (h : a ≤ b) (ξ : Omega1.{u}) (hξ : ξ < a),
      (s b).1 ⟨ξ, lt_of_lt_of_le hξ h⟩ = (s a).1 ⟨ξ, hξ⟩ := fun h ξ hξ => by
    rw [← hs h]
    rfl
  let B : Omega1.{u} → ℕ := fun ξ => (s (up ξ)).1 ⟨ξ, hup ξ⟩
  have hB : ∀ ξ α (hξ : ξ < α), (s α).1 ⟨ξ, hξ⟩ = B ξ := fun ξ α hξ => by
    rw [← hval (le_sup_left : α ≤ α ⊔ up ξ) ξ hξ,
      hval (le_sup_right : up ξ ≤ α ⊔ up ξ) ξ (hup ξ)]
  have hinj : Function.Injective B := fun ξ η hξη => by
    let α := up ξ ⊔ up η
    have hξ : ξ < α := lt_of_lt_of_le (hup ξ) le_sup_left
    have hη : η < α := lt_of_lt_of_le (hup η) le_sup_right
    rw [← hB ξ α hξ, ← hB η α hη] at hξη
    exact congrArg Subtype.val ((s α).2.1 hξη)
  exact Omega1.not_countable hinj.countable

/-- The least countable ordinal. -/
noncomputable def bot : Omega1.{u} := ofOrd 0 (Ordinal.omega_pos 1)

lemma isEmpty_Iio_bot : IsEmpty (Set.Iio bot.{u}) := by
  refine ⟨fun ⟨δ, hδ⟩ => ?_⟩
  have := ord_strictMono hδ
  rw [bot, ord_ofOrd] at this
  exact absurd this (by simp)

/-- `S_0` consists solely of the empty function. -/
lemma system_obj_bot : Nonempty (system.obj (op bot.{u})) ∧
    Subsingleton (system.obj (op bot.{u})) := by
  have := isEmpty_Iio_bot.{u}
  refine ⟨⟨⟨isEmptyElim, fun ξ => isEmptyElim ξ, ?_⟩⟩,
    ⟨fun f g => Subtype.ext (funext isEmptyElim)⟩⟩
  rw [Set.range_eq_empty, Set.compl_empty]
  exact Set.infinite_univ

/-- **Example 4.2.** The linearization `D'` of the injection system has surjective transition
maps and `D'_0 = k`, but `C(D')` has no triangulated embedding. -/
theorem example_4_2 (k : Type u) [Field k] :
    HasSurjectiveTransitions (linearize system k) ∧
      ¬ (cdData (linearize system k)).HasTriangulatedEmbedding.{_, _, _, _, v', u'} := by
  have hD : HasSurjectiveTransitions (linearize system k) :=
    linearize_hasSurjectiveTransitions _ k fun h => system_map_surjective h
  refine ⟨hD, fun h => ?_⟩
  have hP := theoremB_necessity.{u, v', u'} k _ _ hD h
  exact linearize_not_projectionsSurjective _ k (fun _ hT => Omega1.bddAbove_of_countable hT)
    system_no_branch bot (system_obj_bot.1.some) hP

end Injections

end ExtriangulatedRealization
