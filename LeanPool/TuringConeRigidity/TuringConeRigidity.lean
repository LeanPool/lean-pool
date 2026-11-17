/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeRigidity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CoverageMain

/-!
# A one-sided Borel obstruction to isomorphisms with proper Turing cones

For `e : Degree ≃o Set.Ici a`, define `pullback e x = e.symm (a ⊔ x)`.
If this map has a Borel lift on oracles, then `a = ⊥`.

This is a CONDITIONAL result. In particular, this file does not assert that every
cone isomorphism has such a lift. The existing `BorelRepresentation` theorem is
about automorphisms of the whole degree structure and cannot simply be applied
to an isomorphism whose codomain is a cone.

Only an inverse lift is needed: four-value recovery and category avoidance give
`(e x).val ≤ a ⊔ x`. At `x = a` this implies `e a = e ⊥`, hence `a = ⊥`.
There is no need for a second, forward lift or a formalization of relative degrees.

All imports are from the analytic/category portion of the rigidity development;
we do not import the global automorphism representation theorem.
-/


@[expose] public section


open Set Filter Topology

namespace OAI.TuringRigidity.ConeRigidity

/-- Joining with `a`, regarded as a point of the cone above `a`. -/
def coneJoin (a x : Degree) : Set.Ici a := ⟨a ⊔ x, Set.mem_Ici.mpr le_sup_left⟩

/-- The inverse of a cone isomorphism, precomposed with joining with its base. -/
def pullback {a : Degree} (e : Degree ≃o Set.Ici a) (x : Degree) : Degree :=
  e.symm (coneJoin a x)

@[simp] theorem apply_pullback_val {a : Degree} (e : Degree ≃o Set.Ici a)
    (x : Degree) : (e (pullback e x)).val = a ⊔ x := by
  change (e (e.symm (coneJoin a x))).val = a ⊔ x
  rw [e.apply_symm_apply]
  rfl

theorem pullback_mono {a : Degree} (e : Degree ≃o Set.Ici a) :
    Monotone (pullback e) := by
  intro x y hxy
  apply e.symm.monotone
  change a ⊔ x ≤ a ⊔ y
  exact sup_le_sup_left hxy a

theorem pullback_sup {a : Degree} (e : Degree ≃o Set.Ici a) (x y : Degree) :
    pullback e (x ⊔ y) = pullback e x ⊔ pullback e y := by
  have h : coneJoin a (x ⊔ y) = coneJoin a x ⊔ coneJoin a y := by
    apply Subtype.ext
    change a ⊔ (x ⊔ y) = (a ⊔ x) ⊔ (a ⊔ y)
    apply le_antisymm
    · exact sup_le
        (le_trans le_sup_left le_sup_left)
        (sup_le (le_trans le_sup_right le_sup_left)
          (le_trans le_sup_right le_sup_right))
    · exact sup_le
        (sup_le le_sup_left (le_trans le_sup_left le_sup_right))
        (sup_le le_sup_left (le_trans le_sup_right le_sup_right))
  unfold pullback
  rw [h, e.symm.map_sup]

/-- Every order isomorphism onto a principal cone sends bottom to its base. -/
theorem map_bot_val {a : Degree} (e : Degree ≃o Set.Ici a) :
    (e ⊥).val = a := by
  have h : e ⊥ ≤ e (e.symm (⟨a, Set.mem_Ici.mpr le_rfl⟩ : Set.Ici a)) :=
    e.monotone bot_le
  rw [e.apply_symm_apply] at h
  exact le_antisymm h (Set.mem_Ici.mp (e ⊥).property)

/-- The purely order-theoretic endgame needs a bound only at the base degree. -/
theorem eq_bot_of_image_base_le {a : Degree} (e : Degree ≃o Set.Ici a)
    (h : (e a).val ≤ a) : a = ⊥ := by
  have hea : (e a).val = a := le_antisymm h (Set.mem_Ici.mp (e a).property)
  apply e.injective
  exact Subtype.ext (hea.trans (map_bot_val e).symm)

/-- The representation hypothesis still to be established for an arbitrary cone
isomorphism. It is stated on all oracles, not just on a comeager subset. -/
def InverseBorelLift {a : Degree} (e : Degree ≃o Set.Ici a) : Prop :=
  ∃ F : Oracle → Oracle, Measurable F ∧
    ∀ X : Oracle, degree (F X) = pullback e (degree X)

/-- Although `pullback e` need not be injective, its real-valued lift has countable
fibers: all reals in one fiber have cuts reducible to one fixed oracle. -/
theorem inverse_lift_countable_fibers {a : Degree} (e : Degree ≃o Set.Ici a)
    (F : ℝ → Oracle) (hF : ∀ t, degree (F t) = pullback e (realDegree t)) :
    ∀ B : Oracle, {t : ℝ | F t = B}.Countable := by
  intro B
  by_cases hne : ∃ t, F t = B
  · obtain ⟨t₀, ht₀⟩ := hne
    obtain ⟨C, hC⟩ := degree_surjective (a ⊔ realDegree t₀)
    apply ((countable_reduces C).preimage cut_injective).mono
    intro t ht
    have heq : pullback e (realDegree t) = pullback e (realDegree t₀) :=
      (hF t).symm.trans ((congrArg degree (ht.trans ht₀.symm)).trans (hF t₀))
    have hjoin : a ⊔ realDegree t = a ⊔ realDegree t₀ := by
      have h := congrArg (fun d : Degree => (e d).val) heq
      simpa only [apply_pullback_val] using h
    change realDegree t ≤ degree C
    rw [hC, ← hjoin]
    exact le_sup_right
  · have hempty : {t : ℝ | F t = B} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hne ⟨t, ht⟩
    rw [hempty]
    exact Set.countable_empty

/-- The four-tuple upper bound only uses monotonicity of the represented degree
map. The automorphism assumption in the original assembly lemma is unnecessary. -/
theorem fourTuple_bound_of_monotone (g : Degree → Degree) (hg : Monotone g)
    (F : ℝ → Oracle) (hF : ∀ x, degree (F x) = g (realDegree x))
    (t u v : ℝ) (δ : ℚ) :
    degree (fourTuple F t u v δ) ≤ g (realDegree t ⊔ realDegree u ⊔ realDegree v) := by
  let b := realDegree t ⊔ realDegree u ⊔ realDegree v
  have ht : realDegree t ≤ b := le_trans le_sup_left le_sup_left
  have hu : realDegree u ≤ b := le_trans le_sup_right le_sup_left
  have hv : realDegree v ≤ b := le_sup_right
  have huv : realDegree (u - v) ≤ b :=
    (cut_arithmetic.sub u v).trans (sup_le hu hv)
  have hvu : realDegree (v - u) ≤ b :=
    (cut_arithmetic.sub v u).trans (sup_le hv hu)
  have hδt : realDegree ((δ : ℝ) * t) ≤ b := (cut_arithmetic.smul δ t).trans ht
  have ht1 : realDegree (t - 1) ≤ realDegree t := by
    simpa [sub_eq_add_neg] using cut_arithmetic.translate t (-1)
  have hδt1 : realDegree ((δ : ℝ) * (t - 1)) ≤ b :=
    (cut_arithmetic.smul δ (t - 1)).trans (ht1.trans ht)
  have h3 : realDegree (v - u + (δ : ℝ) * t) ≤ b :=
    (cut_arithmetic.add _ _).trans (sup_le hvu hδt)
  have h4 : realDegree (v - u + (δ : ℝ) * (t - 1)) ≤ b :=
    (cut_arithmetic.add _ _).trans (sup_le hvu hδt1)
  have hvalue : ∀ x : ℝ, realDegree x ≤ b → degree (F x) ≤ g b := by
    intro x hx
    rw [hF]
    exact hg hx
  change ((degree (F u) ⊔ degree (F (u - v))) ⊔
    degree (F (v - u + (δ : ℝ) * t))) ⊔
    degree (F (v - u + (δ : ℝ) * (t - 1))) ≤ g b
  exact sup_le (sup_le (sup_le (hvalue _ hu) (hvalue _ huv))
    (hvalue _ h3)) (hvalue _ h4)

/-- Remove two generic real degrees from an upper bound. The fixed base degree
`b` may already include a noncomputable oracle. -/
theorem le_of_residual_le_join (c b : Degree)
    (h : {p : ℝ × ℝ | c ≤ b ⊔ realDegree p.1 ⊔ realDegree p.2}
      ∈ residual (ℝ × ℝ)) : c ≤ b := by
  by_contra hnle
  obtain ⟨X, hX⟩ := degree_surjective b
  obtain ⟨Y, hY⟩ := degree_surjective c
  have hnred : ¬ Reduces Y X := by
    intro hred
    apply hnle
    change degree Y ≤ degree X at hred
    simpa only [hY, hX] using hred
  have hmeager := CategorySearch.category_avoidance X Y hnred
  obtain ⟨p, hp, hpnot⟩ := (dense_of_mem_residual (inter_mem h hmeager)).nonempty
  apply hpnot
  change degree Y ≤ degree X ⊔ realDegree p.1 ⊔ realDegree p.2
  rw [hY, hX]
  exact Set.mem_ofPred_eq.mp hp

/-- One Borel inverse lift supplies the upper half of the proposed squeeze. -/
theorem image_le_join_of_inverse_borel_lift {a : Degree} (e : Degree ≃o Set.Ici a)
    (hrep : InverseBorelLift e) (x : Degree) : (e x).val ≤ a ⊔ x := by
  by_cases hx : x = ⊥
  · subst x
    rw [map_bot_val, sup_bot_eq]
  obtain ⟨t, ht, ht0, ht1, rfl⟩ := irrational_degree_coverage x hx
  obtain ⟨F₀, hmeas₀, hF₀⟩ := hrep
  let F : ℝ → Oracle := fun u => F₀ (cut u)
  have hmeas : Measurable F := hmeas₀.comp cut_measurable
  have hF : ∀ u, degree (F u) = pullback e (realDegree u) := fun u => hF₀ (cut u)
  have hfiber := inverse_lift_countable_fibers e F hF
  have hadd : ∀ u v, Reduces (F (u + v)) (join (F u) (F v)) := by
    intro u v
    change degree (F (u + v)) ≤ degree (F u) ⊔ degree (F v)
    rw [hF, hF, hF, ← pullback_sup]
    exact pullback_mono e (cut_arithmetic.add u v)
  obtain ⟨G, hG, hrecovery⟩ := four_value_recovery F hmeas hfiber hadd t ht ht0 ht1
  apply le_of_residual_le_join (e (realDegree t)).val (a ⊔ realDegree t)
  filter_upwards [hG] with p hp
  obtain ⟨δ, _, _, hδ⟩ := hrecovery p hp
  have hle : realDegree t ≤ pullback e
      (realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2) :=
    le_trans hδ (fourTuple_bound_of_monotone (pullback e) (pullback_mono e)
      F hF t p.1 p.2 δ)
  have hmap := e.monotone hle
  have hval : (e (realDegree t)).val ≤
      (e (pullback e (realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2))).val := hmap
  rw [apply_pullback_val] at hval
  simpa only [sup_assoc] using hval

/-- A cone isomorphism with a Borel inverse lift has trivial base. -/
theorem eq_bot_of_inverse_borel_lift {a : Degree} (e : Degree ≃o Set.Ici a)
    (hrep : InverseBorelLift e) : a = ⊥ := by
  apply eq_bot_of_image_base_le e
  simpa only [sup_idem] using image_le_join_of_inverse_borel_lift e hrep a

/-- No isomorphism with a proper cone can have the inverse lift specified above. -/
theorem no_inverse_borel_lift_of_ne_bot {a : Degree} (ha : a ≠ ⊥)
    (e : Degree ≃o Set.Ici a) : ¬ InverseBorelLift e :=
  fun hrep => ha (eq_bot_of_inverse_borel_lift e hrep)

/-- An explicit interface for the remaining representation problem. This is not
an unconditional non-isomorphism theorem: `hrep` is a mathematical hypothesis. -/
theorem no_cone_iso_of_inverse_representation {a : Degree} (ha : a ≠ ⊥)
    (hrep : ∀ e : Degree ≃o Set.Ici a, InverseBorelLift e) :
    ¬ Nonempty (Degree ≃o Set.Ici a) := by
  rintro ⟨e⟩
  exact no_inverse_borel_lift_of_ne_bot ha e (hrep e)

end OAI.TuringRigidity.ConeRigidity
