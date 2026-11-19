/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeRigidity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRigidity

/-!
# Analytic rigidity for isomorphisms between two Turing cones

For `e : Set.Ici a ≃o Set.Ici b`, the joined inverse is
`pullback e x = (e.symm (b ⊔ x)).val`. A Borel oracle lift of this map forces
`e (a ⊔ x) ≤ b ⊔ x`. Lifts in both directions force equal bases and pointwise
identity. All representation hypotheses in this file are explicit; the
unconditional target `cones_orderIso_iff` is not asserted here.
-/


@[expose] public section


open Set Filter Topology

namespace OAI.TuringRigidity.TwoConeRigidity

open ConeRigidity (coneJoin fourTuple_bound_of_monotone le_of_residual_le_join)

/-- Apply the cone isomorphism after joining the input degree with the source base. -/
def imageJoin {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (x : Degree) : Degree :=
  (e (coneJoin a x)).val

/-- Apply the inverse cone isomorphism after joining the input degree with the target base. -/
def pullback {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (x : Degree) : Degree :=
  imageJoin e.symm x

theorem coneJoin_sup (a x y : Degree) :
    coneJoin a (x ⊔ y) = coneJoin a x ⊔ coneJoin a y := by
  apply Subtype.ext
  change a ⊔ (x ⊔ y) = (a ⊔ x) ⊔ (a ⊔ y)
  apply le_antisymm
  · exact sup_le (le_trans le_sup_left le_sup_left)
      (sup_le (le_trans le_sup_right le_sup_left)
        (le_trans le_sup_right le_sup_right))
  · exact sup_le (sup_le le_sup_left (le_trans le_sup_left le_sup_right))
      (sup_le le_sup_left (le_trans le_sup_right le_sup_right))

theorem imageJoin_mono {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    Monotone (imageJoin e) := by
  intro x y hxy
  exact e.monotone (show coneJoin a x ≤ coneJoin a y from sup_le_sup_left hxy a)

theorem imageJoin_sup {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (x y : Degree) :
    imageJoin e (x ⊔ y) = imageJoin e x ⊔ imageJoin e y := by
  unfold imageJoin
  rw [coneJoin_sup]
  exact congrArg Subtype.val (e.map_sup (coneJoin a x) (coneJoin a y))

theorem pullback_mono {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    Monotone (pullback e) := imageJoin_mono e.symm

theorem pullback_sup {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (x y : Degree) :
    pullback e (x ⊔ y) = pullback e x ⊔ pullback e y := imageJoin_sup e.symm x y

theorem base_le_pullback {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (x : Degree) :
    a ≤ pullback e x := (e.symm (coneJoin b x)).property

@[simp] theorem apply_pullback_val {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (x : Degree) : imageJoin e (pullback e x) = b ⊔ x := by
  have h : coneJoin a (pullback e x) = e.symm (coneJoin b x) :=
    Subtype.ext (sup_eq_right.mpr (base_le_pullback e x))
  change (e (coneJoin a (pullback e x))).val = b ⊔ x
  rw [h, e.apply_symm_apply]
  rfl

theorem map_base_val {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    (e ⟨a, Set.mem_Ici.mpr le_rfl⟩).val = b := by
  let a₀ : Set.Ici a := ⟨a, Set.mem_Ici.mpr le_rfl⟩
  let b₀ : Set.Ici b := ⟨b, Set.mem_Ici.mpr le_rfl⟩
  have h : e a₀ ≤ e (e.symm b₀) := e.monotone (e.symm b₀).property
  rw [e.apply_symm_apply] at h
  exact le_antisymm h (e a₀).property

@[simp] theorem imageJoin_bot {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    imageJoin e ⊥ = b := by
  have h : coneJoin a ⊥ = (⟨a, Set.mem_Ici.mpr le_rfl⟩ : Set.Ici a) :=
    Subtype.ext (sup_bot_eq a)
  unfold imageJoin
  rw [h]
  exact map_base_val e

/-- Convert an ordinary lower bound to a lower bound in the source cone. -/
theorem le_pullback_iff {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) (z x : Degree) :
    z ≤ pullback e x ↔ imageJoin e z ≤ b ⊔ x := by
  constructor
  · intro h
    have hsrc : coneJoin a z ≤ e.symm (coneJoin b x) :=
      sup_le (base_le_pullback e x) h
    have hmap : (e (coneJoin a z)).val ≤ (e (e.symm (coneJoin b x))).val :=
      e.monotone hsrc
    simpa only [e.apply_symm_apply, imageJoin, coneJoin] using hmap
  · intro h
    have hmap : e (coneJoin a z) ≤ e (e.symm (coneJoin b x)) := by
      rw [e.apply_symm_apply]
      exact h
    have hsrc : coneJoin a z ≤ e.symm (coneJoin b x) := e.le_iff_le.mp hmap
    exact le_trans le_sup_right hsrc

/-- Explicit regularity hypothesis for the joined inverse map. -/
def InverseBorelLift {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) : Prop :=
  ∃ F : Oracle → Oracle, Measurable F ∧
    ∀ X : Oracle, degree (F X) = pullback e (degree X)

theorem inverse_lift_countable_fibers {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (F : ℝ → Oracle) (hF : ∀ t, degree (F t) = pullback e (realDegree t)) :
    ∀ B : Oracle, {t : ℝ | F t = B}.Countable := by
  intro B
  by_cases hne : ∃ t, F t = B
  · obtain ⟨t₀, ht₀⟩ := hne
    obtain ⟨C, hC⟩ := degree_surjective (b ⊔ realDegree t₀)
    apply ((countable_reduces C).preimage cut_injective).mono
    intro t ht
    have heq : pullback e (realDegree t) = pullback e (realDegree t₀) :=
      (hF t).symm.trans ((congrArg degree (ht.trans ht₀.symm)).trans (hF t₀))
    have hjoin : b ⊔ realDegree t = b ⊔ realDegree t₀ := by
      simpa only [apply_pullback_val] using congrArg (imageJoin e) heq
    change realDegree t ≤ degree C
    rw [hC, ← hjoin]
    exact le_sup_right
  · have hempty : {t : ℝ | F t = B} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hne ⟨t, ht⟩
    rw [hempty]
    exact Set.countable_empty

/-- The target bound contains `b`, not the weaker extra join with `a`. -/
theorem imageJoin_le_of_inverse_borel_lift {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (hrep : InverseBorelLift e) (x : Degree) :
    imageJoin e x ≤ b ⊔ x := by
  by_cases hx : x = ⊥
  · subst x
    rw [imageJoin_bot, sup_bot_eq]
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
  apply le_of_residual_le_join (imageJoin e (realDegree t)) (b ⊔ realDegree t)
  filter_upwards [hG] with p hp
  obtain ⟨δ, _, _, hδ⟩ := hrecovery p hp
  have hle : realDegree t ≤ pullback e
      (realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2) :=
    le_trans hδ (fourTuple_bound_of_monotone (pullback e) (pullback_mono e)
      F hF t p.1 p.2 δ)
  have hval := (le_pullback_iff e _ _).mp hle
  simpa only [sup_assoc] using hval

/-- One inverse representative already forces the target base below the source. -/
theorem target_le_source_of_bounds {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (h : ∀ x, imageJoin e x ≤ b ⊔ x) : b ≤ a := by
  have hv : (e (coneJoin a b)).val = b :=
    le_antisymm (by simpa only [sup_idem, imageJoin] using h b)
      (e (coneJoin a b)).property
  have he : e (coneJoin a b) = e ⟨a, Set.mem_Ici.mpr le_rfl⟩ :=
    Subtype.ext (hv.trans (map_base_val e).symm)
  have hj : a ⊔ b = a := congrArg Subtype.val (e.injective he)
  exact hj ▸ (show b ≤ a ⊔ b from le_sup_right)

theorem target_le_source_of_inverse_borel_lift {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (h : InverseBorelLift e) : b ≤ a :=
  target_le_source_of_bounds e (imageJoin_le_of_inverse_borel_lift e h)

theorem bases_eq_of_inverse_borel_lifts {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (hinv : InverseBorelLift e) (hfwd : InverseBorelLift e.symm) : a = b :=
  le_antisymm (target_le_source_of_inverse_borel_lift e.symm hfwd)
    (target_le_source_of_inverse_borel_lift e hinv)

theorem imageJoin_eq_of_inverse_borel_lifts {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (hinv : InverseBorelLift e)
    (hfwd : InverseBorelLift e.symm) (x : Degree) : imageJoin e x = b ⊔ x := by
  apply le_antisymm (imageJoin_le_of_inverse_borel_lift e hinv x)
  have hsrc : e.symm (coneJoin b x) ≤ coneJoin a x :=
    imageJoin_le_of_inverse_borel_lift e.symm hfwd x
  have hmap : (e (e.symm (coneJoin b x))).val ≤ (e (coneJoin a x)).val :=
    e.monotone hsrc
  simpa only [e.apply_symm_apply, imageJoin, coneJoin] using hmap

theorem apply_val_eq_of_inverse_borel_lifts {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (hinv : InverseBorelLift e)
    (hfwd : InverseBorelLift e.symm) (x : Set.Ici a) : (e x).val = x.val := by
  have hab := bases_eq_of_inverse_borel_lifts e hinv hfwd
  have hx : coneJoin a x.val = x := Subtype.ext (sup_eq_right.mpr x.property)
  have h := imageJoin_eq_of_inverse_borel_lifts e hinv hfwd x.val
  change (e (coneJoin a x.val)).val = b ⊔ x.val at h
  rw [hx] at h
  have hbx : b ≤ x.val := (le_of_eq hab.symm).trans x.property
  exact h.trans (sup_eq_right.mpr hbx)

end OAI.TuringRigidity.TwoConeRigidity
