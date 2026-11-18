/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import LeanPool.TruthTableRigidity.Cantor

/-!
# Joins, the least tt-degree, and functions inducing automorphisms (Lemma 2.2)
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

theorem isTTFunctional_evens : IsTTFunctional evens := by
  refine isTTFunctional_of_use (u := fun n => 2 * n + 1) (t := fun n L => L.getD (2 * n) false)
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
    (getD_primrec.comp Primrec.snd (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)) ?_
  intro X n; rw [getD_pre X (by omega)]; rfl

theorem isTTFunctional_odds : IsTTFunctional odds := by
  refine isTTFunctional_of_use (u := fun n => 2 * n + 2) (t := fun n L => L.getD (2 * n + 1) false)
    (Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))
    (getD_primrec.comp Primrec.snd
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))) ?_
  intro X n; rw [getD_pre X (by omega)]; rfl

theorem ttReducible_ojoin_left (A B : Oracle) : TTReducible A (ojoin A B) :=
  ⟨evens, isTTFunctional_evens, evens_ojoin A B⟩

theorem ttReducible_ojoin_right (A B : Oracle) : TTReducible B (ojoin A B) :=
  ⟨odds, isTTFunctional_odds, odds_ojoin A B⟩

theorem ojoin_ttReducible {A B C : Oracle} (hA : TTReducible A C) (hB : TTReducible B C) :
    TTReducible (ojoin A B) C := by
  obtain ⟨Φ, hΦ, rfl⟩ := hA
  obtain ⟨Ψ, hΨ, rfl⟩ := hB
  exact ⟨fun X => ojoin (Φ X) (Ψ X), hΦ.join hΨ, rfl⟩

theorem ojoin_mono {A B A' B' : Oracle} (hA : TTReducible A A') (hB : TTReducible B B') :
    TTReducible (ojoin A B) (ojoin A' B') :=
  ojoin_ttReducible (hA.trans (ttReducible_ojoin_left _ _))
    (hB.trans (ttReducible_ojoin_right _ _))

theorem ttReducible_of_isTTFunctional {Φ : Oracle → Oracle} (hΦ : IsTTFunctional Φ) (X : Oracle) :
    TTReducible (Φ X) X := ⟨Φ, hΦ, rfl⟩

theorem prep_ttEquiv (τ : List Bool) (W : Oracle) :
    TTReducible (prep τ W) W ∧ TTReducible W (prep τ W) := by
  refine ⟨ttReducible_of_isTTFunctional (isTTFunctional_prep τ) W, ?_⟩
  have h := ttReducible_of_isTTFunctional (isTTFunctional_dropF τ.length) (prep τ W)
  have : dropF τ.length (prep τ W) = W := by
    funext n; simp [dropF, prep]
  rwa [this] at h

/-- No countable set contains all oracles. -/
theorem not_countable_univ_oracle : ¬ (Set.univ : Set Oracle).Countable := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_eq_range ⟨fun _ => false, trivial⟩
  have hD : (fun n => !(f n n)) ∈ Set.range f := hf ▸ trivial
  obtain ⟨m, hm⟩ := hD
  have := congrFun hm m
  cases h' : f m m <;> simp_all

/-- The consequences of inducing an automorphism used in the proof (Lemma 2.2 of the
paper, in the weak forms (M), (J'), (C), (N') used in Proposition 3.1). -/
structure InducesProperties (F : Oracle → Oracle) : Prop where
  mono : ∀ A B, TTReducible A B → TTReducible (F A) (F B)
  join : ∀ A B, TTReducible (F (ojoin A B)) (ojoin (F A) (F B))
  computable : ∀ A, TTComputable A → TTComputable (F A)
  nonconst : ∀ U : Set Oracle, IsOpen U → U.Nonempty → ∃ X ∈ U, ∃ Y ∈ U, F X ≠ F Y

theorem InducedBy.inducesProperties {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : InducedBy π F) : InducesProperties F := by
  have hmono : ∀ A B, TTReducible A B → TTReducible (F A) (F B) := by
    intro A B h
    rw [← ttDegree_le_iff, hF, hF]
    exact π.monotone (ttDegree_le_iff.mpr h)
  have hback : ∀ A B, TTReducible (F A) (F B) → TTReducible A B := by
    intro A B h
    rw [← ttDegree_le_iff, hF, hF] at h
    exact ttDegree_le_iff.mp (π.le_iff_le.mp h)
  refine ⟨hmono, ?_, ?_, ?_⟩
  · intro A B
    obtain ⟨D, hD⟩ := ttDegree_surjective (π.symm (ttDegree (ojoin (F A) (F B))))
    have hD' : ttDegree (F D) = ttDegree (ojoin (F A) (F B)) := by
      rw [hF, hD, OrderIso.apply_symm_apply]
    have hAD : TTReducible A D := by
      apply hback
      rw [← ttDegree_le_iff, hD']
      exact ttReducible_ojoin_left _ _
    have hBD : TTReducible B D := by
      apply hback
      rw [← ttDegree_le_iff, hD']
      exact ttReducible_ojoin_right _ _
    rw [← ttDegree_le_iff, ← hD', ttDegree_le_iff]
    exact hmono _ _ (ojoin_ttReducible hAD hBD)
  · intro A hA
    obtain ⟨Z, hZ⟩ := ttDegree_surjective (π.symm (ttDegree (fun _ => false)))
    have hZ' : ttDegree (F Z) = ttDegree (fun _ => false) := by
      rw [hF, hZ, OrderIso.apply_symm_apply]
    change TTReducible (F A) (fun _ => false)
    rw [← ttDegree_le_iff, ← hZ', ttDegree_le_iff]
    exact hmono _ _ (hA.ttReducible Z)
  · intro U hU hne
    by_contra hcon
    push Not at hcon
    obtain ⟨X₀, hX₀⟩ := hne
    obtain ⟨k, hk⟩ := exists_cyl_subset hU hX₀
    have hall : ∀ W, F (prep (pre X₀ k) W) = F X₀ := fun W =>
      hcon _ (hk (by rw [← Ncyl_pre]; exact prep_mem _ _)) _ hX₀
    have hdeg : ∀ W, ttDegree W = π.symm (ttDegree (F X₀)) := by
      intro W
      rw [← hall W, hF, OrderIso.symm_apply_apply, ttDegree_eq_iff]
      exact ⟨(prep_ttEquiv _ W).2, (prep_ttEquiv _ W).1⟩
    apply not_countable_univ_oracle
    refine (countable_ttReducible (fun _ => false)).mono fun W _ => ?_
    change TTReducible W (fun _ => false)
    rw [← ttDegree_le_iff, hdeg W, hdeg (fun _ => false)]

/-! ### Uniformization by Baire category (Lemma 2.3) -/

theorem uniformization {B : Type*} [TopologicalSpace B] [BaireSpace B] {U : Set B}
    (hU : IsOpen U) (hne : U.Nonempty) {φ ψ : B → Oracle} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : ∀ x ∈ U, TTReducible (φ x) (ψ x)) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧
      ∃ Φ, IsTTFunctional Φ ∧ ∀ x ∈ V, φ x = Φ (ψ x) := by
  let f : {Φ : Oracle → Oracle // IsTTFunctional Φ} → Set B :=
    fun Φ => {x | φ x = Φ.1 (ψ x)} ∪ Uᶜ
  have hclosed : ∀ Φ, IsClosed (f Φ) := fun Φ =>
    (isClosed_eq hφ (Φ.2.continuous.comp hψ)).union hU.isClosed_compl
  have hcover : ⋃ Φ, f Φ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨Φ, hΦ, hx'⟩ := h x hx
      exact Set.mem_iUnion.mpr ⟨⟨Φ, hΦ⟩, Or.inl hx'.symm⟩
    · obtain ⟨Φ, hΦ⟩ : ∃ Φ : Oracle → Oracle, IsTTFunctional Φ := ⟨id, isTTFunctional_id⟩
      exact Set.mem_iUnion.mpr ⟨⟨Φ, hΦ⟩, Or.inr hx⟩
  have hdense := dense_iUnion_interior_of_closed hclosed hcover
  obtain ⟨x, hxU, hx⟩ := hdense.inter_open_nonempty U hU hne
  obtain ⟨Φ, hxΦ⟩ := Set.mem_iUnion.mp hx
  refine ⟨U ∩ interior (f Φ), Set.inter_subset_left, hU.inter isOpen_interior, ⟨x, hxU, hxΦ⟩,
    Φ.1, Φ.2, fun y hy => ?_⟩
  rcases interior_subset hy.2 with hy' | hy'
  · exact hy'
  · exact absurd hy.1 hy'

end TT
