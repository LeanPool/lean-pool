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

open Filter Topology

namespace TT

open OAI.TuringRigidity

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

/-! ### Uniformization by Baire category (Lemma 2.4) -/

/-- A countable family of closed sets covering `E ∩ U` contains a member that covers a
nonempty open subset of `U` when `E` is dense `Gδ`. -/
theorem exists_open_subset_of_closed_cover {B ι : Type*} [TopologicalSpace B] [BaireSpace B]
    [Countable ι] {E U : Set B} (hEG : IsGδ E) (hEd : Dense E)
    (hU : IsOpen U) (hne : U.Nonempty) {K : ι → Set B} (hclosed : ∀ i, IsClosed (K i))
    (hcover : ∀ x ∈ E, x ∈ U → ∃ i, x ∈ K i) :
    ∃ i, ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ V ⊆ K i := by
  obtain ⟨x₀, hx₀U, hx₀E⟩ := hEd.inter_open_nonempty U hU hne
  obtain ⟨i₀, -⟩ := hcover x₀ hx₀E hx₀U
  let f : ι → Set B := fun i => K i ∪ Uᶜ
  have hcov : E ⊆ ⋃ i, f i := by
    intro x hxE
    by_cases hx : x ∈ U
    · obtain ⟨i, hi⟩ := hcover x hxE hx
      exact Set.mem_iUnion.mpr ⟨i, Or.inl hi⟩
    · exact Set.mem_iUnion.mpr ⟨i₀, Or.inr hx⟩
  have hdense := hEG.dense_iUnion_interior_of_closed hEd
    (fun i => (hclosed i).union hU.isClosed_compl) hcov
  obtain ⟨x, hxU, hx⟩ := hdense.inter_open_nonempty U hU hne
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  refine ⟨i, U ∩ interior (f i), Set.inter_subset_left, hU.inter isOpen_interior,
    ⟨x, hxU, hxi⟩, fun y hy => ?_⟩
  exact (interior_subset hy.2).resolve_right (fun h => h hy.1)

/-- An equation between functions continuous on `E` defines a relatively closed subset. -/
theorem eq_of_mem_closure {B : Type*} [TopologicalSpace B] {E : Set B} {f g : B → Oracle}
    (hf : ContinuousOn f E) (hg : ContinuousOn g E) (Q : B → Prop) {y : B} (hy : y ∈ E)
    (hcl : y ∈ closure {x | x ∈ E ∧ Q x ∧ f x = g x}) : f y = g y := by
  by_contra hne
  have hc : ContinuousWithinAt (fun z => (f z, g z)) E y := (hf y hy).prodMk (hg y hy)
  have hopen : IsOpen {p : Oracle × Oracle | p.1 ≠ p.2} := isClosed_diagonal.isOpen_compl
  have hev : ∀ᶠ z in 𝓝[E] y, f z ≠ g z :=
    hc.eventually (hopen.mem_nhds (show (f y, g y).1 ≠ (f y, g y).2 from hne))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨z, hz1, hz2⟩ := (mem_closure_iff_frequently.mp hcl).and_eventually hev |>.exists
  exact hz2 hz1.1 hz1.2.2

/-- **Lemma 2.4, relative version.** Let `E` be a dense `Gδ` subset of a Baire space and let
`φ, ψ` be continuous on `E` with `φ x ≤tt ψ x` for `x ∈ E ∩ U`.  Then a single tt-functional
witnesses this on `E ∩ V` for some nonempty open `V ⊆ U`. -/
theorem uniformization_on {B : Type*} [TopologicalSpace B] [BaireSpace B] {E U : Set B}
    (hEG : IsGδ E) (hEd : Dense E) (hU : IsOpen U) (hne : U.Nonempty) {φ ψ : B → Oracle}
    (hφ : ContinuousOn φ E) (hψ : ContinuousOn ψ E)
    (h : ∀ x ∈ E, x ∈ U → TTReducible (φ x) (ψ x)) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧
      ∃ Φ, IsTTFunctional Φ ∧ ∀ x ∈ E, x ∈ V → φ x = Φ (ψ x) := by
  let S : {Φ : Oracle → Oracle // IsTTFunctional Φ} → Set B :=
    fun Φ => {x | x ∈ E ∧ x ∈ U ∧ φ x = Φ.1 (ψ x)}
  have hcover : ∀ x ∈ E, x ∈ U → ∃ Φ, x ∈ closure (S Φ) := by
    intro x hxE hx
    obtain ⟨Φ, hΦ, hx'⟩ := h x hxE hx
    exact ⟨⟨Φ, hΦ⟩, subset_closure ⟨hxE, hx, hx'.symm⟩⟩
  obtain ⟨Φ, V, hVU, hV, hVne, hVsub⟩ :=
    exists_open_subset_of_closed_cover hEG hEd hU hne (fun _ => isClosed_closure) hcover
  have hc : ContinuousOn (fun z => Φ.1 (ψ z)) E := Φ.2.continuous.comp_continuousOn hψ
  exact ⟨V, hVU, hV, hVne, Φ.1, Φ.2, fun y hyE hy =>
    eq_of_mem_closure hφ hc (· ∈ U) hyE (hVsub hy)⟩

theorem uniformization {B : Type*} [TopologicalSpace B] [BaireSpace B] {U : Set B}
    (hU : IsOpen U) (hne : U.Nonempty) {φ ψ : B → Oracle} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : ∀ x ∈ U, TTReducible (φ x) (ψ x)) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧
      ∃ Φ, IsTTFunctional Φ ∧ ∀ x ∈ V, φ x = Φ (ψ x) := by
  obtain ⟨V, hVU, hV, hVne, Φ, hΦ, hEq⟩ := uniformization_on IsGδ.univ dense_univ hU hne
    hφ.continuousOn hψ.continuousOn (fun x _ hx => h x hx)
  exact ⟨V, hVU, hV, hVne, Φ, hΦ, fun x hx => hEq x (Set.mem_univ _) hx⟩

/-- The three tt-functionals in a witness for an inverse image of a truth-table degree. -/
abbrev InverseWitness :=
  let Functional := {Φ : Oracle → Oracle // IsTTFunctional Φ}
  Functional × Functional × Functional

/-- Both truth-table reductions identifying the image of the chosen preimage. -/
def InverseWitness.valid (w : InverseWitness) (F : Oracle → Oracle) (Z : Oracle) : Prop :=
  w.2.1.1 (F (w.1.1 Z)) = Z ∧ w.2.2.1 Z = F (w.1.1 Z)

theorem InverseWitness.degree_eq {w : InverseWitness} {F : Oracle → Oracle}
    {Z : Oracle} (h : w.valid F Z) : ttDegree (F (w.1.1 Z)) = ttDegree Z :=
  ttDegree_eq_iff.mpr ⟨⟨w.2.2.1, w.2.2.2, h.2⟩, ⟨w.2.1.1, w.2.1.2, h.1⟩⟩

/-- Given `X ≤tt F(X)`, every `Z` has a preimage up to truth-table equivalence of the
form `Φ Z`, together with functional witnesses for both reductions. -/
theorem InducedBy.exists_inverse_witness {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hπ : InducedBy π F) (hle : ∀ X, TTReducible X (F X)) (Z : Oracle) :
    ∃ w : InverseWitness, w.valid F Z := by
  obtain ⟨X, hX⟩ := ttDegree_surjective (π.symm (ttDegree Z))
  have hFX : ttDegree (F X) = ttDegree Z := by rw [hπ, hX, OrderIso.apply_symm_apply]
  obtain ⟨h1, h2⟩ := ttDegree_eq_iff.mp hFX
  obtain ⟨Φ, hΦ, hΦZ⟩ := (hle X).trans h1
  obtain ⟨Λ, hΛ, hΛZ⟩ := h2
  obtain ⟨Λ', hΛ', hΛ'Z⟩ := h1
  refine ⟨(⟨Φ, hΦ⟩, ⟨Λ, hΛ⟩, ⟨Λ', hΛ'⟩), ?_, ?_⟩
  · change Λ (F (Φ Z)) = Z
    rw [hΦZ, hΛZ]
  · change Λ' Z = F (Φ Z)
    rw [hΦZ, hΛ'Z]

end TT
