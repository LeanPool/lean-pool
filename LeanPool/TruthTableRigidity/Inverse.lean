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

public import LeanPool.TruthTableRigidity.BaireMain

/-!
# The inverse automorphism (Proposition 4.8) and Theorem 1.1 in full generality

Section 4.6 of the note.  Under hypothesis (7) — `π` an automorphism of the tt-degrees,
`D ⊆ 2^ω` a dense `Gδ` set and `F` continuous on `D` inducing `π` on `D` — there are a
tt-functional `Ψ` and a dense `Gδ` set `D'` such that `Ψ` induces `π⁻¹` on `D'`
(Proposition 4.8).  In fact we obtain `D' = 2^ω`.

Consequently (Theorem 1.1) an automorphism induced on a comeager set by a continuous function
is the identity, and (Corollary 1.2) so is an automorphism induced by a Baire measurable
function.

The proof differs from the note in how the Baire property of the sets `B_Φ` is avoided.
We work on the space of pairs `(G, Z)` and consider the dense `Gδ` set `E` of pairs with
`G ∈ D` and `G + Φ(Z) ∈ D` for every tt-functional `Φ`.  For a pair in `E`, if
`deg(Φ Z) = π⁻¹(deg Z)` then `F(G) ⊕ F(G + Φ Z) ≡tt Z ⊕ F(G)`.  By Baire category
(on the relatively closed sets where fixed tt-functionals witness this equivalence) one triple
of tt-functionals works on `E ∩ (N_γ × N_σ)`.  For every `Z ∈ N_σ` and comeager many
`G ∈ N_γ` this gives `Φ(Z) ⊕ G ≡tt B ⊕ G` with `deg B = π⁻¹(deg Z)`, and removing the
parameter `G` (Lemma 4.4) gives `deg(Φ Z) = π⁻¹(deg Z)` for **every** `Z ∈ N_σ`.
-/

@[expose] public section

open Filter Topology

namespace TT

open OAI.TuringRigidity

/-! ### Two 2-adic reductions -/

theorem red_zaddO_ojoin (G Y : Oracle) : TTReducible (zaddO G Y) (ojoin Y G) := by
  refine ⟨_, isTTFunctional_odds.add isTTFunctional_evens, ?_⟩
  simp only [evens_ojoin, odds_ojoin]
  rfl

theorem red_of_zaddO (G Y : Oracle) : TTReducible Y (ojoin G (zaddO G Y)) := by
  refine ⟨_, isTTFunctional_odds.sub isTTFunctional_evens, ?_⟩
  simp only [evens_ojoin, odds_ojoin]
  exact add_sub_cancel_left (Z2.of G) (Z2.of Y)

/-! ### Baire category with a countable family of relatively closed sets -/

/-- If a dense `Gδ` subset `E` of a Baire space is covered by countably many sets which are
relatively closed in `E`, then one of them contains `E ∩ V` for a nonempty open `V`. -/
theorem exists_open_of_cover {B ι : Type*} [TopologicalSpace B] [BaireSpace B] [Nonempty B]
    [Countable ι] {E : Set B} (hEG : IsGδ E) (hEd : Dense E) (P : ι → B → Prop)
    (hP : ∀ i, ∀ y ∈ E, y ∈ closure {x | x ∈ E ∧ P i x} → P i y)
    (hcov : ∀ x ∈ E, ∃ i, P i x) :
    ∃ i, ∃ V : Set B, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ E, x ∈ V → P i x := by
  let f : ι → Set B := fun i => closure {x | x ∈ E ∧ P i x}
  have hcover : ∀ x ∈ E, x ∈ Set.univ → ∃ i, x ∈ f i := by
    intro x hx _
    obtain ⟨i, hi⟩ := hcov x hx
    exact ⟨i, subset_closure ⟨hx, hi⟩⟩
  obtain ⟨i, V, -, hV, hVne, hVf⟩ := exists_open_subset_of_closed_cover hEG hEd
    isOpen_univ Set.univ_nonempty (fun _ => isClosed_closure) hcover
  exact ⟨i, V, hV, hVne, fun y hyE hy => hP i y hyE (hVf hy)⟩

/-! ### Removing one parameter -/

/-- **Lemma 4.4, one parameter.** If `A ≤tt X ⊕ G` for comeager many `G ∈ N_γ`, then
`A ≤tt X`. -/
theorem remove_parameter {γ : List Bool} {A X : Oracle}
    (h : ∀ᶠ G in residual Oracle, G ∈ Ncyl γ → TTReducible A (ojoin X G)) :
    TTReducible A X := by
  refine remove_parameters (U := Ncyl γ ×ˢ Set.univ) ((isOpen_Ncyl γ).prod isOpen_univ)
    ⟨(prep γ zzero, zzero), prep_mem γ zzero, trivial⟩ ?_
  filter_upwards [preimage_mem_residual continuous_fst isOpenMap_fst h] with p hp hpU
  exact (hp hpU.1).trans (ojoin_mono (TTReducible.refl X) (ttReducible_ojoin_left _ _))

/-! ### The main step -/

/-- The set of pairs `(G, Z)` with `G ∈ D` and `G + Φ Z ∈ D` for all tt-functionals `Φ`. -/
def goodPairs (D : Set Oracle) : Set (Oracle × Oracle) :=
  {p | p.1 ∈ D ∧ ∀ Φ : {Φ : Oracle → Oracle // IsTTFunctional Φ}, zaddO p.1 (Φ.1 p.2) ∈ D}

theorem goodPairs_eq (D : Set Oracle) : goodPairs D = Prod.fst ⁻¹' D ∩
    ⋂ Φ : {Φ : Oracle → Oracle // IsTTFunctional Φ},
      (fun p : Oracle × Oracle => zaddO p.1 (Φ.1 p.2)) ⁻¹' D := by
  ext p
  simp [goodPairs]

theorem continuous_zaddO_comp (Φ : {Φ : Oracle → Oracle // IsTTFunctional Φ}) :
    Continuous fun p : Oracle × Oracle => zaddO p.1 (Φ.1 p.2) :=
  continuous_zaddO.comp (continuous_fst.prodMk (Φ.2.continuous.comp continuous_snd))

theorem isGδ_goodPairs {D : Set Oracle} (hD : IsGδ D) : IsGδ (goodPairs D) := by
  rw [goodPairs_eq]
  exact (hD.preimage continuous_fst).inter
    (IsGδ.iInter fun Φ => hD.preimage (continuous_zaddO_comp Φ))

theorem goodPairs_mem_residual {D : Set Oracle} (hD : D ∈ residual Oracle) :
    goodPairs D ∈ residual (Oracle × Oracle) := by
  rw [goodPairs_eq]
  refine Filter.inter_mem (preimage_mem_residual continuous_fst isOpenMap_fst hD)
    (countable_iInter_mem.mpr fun Φ => ?_)
  exact preimage_mem_residual (continuous_zaddO_comp Φ)
    (isOpenMap_shear_fst Φ.1 Φ.2.continuous) hD

theorem goodPairs_section_mem_residual {D : Set Oracle} (hD : D ∈ residual Oracle)
    (Z : Oracle) : {G | (G, Z) ∈ goodPairs D} ∈ residual Oracle := by
  have : {G | (G, Z) ∈ goodPairs D} = D ∩
      ⋂ Φ : {Φ : Oracle → Oracle // IsTTFunctional Φ}, (translHomeo (Φ.1 Z)) ⁻¹' D := by
    ext G
    simp [goodPairs, translHomeo]
  rw [this]
  exact Filter.inter_mem hD (countable_iInter_mem.mpr fun Φ =>
    preimage_mem_residual (translHomeo _).continuous (translHomeo _).isOpenMap hD)

/-- **Proposition 4.8, strong form, for a Baire measurable function.**  If a Baire measurable
`F` induces `π`, then some tt-functional `Ψ` induces `π⁻¹` on all of `2^ω`. -/
theorem exists_ttFunctional_inducedBy_symm {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : BaireMeasurableFun F) (hπ : InducedBy π F) :
    ∃ Ψ : Oracle → Oracle, IsTTFunctional Ψ ∧ InducedBy π.symm Ψ := by
  have hP := hπ.inducesProperties
  have hback : ∀ A B, TTReducible (F A) (F B) → TTReducible A B := by
    intro A B h
    rw [← ttDegree_le_iff, hπ, hπ] at h
    exact ttDegree_le_iff.mp (π.le_iff_le.mp h)
  -- `F(A) ⊕ F(B) ≤tt F(A ⊕ B)`
  have hjoin' : ∀ A B, TTReducible (ojoin (F A) (F B)) (F (ojoin A B)) := fun A B =>
    ojoin_ttReducible (hP.mono _ _ (ttReducible_ojoin_left _ _))
      (hP.mono _ _ (ttReducible_ojoin_right _ _))
  -- representatives of `π⁻¹(deg Z)`
  have hrep : ∀ Z, ∃ A, ttDegree A = π.symm (ttDegree Z) ∧ TTReducible (F A) Z ∧
      TTReducible Z (F A) := by
    intro Z
    obtain ⟨A, hA⟩ := ttDegree_surjective (π.symm (ttDegree Z))
    have hFA : ttDegree (F A) = ttDegree Z := by rw [hπ, hA, OrderIso.apply_symm_apply]
    exact ⟨A, hA, (ttDegree_eq_iff.mp hFA).1, (ttDegree_eq_iff.mp hFA).2⟩
  obtain ⟨D₀, hDG, hDd, hFD⟩ := hF.exists_continuousOn
  have hDres : D₀ ∈ residual Oracle := mem_residual.mpr ⟨D₀, subset_rfl, hDG, hDd⟩
  set E := goodPairs D₀ with hE
  have hEG : IsGδ E := isGδ_goodPairs hDG
  have hEd : Dense E := dense_of_mem_residual (goodPairs_mem_residual hDres)
  let ι := {Φ : Oracle → Oracle // IsTTFunctional Φ}
  -- the relations `F(G) ⊕ F(G + Φ Z) ≡tt Z ⊕ F(G)`, witnessed by fixed tt-functionals
  let K : ι → Oracle × Oracle → Oracle := fun Φ p => ojoin (F p.1) (F (zaddO p.1 (Φ.1 p.2)))
  let L : Oracle × Oracle → Oracle := fun p => ojoin p.2 (F p.1)
  let P : ι × ι × ι → Oracle × Oracle → Prop := fun i p =>
    i.2.1.1 (K i.1 p) = L p ∧ i.2.2.1 (L p) = K i.1 p
  have c1 : ContinuousOn (fun p : Oracle × Oracle => F p.1) E :=
    hFD.comp continuous_fst.continuousOn fun p hp => hp.1
  have hK : ∀ Φ, ContinuousOn (K Φ) E := fun Φ =>
    continuous_ojoin.comp_continuousOn (c1.prodMk
      (hFD.comp (continuous_zaddO_comp Φ).continuousOn fun p hp => hp.2 Φ))
  have hL : ContinuousOn L E :=
    continuous_ojoin.comp_continuousOn (continuous_snd.continuousOn.prodMk c1)
  have hPcl : ∀ i, ∀ y ∈ E, y ∈ closure {x | x ∈ E ∧ P i x} → P i y := by
    intro i y hy hcl
    refine ⟨eq_of_mem_closure (i.2.1.2.continuous.comp_continuousOn (hK i.1)) hL
      (fun x => i.2.2.1 (L x) = K i.1 x) hy (closure_mono (fun x hx => ?_) hcl),
      eq_of_mem_closure (i.2.2.2.continuous.comp_continuousOn hL) (hK i.1)
      (fun x => i.2.1.1 (K i.1 x) = L x) hy (closure_mono (fun x hx => ?_) hcl)⟩
    · exact ⟨hx.1, hx.2.2, hx.2.1⟩
    · exact ⟨hx.1, hx.2.1, hx.2.2⟩
  have hcov : ∀ p ∈ E, ∃ i, P i p := by
    rintro ⟨G, Z⟩ -
    obtain ⟨A, hA, hAZ, hZA⟩ := hrep Z
    obtain ⟨Φ, hΦ, hΦZ⟩ : TTReducible A Z := by
      rw [← ttDegree_le_iff, hA]
      exact symm_le_of_baireMeasurable hF hπ _
    subst hΦZ
    have r1 : TTReducible (ojoin Z (F G)) (ojoin (F G) (F (zaddO G (Φ Z)))) :=
      ojoin_ttReducible ((hZA.trans (hP.mono _ _ (red_of_zaddO G (Φ Z)))).trans (hP.join _ _))
        (ttReducible_ojoin_left _ _)
    have r2 : TTReducible (ojoin (F G) (F (zaddO G (Φ Z)))) (ojoin Z (F G)) :=
      ojoin_ttReducible (ttReducible_ojoin_right _ _)
        (((hP.mono _ _ (red_zaddO_ojoin G (Φ Z))).trans (hP.join _ _)).trans
          (ojoin_mono hAZ (TTReducible.refl _)))
    obtain ⟨Λ₁, hΛ₁, h1⟩ := r1
    obtain ⟨Λ₂, hΛ₂, h2⟩ := r2
    exact ⟨(⟨Φ, hΦ⟩, ⟨Λ₁, hΛ₁⟩, ⟨Λ₂, hΛ₂⟩), h1, h2⟩
  obtain ⟨i, V, hV, hVne, hVP⟩ := exists_open_of_cover hEG hEd P hPcl hcov
  obtain ⟨γ, σ, hγσ⟩ := exists_box_subset hV hVne
  set Φ := i.1 with hΦ
  have hmain : ∀ Z ∈ Ncyl σ, ttDegree (Φ.1 Z) = π.symm (ttDegree Z) := by
    intro Z hZ
    obtain ⟨A, hA, hAZ, hZA⟩ := hrep Z
    have hgood : ∀ᶠ G in residual Oracle, G ∈ Ncyl γ → P i (G, Z) := by
      filter_upwards [goodPairs_section_mem_residual hDres Z] with G hG hGγ
      exact hVP _ hG (hγσ ⟨hGγ, hZ⟩)
    have e1 : TTReducible A (Φ.1 Z) := by
      refine remove_parameter (γ := γ) ?_
      filter_upwards [hgood] with G hG hGγ
      obtain ⟨h1, -⟩ := hG hGγ
      apply hback
      refine (hAZ.trans (ttReducible_ojoin_left Z (F G))).trans ?_
      refine TTReducible.trans ⟨i.2.1.1, i.2.1.2, h1⟩ ?_
      refine (hjoin' _ _).trans (hP.mono _ _ ?_)
      exact ojoin_ttReducible (ttReducible_ojoin_right _ _) (red_zaddO_ojoin G (Φ.1 Z))
    have e2 : TTReducible (Φ.1 Z) A := by
      refine remove_parameter (γ := γ) ?_
      filter_upwards [hgood] with G hG hGγ
      obtain ⟨-, h2⟩ := hG hGγ
      apply hback
      refine ((hP.mono _ _ (red_of_zaddO G (Φ.1 Z))).trans (hP.join _ _)).trans ?_
      refine TTReducible.trans ⟨i.2.2.1, i.2.2.2, h2⟩ ?_
      exact (ojoin_mono hZA (TTReducible.refl _)).trans (hjoin' _ _)
    rw [← hA]
    exact ttDegree_eq_iff.mpr ⟨e2, e1⟩
  refine ⟨fun Z => Φ.1 (prep σ Z), Φ.2.comp (isTTFunctional_prep σ), fun Z => ?_⟩
  rw [hmain _ (prep_mem σ Z)]
  congr 1
  exact ttDegree_eq_iff.mpr (prep_ttEquiv σ Z)

/-! ### From hypothesis (7) to a Baire measurable function inducing `π` -/

/-- If `F` is continuous on a comeager set `D` and induces `π` on `D`, then some Baire
measurable function agrees with `F` on `D` and induces `π` everywhere. -/
theorem exists_baireMeasurable_extension {π : TTDegree ≃o TTDegree} {D : Set Oracle}
    (hD : D ∈ residual Oracle) {F : Oracle → Oracle} (hFD : ContinuousOn F D)
    (hπ : ∀ X ∈ D, ttDegree (F X) = π (ttDegree X)) :
    ∃ F' : Oracle → Oracle, BaireMeasurableFun F' ∧ InducedBy π F' ∧ Set.EqOn F' F D := by
  classical
  choose R hR using fun X => ttDegree_surjective (π (ttDegree X))
  refine ⟨fun X => if X ∈ D then F X else R X, fun U hU => ?_, fun X => ?_, fun X hX => ?_⟩
  · obtain ⟨O, hO, hOD⟩ := continuousOn_iff'.mp hFD U hU
    refine hO.baireMeasurableSet.congr ?_
    filter_upwards [hD] with X hX
    have h := congrArg (fun s : Set Oracle => X ∈ s) hOD
    simp only [Set.mem_inter_iff, Set.mem_preimage, hX, and_true, eq_iff_iff] at h
    simp only [Set.mem_preimage, hX, ↓reduceIte]
    exact h.symm
  · by_cases hX : X ∈ D
    · simp only [hX, ↓reduceIte]; exact hπ X hX
    · simp only [hX, ↓reduceIte]; exact hR X
  · simp only [hX, ↓reduceIte]

/-- **Proposition 4.8, strong form.** Under hypothesis (7) some tt-functional induces `π⁻¹` on
all of `2^ω`. -/
theorem prop_4_8_everywhere {π : TTDegree ≃o TTDegree} {D : Set Oracle} (hDG : IsGδ D)
    (hDd : Dense D) {F : Oracle → Oracle} (hFD : ContinuousOn F D)
    (hπ : ∀ X ∈ D, ttDegree (F X) = π (ttDegree X)) :
    ∃ Ψ : Oracle → Oracle, IsTTFunctional Ψ ∧ InducedBy π.symm Ψ := by
  obtain ⟨F', hF', hπ', -⟩ := exists_baireMeasurable_extension
    (mem_residual.mpr ⟨D, subset_rfl, hDG, hDd⟩) hFD hπ
  exact exists_ttFunctional_inducedBy_symm hF' hπ'

/-- **Proposition 4.8.** Assume (7): `π` is an automorphism of the tt-degrees, `D` is a dense
`Gδ` set and `F` is continuous on `D` and induces `π` on `D`.  Then there are a tt-functional
`Ψ` and a dense `Gδ` set `D'` such that `Ψ` induces `π⁻¹` on `D'`. -/
theorem prop_4_8 {π : TTDegree ≃o TTDegree} {D : Set Oracle} (hDG : IsGδ D) (hDd : Dense D)
    {F : Oracle → Oracle} (hFD : ContinuousOn F D)
    (hπ : ∀ X ∈ D, ttDegree (F X) = π (ttDegree X)) :
    ∃ Ψ : Oracle → Oracle, IsTTFunctional Ψ ∧ ∃ D' : Set Oracle, IsGδ D' ∧ Dense D' ∧
      ∀ Z ∈ D', ttDegree (Ψ Z) = π.symm (ttDegree Z) := by
  obtain ⟨Ψ, hΨ, hΨπ⟩ := prop_4_8_everywhere hDG hDd hFD hπ
  exact ⟨Ψ, hΨ, Set.univ, isOpen_univ.isGδ, dense_univ, fun Z _ => hΨπ Z⟩

/-- **Corollary 1.2.** An automorphism of the tt-degrees induced by a Baire measurable
function is the identity. -/
theorem eq_refl_of_inducedByBaireMeasurable' {π : TTDegree ≃o TTDegree}
    (h : InducedByBaireMeasurable π) : π = OrderIso.refl TTDegree := by
  obtain ⟨F, hF, hπ⟩ := h
  obtain ⟨Ψ, hΨ, hΨπ⟩ := exists_ttFunctional_inducedBy_symm hF hπ
  exact eq_refl_of_inducedByBaireMeasurable ⟨F, hF, hπ⟩
    ⟨Ψ, .of_continuous hΨ.continuous, hΨπ⟩

/-- **Theorem 1.1.** If an automorphism `π` of the tt-degrees is induced on a comeager set `D`
by a function `F` continuous on `D`, then `π` is the identity. -/
theorem eq_refl_of_inducedOn_comeager {π : TTDegree ≃o TTDegree} {D : Set Oracle}
    (hD : D ∈ residual Oracle) {F : Oracle → Oracle} (hFD : ContinuousOn F D)
    (hπ : ∀ X ∈ D, ttDegree (F X) = π (ttDegree X)) :
    π = OrderIso.refl TTDegree := by
  obtain ⟨F', hF', hπ', -⟩ := exists_baireMeasurable_extension hD hFD hπ
  exact eq_refl_of_inducedByBaireMeasurable' ⟨F', hF', hπ'⟩

end TT
