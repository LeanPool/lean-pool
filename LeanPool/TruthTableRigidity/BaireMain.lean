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

public import LeanPool.TruthTableRigidity.Decode

/-!
# Baire measurable functions induce only the trivial automorphism

Section 4 of the note: the coding lemma (Proposition 4.3) for Baire measurable functions,
and its consequences (Remark 4.5): if both `π` and `π⁻¹` are induced by Baire measurable
functions (in particular, by Borel functions), then `π` is the identity.
-/

@[expose] public section

open Filter Topology

namespace TT

open OAI.TuringRigidity

/-- An automorphism `π` of the tt-degrees is *induced by a Baire measurable function* if some
Baire measurable `F : 2^ω → 2^ω` induces it. -/
def InducedByBaireMeasurable (π : TTDegree ≃o TTDegree) : Prop :=
  ∃ F : Oracle → Oracle, BaireMeasurableFun F ∧ InducedBy π F

/-- **Proposition 4.3 (Coding lemma).** If a Baire measurable `F` induces an automorphism of
the tt-degrees, then there is a nonempty open `U ⊆ 2^ω × 2^ω` such that for every `X`,
`X ≤tt F(X) ⊕ F(G) ⊕ F(H)` for comeager many `(G, H) ∈ U`. -/
theorem coding_lemma {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : BaireMeasurableFun F) (hπ : InducedBy π F) :
    ∃ U : Set (Oracle × Oracle), IsOpen U ∧ U.Nonempty ∧ ∀ X : Oracle,
      ∀ᶠ p in residual (Oracle × Oracle), p ∈ U →
        TTReducible X (ojoin (F X) (ojoin (F p.1) (F p.2))) := by
  have hP := hπ.inducesProperties
  obtain ⟨D, hDG, hDd, hFD⟩ := hF.exists_continuousOn
  have hDres : D ∈ residual Oracle := mem_residual.mpr ⟨D, subset_rfl, hDG, hDd⟩
  obtain ⟨α, β, hlen, Φp, Φm, Φh, hp, hm, hh, hE⟩ := lemma_4_1 hDG hDd hFD hP.mono hP.join
  obtain ⟨j, b, i, σ, q₁, hασ, hq, hb0, hb1⟩ := lemma_4_2 hFD (hπ.nonconst_residual hDres α)
  refine ⟨Ncyl (σ ++ [i]) ×ˢ Ncyl β, (isOpen_Ncyl _).prod (isOpen_Ncyl _),
    ⟨(prep _ zzero, prep β zzero), prep_mem _ _, prep_mem _ _⟩, fun X => ?_⟩
  set l := σ.length with hl
  have hαl : α.length ≤ l := hασ.length_le
  let S : Set Z2 := Set.range (zseq l X) ∪ {zpow2 l}
  let C : AddSubgroup Z2 := AddSubgroup.closure S
  have hCcount : (C : Set Z2).Countable :=
    countable_addSubgroup_closure S ((Set.countable_range _).union (Set.countable_singleton _))
  let L : AddSubgroup Z2 :=
    { carrier := {T | LowZero l T}
      add_mem' := fun ha hb => Z2.lowZero_add ha hb
      zero_mem' := lowZero_zero l
      neg_mem' := fun ha => Z2.lowZero_neg ha }
  have hCL : C ≤ L := by
    rw [AddSubgroup.closure_le]
    rintro _ (⟨m, rfl⟩ | h)
    · exact lowZero_zseq l X m
    · rw [Set.mem_singleton_iff.mp h]; exact lowZero_zpow2 l
  have hCl : ∀ T ∈ C, LowZero l T := fun T hT => hCL hT
  have hY : zpow2 l ∈ C := AddSubgroup.subset_closure (Or.inr rfl)
  have hXm : ∀ m, zseq l X m ∈ C := fun m => AddSubgroup.subset_closure (Or.inl ⟨m, rfl⟩)
  -- the good pairs are comeager in `U`
  have hgood : ∀ᶠ p in residual (Oracle × Oracle), ∀ c₁ ∈ (C : Set Z2), ∀ c₂ ∈ (C : Set Z2),
      p ∈ Ncyl (σ ++ [i]) ×ˢ Ncyl β →
        Relations F Φp Φm Φh (Z2.of p.1 + c₁) (Z2.of p.2 + c₂) ∧ ((Z2.of p.1 +
          c₁ : Z2) : Oracle) ∈ D := by
    rw [eventually_countable_ball hCcount]
    intro c₁ hc₁
    rw [eventually_countable_ball hCcount]
    intro c₂ hc₂
    filter_upwards [translate_mem_residual c₁ c₂ hE] with p hp hpU
    have hασ' : α <+: σ ++ [i] := hασ.trans (List.prefix_append σ [i])
    have h1 : (Z2.of p.1 + c₁ : Z2) ∈ Ncyl α :=
      mem_Ncyl_add (Ncyl_antitone hασ' hpU.1) ((hCl c₁ hc₁).mono hαl)
    have h2 : (Z2.of p.2 + c₂ : Z2) ∈ Ncyl β :=
      mem_Ncyl_add hpU.2 (by rw [← hlen]; exact (hCl c₂ hc₂).mono hαl)
    exact hp h1 h2
  filter_upwards [hgood] with p hgp hpU
  have hdec := decode_of_good hp hm hh hq hb0 hb1 C hCl hY X hXm hpU.1
    (fun c₁ hc₁ c₂ hc₂ => hgp c₁ hc₁ c₂ hc₂ hpU)
  -- bounding the parameters
  set Q := ojoin X (ojoin p.1 p.2)
  set R := ojoin (F X) (ojoin (F p.1) (F p.2))
  have key : ∀ Φ, IsTTFunctional Φ → TTReducible (F (Φ Q)) R := fun Φ hΦ =>
    (hP.mono _ _ (ttReducible_of_isTTFunctional hΦ Q)).trans
      ((hP.join _ _).trans (ojoin_mono (TTReducible.refl _) (hP.join _ _)))
  have hG : IsTTFunctional fun Q : Oracle => evens (odds Q) :=
    isTTFunctional_evens.comp isTTFunctional_odds
  have hH : IsTTFunctional fun Q : Oracle => odds (odds Q) :=
    isTTFunctional_odds.comp isTTFunctional_odds
  have hYc : TTComputable (zpow2 l) := ttComputable_zpow2 l
  have k1 := key _ (hG.add ((isTTFunctional_prep (List.replicate l false)).comp
    isTTFunctional_evens))
  have k2 := key _ (hH.add (isTTFunctional_const (hYc.add hYc)))
  have k3 := key _ (hH.sub (isTTFunctional_const hYc))
  have k4 := key _ hH.neg
  have k5 := key _ (hG.add (hH.add hH))
  simp only [Q, Function.comp, evens_ojoin, odds_ojoin] at k1 k2 k3 k4 k5
  refine hdec.trans (ojoin_ttReducible ?_ (ojoin_ttReducible (ojoin_ttReducible ?_ ?_)
    (ojoin_ttReducible ?_ ?_)))
  · exact k1
  · exact k2
  · exact k3
  · exact k4
  · exact k5

/-- If a Baire measurable `F` induces `π`, then `π⁻¹(z) ≤ z` for every degree `z`. -/
theorem symm_le_of_baireMeasurable {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : BaireMeasurableFun F) (hπ : InducedBy π F) (a : TTDegree) : π.symm a ≤ a := by
  have hP := hπ.inducesProperties
  obtain ⟨U, hU, hne, hcode⟩ := coding_lemma hF hπ
  obtain ⟨Z, rfl⟩ := ttDegree_surjective a
  obtain ⟨A, hA⟩ := ttDegree_surjective (π.symm (ttDegree Z))
  rw [← hA, ttDegree_le_iff]
  refine remove_parameters hU hne ?_
  filter_upwards [hcode Z] with p hp hpU
  have h1 : TTReducible Z (F (ojoin Z (ojoin p.1 p.2))) := by
    refine (hp hpU).trans (ojoin_ttReducible (hP.mono _ _ (ttReducible_ojoin_left _ _)) ?_)
    refine ojoin_ttReducible ?_ ?_
    · exact hP.mono _ _ ((ttReducible_ojoin_left _ _).trans (ttReducible_ojoin_right _ _))
    · exact hP.mono _ _ ((ttReducible_ojoin_right _ _).trans (ttReducible_ojoin_right _ _))
  rw [← ttDegree_le_iff, hπ] at h1
  rw [← ttDegree_le_iff, hA]
  exact (OrderIso.symm_apply_le π).mpr h1

/-- **Coding consequence.** If a Baire measurable `F` induces an automorphism of the
tt-degrees, then `X ≤tt F(X)` for every `X`. -/
theorem ttReducible_self_of_baireMeasurable {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : BaireMeasurableFun F) (hπ : InducedBy π F) (X : Oracle) : TTReducible X (F X) := by
  have := symm_le_of_baireMeasurable hF hπ (ttDegree (F X))
  rwa [hπ, OrderIso.symm_apply_apply, ← hπ, ttDegree_le_iff] at this

/-- An automorphism induced by a Baire measurable function satisfies `z ≤ π(z)` for all `z`. -/
theorem le_apply_of_inducedByBaireMeasurable {π : TTDegree ≃o TTDegree}
    (h : InducedByBaireMeasurable π) (a : TTDegree) : a ≤ π a := by
  obtain ⟨F, hF, hπ⟩ := h
  have := symm_le_of_baireMeasurable hF hπ (π a)
  rwa [OrderIso.symm_apply_apply] at this

/-- **Remark 4.5.** If both `π` and `π⁻¹` are induced by Baire measurable functions, then `π`
is the identity. -/
theorem eq_refl_of_inducedByBaireMeasurable {π : TTDegree ≃o TTDegree}
    (h : InducedByBaireMeasurable π) (h' : InducedByBaireMeasurable π.symm) :
    π = OrderIso.refl TTDegree := by
  ext a
  refine le_antisymm ?_ (le_apply_of_inducedByBaireMeasurable h a)
  have h2 := π.monotone (le_apply_of_inducedByBaireMeasurable h' a)
  rwa [OrderIso.apply_symm_apply] at h2

/-- Under the hypotheses of Remark 4.5, a Baire measurable `F` inducing `π` satisfies
`F(X) ≡tt X` for all `X`. -/
theorem ttEquiv_of_inducedBy_baireMeasurable {π : TTDegree ≃o TTDegree} {F : Oracle → Oracle}
    (hF : BaireMeasurableFun F) (hπ : InducedBy π F) (h' : InducedByBaireMeasurable π.symm)
    (X : Oracle) : TTReducible (F X) X ∧ TTReducible X (F X) := by
  have := hπ X
  rw [eq_refl_of_inducedByBaireMeasurable ⟨F, hF, hπ⟩ h'] at this
  exact ttDegree_eq_iff.mp this

/-- **Borel case of Remark 4.5.** If `π` and `π⁻¹` are induced by Borel measurable functions,
then `π` is the identity. -/
theorem eq_refl_of_inducedByBorel_of_symm {π : TTDegree ≃o TTDegree} {F F' : Oracle → Oracle}
    (hF : Measurable F) (hπ : InducedBy π F) (hF' : Measurable F') (hπ' : InducedBy π.symm F') :
    π = OrderIso.refl TTDegree :=
  eq_refl_of_inducedByBaireMeasurable ⟨F, .of_measurable hF, hπ⟩ ⟨F', .of_measurable hF', hπ'⟩

end TT
