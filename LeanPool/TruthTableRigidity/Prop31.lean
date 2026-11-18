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

public import LeanPool.TruthTableRigidity.Degrees
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import LeanPool.TruthTableRigidity.ShiftStep

/-!
# Proposition 3.1

A continuous `F` with properties (M), (J′), (C), (N′) has, below every string `ρ`, a string
`τ ⊇ ρ` and a tt-functional `Γ` with `Γ (F (τ⌢X)) = X`.  In particular `X ≤tt F X`.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-! ### Continuity of the group operations -/

/-- 2-adic addition, as a map of oracles. -/
def zaddO (G H : Oracle) : Oracle := (Z2.of G + Z2.of H : Z2)

/-- 2-adic negation, as a map of oracles. -/
def znegO (G : Oracle) : Oracle := (-Z2.of G : Z2)

theorem continuous_ojoin : Continuous fun p : Oracle × Oracle => ojoin p.1 p.2 := by
  apply continuous_pi
  intro n
  by_cases h : n % 2 = 0
  · simp only [ojoin, h, ite_true]
    exact (continuous_apply _).comp continuous_fst
  · simp only [ojoin, h, ite_false]
    exact (continuous_apply _).comp continuous_snd

theorem continuous_zaddO : Continuous fun p : Oracle × Oracle => zaddO p.1 p.2 :=
  (isTTFunctional_addHalves.continuous.comp continuous_ojoin).congr fun p => by
    simp [Function.comp, zaddO]

theorem continuous_znegO : Continuous znegO := isTTFunctional_neg.continuous

/-! ### The reductions (2) -/

theorem red_plus (G H : Z2) : TTReducible (G + H : Z2) (ojoin G H) := by
  change TTReducible (Z2.of G + Z2.of H : Z2) (ojoin G H)
  simpa only [evens_ojoin, odds_ojoin] using
    ttReducible_of_isTTFunctional isTTFunctional_addHalves (ojoin G H)

theorem red_minus (G H : Z2) : TTReducible G (ojoin (G + H : Z2) (-H : Z2)) := by
  have := ttReducible_of_isTTFunctional isTTFunctional_addHalves (ojoin (G + H : Z2) (-H : Z2))
  simp only [evens_ojoin, odds_ojoin] at this
  have e : (Z2.of (G + H) + Z2.of (-H) : Z2) = G := by
    change (G + H) + -H = G; abel
  rwa [e] at this

theorem shift_cons (b : Bool) (X : Oracle) : shift (cons b X) = X := by
  funext n; simp [shift, cons]

theorem red_half (G H : Z2) : TTReducible (G + H : Z2) (ojoin G (G + (H + H) : Z2)) := by
  have := ttReducible_of_isTTFunctional (isTTFunctional_shift.comp isTTFunctional_addHalves)
    (ojoin G (G + (H + H) : Z2))
  simp only [Function.comp, evens_ojoin, odds_ojoin] at this
  have e : shift (Z2.of G + Z2.of (G + (H + H)) : Z2) = (G + H : Z2) := by
    have : (Z2.of G + Z2.of (G + (H + H)) : Z2) = (G + H) + (G + H) := by
      change G + (G + (H + H)) = (G + H) + (G + H); abel
    rw [this, Z2.add_self, shift_cons]
  rwa [e] at this

/-! ### Step 1: uniform relations on a box -/

theorem step_relations {F : Oracle → Oracle} (hF : Continuous F) (hP : InducesProperties F)
    (ρ : List Bool) :
    ∃ α β : List Bool, ρ <+: α ∧ α.length = β.length ∧
      ∃ Φp Φm Φh : Oracle → Oracle, IsTTFunctional Φp ∧ IsTTFunctional Φm ∧
        IsTTFunctional Φh ∧ ∀ G H : Z2, G ∈ Ncyl α → H ∈ Ncyl β → Relations F Φp Φm Φh G H := by
  let U₀ : Set (Oracle × Oracle) := Ncyl ρ ×ˢ Ncyl ρ
  have hU₀ : IsOpen U₀ := (isOpen_Ncyl ρ).prod (isOpen_Ncyl ρ)
  have hU₀ne : U₀.Nonempty := ⟨(prep ρ zzero, prep ρ zzero), prep_mem _ _, prep_mem _ _⟩
  have cF1 : Continuous fun p : Oracle × Oracle => F p.1 := hF.comp' continuous_fst
  have cF2 : Continuous fun p : Oracle × Oracle => F p.2 := hF.comp' continuous_snd
  have cAdd : Continuous fun p : Oracle × Oracle => F (zaddO p.1 p.2) :=
    hF.comp' continuous_zaddO
  have cNeg : Continuous fun p : Oracle × Oracle => F (znegO p.2) :=
    hF.comp' (continuous_znegO.comp' continuous_snd)
  have cDouble : Continuous fun p : Oracle × Oracle => zaddO p.2 p.2 :=
    continuous_zaddO.comp₂ continuous_snd continuous_snd
  have cDbl : Continuous fun p : Oracle × Oracle => F (zaddO p.1 (zaddO p.2 p.2)) :=
    hF.comp' (continuous_zaddO.comp₂ continuous_fst cDouble)
  -- (R+)
  obtain ⟨V₁, hV₁U, hV₁, hV₁ne, Φp, hp, hRp⟩ := uniformization hU₀ hU₀ne cAdd
    (continuous_ojoin.comp₂ cF1 cF2) (fun p _ =>
      (hP.mono _ _ (red_plus p.1 p.2)).trans (hP.join _ _))
  -- (R−)
  obtain ⟨V₂, hV₂V, hV₂, hV₂ne, Φm, hm, hRm⟩ := uniformization hV₁ hV₁ne cF1
    (continuous_ojoin.comp₂ cAdd cNeg) (fun p _ =>
      (hP.mono _ _ (red_minus p.1 p.2)).trans (hP.join _ _))
  -- (R1/2)
  obtain ⟨V₃, hV₃V, hV₃, hV₃ne, Φh, hh, hRh⟩ := uniformization hV₂ hV₂ne cAdd
    (continuous_ojoin.comp₂ cF1 cDbl) (fun p _ =>
      (hP.mono _ _ (red_half p.1 p.2)).trans (hP.join _ _))
  obtain ⟨⟨x, y⟩, hxy⟩ := hV₃ne
  obtain ⟨k₀, hk₀⟩ := exists_cyl_prod_subset hV₃ hxy
  set k := max k₀ ρ.length
  have hbox : Ncyl (pre x k) ×ˢ Ncyl (pre y k) ⊆ V₃ := by
    rw [Ncyl_pre, Ncyl_pre]
    exact fun p hp => hk₀ ⟨cyl_antitone x (le_max_left _ _) hp.1,
      cyl_antitone y (le_max_left _ _) hp.2⟩
  have hxρ : x ∈ Ncyl ρ := (hV₁U (hV₂V (hV₃V hxy))).1
  refine ⟨pre x k, pre y k, ?_, by simp [length_pre], Φp, Φm, Φh, hp, hm, hh, ?_⟩
  · have : pre x ρ.length = ρ := hxρ
    rw [← this]
    exact pre_prefix x (le_max_right _ _)
  · intro G H hG hH
    let point : Oracle × Oracle := (G, H)
    have h3 : point ∈ V₃ := hbox ⟨hG, hH⟩
    have h2 : point ∈ V₂ := hV₃V h3
    have h1 : point ∈ V₁ := hV₂V h2
    change F (zaddO G H) = Φp (ojoin (F G) (F H)) ∧
      F G = Φm (ojoin (F (zaddO G H)) (F (znegO H))) ∧
      F (zaddO G H) = Φh (ojoin (F G) (F (zaddO G (zaddO H H))))
    exact ⟨hRp point h1, hRm point h2, hRh point h3⟩

/-! ### Step 2: a splitting bit -/

/-- A continuous `f : 2^ω → Bool` depends only on a bounded initial segment. -/
theorem uniform_of_continuous_bool {f : Oracle → Bool} (hf : Continuous f) :
    ∃ n₀, ∀ Z Z' : Oracle, (∀ i < n₀, Z i = Z' i) → f Z = f Z' := by
  have hk : ∀ Z, ∃ k, cyl Z k ⊆ f ⁻¹' {f Z} := fun Z =>
    exists_cyl_subset ((isOpen_discrete _).preimage hf) rfl
  choose k hk using hk
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun Z => cyl Z (k Z))
    (fun Z => isOpen_cyl Z (k Z)) (fun Z _ => Set.mem_iUnion.mpr ⟨Z, mem_cyl Z _⟩)
  refine ⟨t.sup k, fun Z Z' hZZ' => ?_⟩
  obtain ⟨Z₁, hZ₁t, hZ₁⟩ : ∃ Z₁ ∈ t, Z ∈ cyl Z₁ (k Z₁) := by
    simpa using ht (Set.mem_univ Z)
  have hle : k Z₁ ≤ t.sup k := Finset.le_sup hZ₁t
  have h1 : f Z = f Z₁ := hk Z₁ hZ₁
  have h2 : f Z' = f Z₁ := hk Z₁ (fun i hi => by rw [← hZZ' i (by omega)]; exact hZ₁ i hi)
  rw [h1, h2]

theorem step_split {F : Oracle → Oracle} (hF : Continuous F) (hP : InducesProperties F)
    (α : List Bool) : ∃ τ : List Bool, α <+: τ ∧ ∃ (j : ℕ) (b : Bool),
      ∀ W, F (prep τ W) j = xor b (W 0) := by
  obtain ⟨X, hX, Y, hY, hXY⟩ := hP.nonconst (Ncyl α) (isOpen_Ncyl α)
    ⟨prep α zzero, prep_mem _ _⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hXY
  let f : Oracle → Bool := fun Z => F Z j
  have hf : Continuous f := (continuous_apply j).comp hF
  obtain ⟨n₀, hn₀⟩ := uniform_of_continuous_bool hf
  let NC : List Bool → Prop := fun σ => ∃ Z ∈ Ncyl σ, ∃ Z' ∈ Ncyl σ, f Z ≠ f Z'
  have hNClen : ∀ σ, NC σ → σ.length < n₀ := by
    intro σ ⟨Z, hZ, Z', hZ', hne⟩
    by_contra hlen
    apply hne
    apply hn₀
    intro i hi
    rw [mem_Ncyl] at hZ hZ'
    rw [hZ i (by omega), hZ' i (by omega)]
  have descent : ∀ d σ, n₀ - σ.length ≤ d → NC σ →
      ∃ τ, σ <+: τ ∧ NC τ ∧ ¬ NC (τ ++ [false]) ∧ ¬ NC (τ ++ [true]) := by
    intro d
    induction d with
    | zero =>
      intro σ hd hσ
      have := hNClen σ hσ
      omega
    | succ d ih =>
      intro σ hd hσ
      have hlt := hNClen σ hσ
      by_cases h0 : NC (σ ++ [false])
      · obtain ⟨τ, hστ, h⟩ := ih (σ ++ [false]) (by simp; omega) h0
        exact ⟨τ, (List.prefix_append σ _).trans hστ, h⟩
      · by_cases h1 : NC (σ ++ [true])
        · obtain ⟨τ, hστ, h⟩ := ih (σ ++ [true]) (by simp; omega) h1
          exact ⟨τ, (List.prefix_append σ _).trans hστ, h⟩
        · exact ⟨σ, List.prefix_refl σ, hσ, h0, h1⟩
  obtain ⟨τ, hατ, hτ, h0, h1⟩ := descent _ α le_rfl ⟨X, hX, Y, hY, hj⟩
  have const : ∀ c : Bool, ∀ Z ∈ Ncyl (τ ++ [c]), f Z = f (prep (τ ++ [c]) zzero) := by
    intro c Z hZ
    by_contra hne
    cases c
    · exact h0 ⟨Z, hZ, _, prep_mem _ _, hne⟩
    · exact h1 ⟨Z, hZ, _, prep_mem _ _, hne⟩
  have hmem : ∀ W, prep τ W ∈ Ncyl (τ ++ [W 0]) := prep_append_mem τ
  refine ⟨τ, hατ, j, f (prep (τ ++ [false]) zzero), fun W => ?_⟩
  have hdiff : f (prep (τ ++ [true]) zzero) = !f (prep (τ ++ [false]) zzero) := by
    by_contra hne
    have heq : f (prep (τ ++ [true]) zzero) = f (prep (τ ++ [false]) zzero) := by
      revert hne
      cases f (prep (τ ++ [true]) zzero) <;> cases f (prep (τ ++ [false]) zzero) <;> simp
    obtain ⟨Z, hZ, Z', hZ', hne'⟩ := hτ
    apply hne'
    have hval : ∀ V ∈ Ncyl τ, f V = f (prep (τ ++ [false]) zzero) := by
      intro V hV
      have e := eq_prep_of_mem hV
      have hV' := hmem (dropF τ.length V)
      rw [← e] at hV'
      cases hc : dropF τ.length V 0
      · rw [hc] at hV'; exact const false V hV'
      · rw [hc] at hV'; rw [const true V hV', heq]
    rw [hval Z hZ, hval Z' hZ']
  cases hW : W 0
  · have := const false _ (hW ▸ hmem W)
    simpa [f] using this
  · have := const true _ (hW ▸ hmem W)
    simp only [f] at this hdiff ⊢
    rw [this, hdiff]
    simp

/-! ### Step 4 and Proposition 3.1 -/

theorem iterate_shift_zero (X : Oracle) (m : ℕ) : (shift^[m] X) 0 = X m := by
  induction m generalizing X with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih]; rfl

theorem prop_3_1 {F : Oracle → Oracle} (hF : Continuous F) (hP : InducesProperties F)
    (ρ : List Bool) : ∃ τ : List Bool, ρ <+: τ ∧
      ∃ Γ : Oracle → Oracle, IsTTFunctional Γ ∧ ∀ X, Γ (F (prep τ X)) = X := by
  obtain ⟨α, β, hρα, hlen, Φp, Φm, Φh, hp, hm, hh, hR⟩ := step_relations hF hP ρ
  obtain ⟨τ, hατ, j, b, hsplit⟩ := step_split hF hP α
  obtain ⟨Θ, hΘ, hΘW⟩ := shift_functional hP.computable hlen hατ hp hm hh hR hsplit
  refine ⟨τ, hρα.trans hατ, fun A m => xor b ((Θ^[m] A) j),
    (isTTFunctional_xor b).comp (hΘ.iterate j), fun X => ?_⟩
  have hit : ∀ m, Θ^[m] (F (prep τ X)) = F (prep τ (shift^[m] X)) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hΘW, ← Function.iterate_succ_apply' shift]
  funext m
  simp only [hit, hsplit, iterate_shift_zero]
  cases b <;> simp

/-- Consequence of Proposition 3.1: `X ≤tt F X` for all `X`. -/
theorem le_tt_of_prop_3_1 {F : Oracle → Oracle} (hF : Continuous F) (hP : InducesProperties F)
    (X : Oracle) : TTReducible X (F X) := by
  obtain ⟨τ, -, Γ, hΓ, hΓX⟩ := prop_3_1 hF hP []
  have h1 : TTReducible X (F (prep τ X)) := ⟨Γ, hΓ, hΓX X⟩
  exact h1.trans (hP.mono _ _ (prep_ttEquiv τ X).1)

end TT
