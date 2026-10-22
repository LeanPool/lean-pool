/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_LevelNFunctionField
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

import LeanPool.FLTEichlerShimura.Theorems.Thm_WLight_exists_levelFraction_of_stable_family
import LeanPool.FLTEichlerShimura.Theorems.Thm_WLight_levelN_structure_package

/-!
# Ratios of modular forms as Fricke fractions

A ratio of modular forms for a finite-index subgroup containing Γ(N) is locally a fraction
of elements of ℂ[j, f_v]. The denominator is nonzero on a punctured neighbourhood of every
point, so the statement applies at poles as well as regular points.

The normalization argument uses the holomorphic functions f g¹¹ Δ⁻ᵏ and g¹² Δ⁻ᵏ. Its
auxiliary lemmas adapt the existing q-expansion bridge's toolkit; this file is a separate,
handwritten extension and does not represent an additional Prove2Me node.
-/

open UpperHalfPlane Filter
open scoped MatrixGroups Manifold Topology ModularForm

namespace ModularCurve.LevelN

noncomputable section

local notation "Δ" => ModularForm.discriminant

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

abbrev den (γ : SL(2, ℤ)) (τ : ℍ) : ℂ := denom (γ : GL (Fin 2) ℝ) τ

theorem den_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : den γ τ ≠ 0 := denom_ne_zero _ _

theorem apply_smul_eq_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = (f ∣[k] γ) τ * den γ τ ^ k := by
  rw [ModularForm.SL_slash_apply, mul_assoc, ← zpow_add₀ (den_ne_zero γ τ), neg_add_cancel,
    zpow_zero, mul_one]

theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) : Δ (γ • τ) = den γ τ ^ (12 : ℤ) * Δ τ := by
  have hmem : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem τ
  simpa [ModularGroup.sl_moeb] using this


theorem bounded_discriminant_pow (n : ℕ) :
    IsBoundedAtImInfty ((Δ : ℍ → ℂ) ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact Filter.const_boundedAtFilter _ _
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul ModularForm.discriminant_isZeroAtImInfty.isBoundedAtImInfty

def FF (k : ℤ) (f g : ℍ → ℂ) : ℍ → ℂ := fun τ => f τ * g τ ^ 11 * Δ τ ^ (-k)

theorem FF_apply (k : ℤ) (f g : ℍ → ℂ) (τ : ℍ) : FF k f g τ = f τ * g τ ^ 11 * Δ τ ^ (-k) := rfl

theorem zpow_neg_mul_pow_toNat (x : ℂ) (hx : x ≠ 0) (k : ℤ) :
    x ^ (-k) * x ^ k.toNat = x ^ (-k).toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  have := Int.toNat_sub_toNat_neg k
  omega

theorem FF_mul_pow (k : ℤ) (f g : ℍ → ℂ) :
    FF k f g * (Δ : ℍ → ℂ) ^ k.toNat = f * g ^ 11 * (Δ : ℍ → ℂ) ^ (-k).toNat := by
  funext τ
  simp only [Pi.mul_apply, Pi.pow_apply, FF_apply]
  rw [mul_assoc, zpow_neg_mul_pow_toNat _ (ModularForm.discriminant_ne_zero τ)]

theorem mdifferentiable_discriminant : MDiff (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

theorem mdifferentiable_discriminant_zpow (n : ℤ) : MDiff (fun τ : ℍ => Δ τ ^ n) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hd : DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_discriminant
  have : (fun τ : ℍ => Δ τ ^ n) ∘ ofComplex = fun z => ((Δ : ℍ → ℂ) ∘ ofComplex) z ^ n := rfl
  rw [this]
  exact hd.zpow (Or.inl fun z hz => by
    rw [Function.comp_apply]; exact ModularForm.discriminant_ne_zero _)

theorem mdifferentiable_FF
    (k : ℤ) {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g) : MDiff (FF k f g) := by
  have : FF k f g = f * g ^ 11 * (fun τ : ℍ => Δ τ ^ (-k)) := by
    funext τ; simp [FF_apply]
  rw [this]
  exact (hf.mul (hg.pow 11)).mul (mdifferentiable_discriminant_zpow (-k))

theorem factor_cancel (d : ℂ) (hd : d ≠ 0) (k : ℤ) :
    d ^ k * (d ^ k) ^ 11 * (d ^ (12 : ℤ)) ^ (-k) = 1 := by
  rw [← zpow_natCast (d ^ k) 11, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hd, ← zpow_add₀ hd]
  have : k + k * ((11 : ℕ) : ℤ) + 12 * -k = 0 := by push_cast; ring
  rw [this, zpow_zero]

theorem FF_smul (k : ℤ) (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    FF k f g (γ • τ) = FF k (f ∣[k] γ) (g ∣[k] γ) τ := by
  rw [FF_apply, FF_apply, apply_smul_eq_slash (k := k) f γ τ, apply_smul_eq_slash (k := k) g γ τ,
    discriminant_smul γ τ]
  have hd := den_ne_zero γ τ
  set d := den γ τ
  rw [mul_pow, mul_zpow]
  have hc := factor_cancel d hd k
  calc (f ∣[k] γ) τ * d ^ k * ((g ∣[k] γ) τ ^ 11 * (d ^ k) ^ 11)
      * ((d ^ (12 : ℤ)) ^ (-k) * Δ τ ^ (-k))
    = (f ∣[k] γ) τ * (g ∣[k] γ) τ ^ 11 * Δ τ ^ (-k)
          * (d ^ k * (d ^ k) ^ 11 * (d ^ (12 : ℤ)) ^ (-k)) := by
        ring
    _ = (f ∣[k] γ) τ * (g ∣[k] γ) τ ^ 11 * Δ τ ^ (-k) := by rw [hc, mul_one]

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

theorem FF_smul_of_mem
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ)
    (τ : ℍ) : FF k f g (δ • τ) = FF k f g τ := by
  rw [FF_smul]
  have hmem : (δ : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := ⟨δ, hδ, rfl⟩
  have hf : (f : ℍ → ℂ) ∣[k] δ = f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantFormClass.slash_action_eq f _ hmem
  have hg : (g : ℍ → ℂ) ∣[k] δ = g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantFormClass.slash_action_eq g _ hmem
  rw [hf, hg]

theorem isBoundedAtImInfty_FF_smul
    [Γ.FiniteIndex] (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty ((fun τ => FF k f g (γ • τ)) * (Δ : ℍ → ℂ) ^ k.toNat) := by
  have : (fun τ => FF k f g (γ • τ)) = FF k ((f : ℍ → ℂ) ∣[k] γ) ((g : ℍ → ℂ) ∣[k] γ) := by
    funext τ; exact FF_smul k f g γ τ
  rw [this, FF_mul_pow]
  have hg11 : IsBoundedAtImInfty (((g : ℍ → ℂ) ∣[k] γ) ^ 11) := by
    have hb := ModularFormClass.bdd_at_infty_slash g γ
    have : ∀ n : ℕ, IsBoundedAtImInfty (((g : ℍ → ℂ) ∣[k] γ) ^ n) := by
      intro n
      induction n with
      | zero => rw [pow_zero]; exact Filter.const_boundedAtFilter _ _
      | succ n ih => rw [pow_succ]; exact ih.mul hb
    exact this 11
  exact ((ModularFormClass.bdd_at_infty_slash f γ).mul hg11).mul (bounded_discriminant_pow _)


variable (N : ℕ) [NeZero N]

theorem mdifferentiable_of_mem {F : ℍ → ℂ} (hF : F ∈ ring N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.2.2.2.2.1 F hF

theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℍ → ℂ} (ha : a ∈ ring N) (hb : b ∈ ring N)
    (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.2.2.2.2.2 a b ha hb hab


variable (M : ℕ) [NeZero M]
def famS : Set (ℍ → ℂ) :=
  {G | MDiff G ∧ (∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, G (δ • τ) = G τ) ∧
    ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((fun τ => G (γ • τ)) * (Δ : ℍ → ℂ) ^ m)}

theorem mdifferentiable_sl_smul (γ : SL(2, ℤ)) : MDiff (fun τ : ℍ => γ • τ) := by
  have : (fun τ : ℍ => γ • τ) = fun τ : ℍ => (γ : GL (Fin 2) ℝ) • τ := by
    funext τ; exact ModularGroup.sl_moeb γ τ
  rw [this]
  apply UpperHalfPlane.mdifferentiable_smul
  simp

omit [NeZero M] in
theorem famS_stable (γ : SL(2, ℤ)) : ∀ G ∈ famS M, (G ∘ (γ • ·)) ∈ famS M := by
  rintro G ⟨hG, hinv, hpb⟩
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M
  refine ⟨hG.comp (mdifferentiable_sl_smul γ), fun δ hδ τ => ?_, fun γ' => ?_⟩
  · change G (γ • δ • τ) = G (γ • τ)
    have hconj : γ * δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma M :=
      Subgroup.Normal.conj_mem inferInstance δ hδ γ
    have := hinv _ hconj (γ • τ)
    rw [← this, ← mul_smul, ← mul_smul]
    congr 1
    group
  · obtain ⟨m, hm⟩ := hpb (γ * γ')
    refine ⟨m, ?_⟩
    have : (fun τ => (G ∘ (γ • ·)) (γ' • τ)) = fun τ => G ((γ * γ') • τ) := by
      funext τ; simp [mul_smul]
    rw [this]; exact hm

theorem exists_levelFraction {G : ℍ → ℂ} (hG : G ∈ famS M) :
    ∃ a b : ℍ → ℂ, a ∈ ring M ∧ b ∈ ring M ∧ b ≠ 0 ∧ G * b = a :=
  WLight.exists_levelFraction_of_stable_family M PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp M)
    (fun v τ => rfl) (fricke M) (fun v τ => rfl) jAnalytic (fun τ => rfl) (famS M)
    (fun G hG => hG.1)
    (fun G hG => by
      obtain ⟨m, hm⟩ := hG.2.2 1
      exact ⟨m, by simpa using hm⟩)
    (famS_stable M) (fun G hG => hG.2.1) hG

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

omit [NeZero M] in
theorem FF_mem_famS (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) [Γ.FiniteIndex]
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : FF k f g ∈ famS M :=
  ⟨mdifferentiable_FF k f.holo' g.holo', fun _ hδ τ => FF_smul_of_mem f g (hΓ hδ) τ,
    fun γ => ⟨k.toNat, isBoundedAtImInfty_FF_smul f g γ⟩⟩




private theorem fricke_eventually_ne_zero {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hf0 : f ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), f (ofComplex z) ≠ 0 := by
  have hH : ∀ᶠ w in 𝓝[≠] τ, f w ≠ 0 := by
    by_contra h
    exact hf0 (UpperHalfPlane.eq_zero_of_frequently hf
      (by simpa only [Filter.not_eventually, not_not] using h))
  have hmap := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rw [hpre] at hmap
  rw [← hmap, Filter.eventually_map]
  simpa only [ofComplex_apply] using hH

/-- A ratio of modular forms for a group containing Γ(N) is a rational expression in j and
the Fricke functions, with equality on punctured neighbourhoods and nonzero denominator. -/
public theorem exists_frickeFraction_of_modularForm
    (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (f g : ModularForm Γ k) (hg : g ≠ 0) :
    ∃ a b : ℍ → ℂ, a ∈ ModularCurve.LevelN.ring N ∧ b ∈ ModularCurve.LevelN.ring N ∧
      b ≠ 0 ∧ ∀ τ : ℍ,
        (∀ᶠ z in 𝓝[≠] (τ : ℂ), b (ofComplex z) ≠ 0) ∧
        (fun z : ℂ => f (ofComplex z) / g (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
          fun z : ℂ => a (ofComplex z) / b (ofComplex z) := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := exists_levelFraction N (FF_mem_famS N hΓ f g)
  obtain ⟨c, d, hc, hd, hd0, hcd⟩ := exists_levelFraction N (FF_mem_famS N hΓ g g)
  have hc0 : c ≠ 0 := by
    intro hz
    have hprod : FF k g g * d = 0 := hcd.trans hz
    rcases (UpperHalfPlane.mul_eq_zero_iff (mdifferentiable_FF k g.holo' g.holo')
      (mdifferentiable_of_mem N hd)).mp hprod with hG | hD
    · apply hg
      ext τ
      by_contra hτ
      exact mul_ne_zero (mul_ne_zero hτ (pow_ne_zero _ hτ))
        (zpow_ne_zero _ (ModularForm.discriminant_ne_zero τ)) (congrFun hG τ)
    · exact hd0 hD
  have hbc0 : b * c ≠ 0 := by
    intro hz
    exact ((eq_zero_or_eq_zero_of_mul_eq_zero N hb hc hz).elim hb0 hc0)
  have hcross (τ : ℍ) : f τ * (b * c) τ = g τ * (a * d) τ := by
    have h1 := congrFun hab τ
    have h2 := congrFun hcd τ
    change FF k f g τ * b τ = a τ at h1
    change FF k g g τ * d τ = c τ at h2
    simp only [Pi.mul_apply]
    rw [← h1, ← h2, FF_apply, FF_apply]
    ring
  refine ⟨a * d, b * c, (ModularCurve.LevelN.ring N).mul_mem ha hd,
    (ModularCurve.LevelN.ring N).mul_mem hb hc, hbc0, fun τ => ?_⟩
  have hbnz := fricke_eventually_ne_zero
    (mdifferentiable_of_mem N ((ModularCurve.LevelN.ring N).mul_mem hb hc)) hbc0 τ
  refine ⟨hbnz, ?_⟩
  filter_upwards [hbnz, fricke_eventually_ne_zero (f := (g : ℍ → ℂ))
    (ModularFormClass.holo g)
    (fun h => hg (DFunLike.coe_injective h)) τ] with z hbz hgz
  exact (div_eq_div_iff hgz hbz).mpr (by simpa only [mul_comm] using hcross (ofComplex z))

end

end ModularCurve.LevelN
