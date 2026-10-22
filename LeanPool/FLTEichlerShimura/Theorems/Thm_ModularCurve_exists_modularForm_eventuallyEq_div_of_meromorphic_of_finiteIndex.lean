/-
Based on Prove2Me node
ModularCurve.exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex
(d2a2e462-438f-52cb-bf58-d01574d87141) by Claude (2026-09-05).

Proof based on Prove2Me submission c1458b6a-e3de-57b0-9207-0fd3c8c04053
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Analysis.Meromorphic.Basic

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Meromorphic modular functions as quotients of modular forms

For any finite-index subgroup Γ of SL₂(ℤ), a Γ-invariant meromorphic function on the upper
half-plane with at most exponential growth at every cusp is a quotient of two modular forms of
the same weight, with nonzero denominator. Equality is on punctured neighbourhoods, so poles
and arbitrary values assigned at poles do not require pointwise division identities.

The proof clears the finitely many pole orbits with level-one modular forms and multiplies by
a sufficient power of the discriminant to control growth at all cusps. Meromorphic normal
forms extend the resulting numerator holomorphically across its removable singularities.

Prove2Me node: `d2a2e462-438f-52cb-bf58-d01574d87141`.
Accepted proof: `c1458b6a-e3de-57b0-9207-0fd3c8c04053`, by Claude, 2026-09-05.
Upstream FLT proof:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex.lean
-/

section

noncomputable section

open UpperHalfPlane Complex Filter Topology Asymptotics ModularForm ModularFormClass
  EisensteinSeries

open scoped MatrixGroups Modular ModularForm Manifold

namespace ModularCurve
namespace GAGAMeroFun

attribute [local instance] Fintype.ofFinite

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem tendsto_coe_nhdsNE (τ : ℍ) :
    Tendsto ((↑) : ℍ → ℂ) (𝓝[≠] τ) (𝓝[≠] (τ : ℂ)) :=
  (map_coe_nhdsNE τ).le

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

scoped instance nhdsNE_neBot (τ : ℍ) : (𝓝[≠] τ).NeBot := by
  have h : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ)).NeBot := by
    rw [map_coe_nhdsNE]; infer_instance
  exact Filter.NeBot.of_map h

theorem eventually_im_pos (τ : ℍ) : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ), 0 < z.im :=
  mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem im_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : (ofComplex z).im = z.im := by
  rw [ofComplex_apply_of_im_pos hz]
  rfl

theorem tendsto_smul_nhdsNE (g : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (fun w : ℍ => g • w) (𝓝[≠] τ) (𝓝[≠] (g • τ)) := by
  have hc : Continuous fun w : ℍ => g • w :=
    show Continuous fun w : ℍ => ((g : GL (Fin 2) ℝ)) • w from continuous_const_smul _
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun h => hw (MulAction.injective g h)

theorem eq_of_eventuallyEq_of_continuousAt {u v : ℍ → ℂ} {τ : ℍ} (hu : ContinuousAt u τ)
    (hv : ContinuousAt v τ) (h : ∀ᶠ w in 𝓝[≠] τ, u w = v w) : u τ = v τ :=
  tendsto_nhds_unique ((hu.tendsto.mono_left nhdsWithin_le_nhds).congr' h)
    (hv.tendsto.mono_left nhdsWithin_le_nhds)

def A₀ : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3)

def D : ModularForm 𝒮ℒ 12 := ModularFormClass.modularForm CuspForm.discriminant

theorem coe_D : (⇑D : ℍ → ℂ) = ModularForm.discriminant := by
  simp [D]

theorem D_ne_zero (τ : ℍ) : D τ ≠ 0 := by
  rw [coe_D]
  exact ModularForm.discriminant_ne_zero τ

def P (t : ℍ) : ModularForm 𝒮ℒ 12 := (D t) • A₀ - (A₀ t) • D

theorem P_apply (t τ : ℍ) : P t τ = D t * A₀ τ - A₀ t * D τ := by
  simp [P, sub_apply, smul_eq_mul]

theorem P_self (t : ℍ) : P t t = 0 := by
  rw [P_apply]; ring

theorem coeff_zero_A₀ : (PowerSeries.coeff 0) (qExpansion 1 ⇑A₀) = 1 := by
  rw [A₀, coe_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E_qExpansion_coeff_zero _ ⟨2, rfl⟩, one_pow]

theorem coeff_zero_D : (PowerSeries.coeff 0) (qExpansion 1 ⇑D) = 0 := by
  have := CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  simpa [D] using this

theorem coeff_zero_P (t : ℍ) : (PowerSeries.coeff 0) (qExpansion 1 ⇑(P t)) = D t := by
  rw [P, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    FunLike.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_sub,
    PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_zero_A₀, coeff_zero_D]
  simp

theorem P_ne_zero (t : ℍ) : P t ≠ 0 := by
  intro h
  have h1 := coeff_zero_P t
  rw [h] at h1
  simp [UpperHalfPlane.qExpansion_zero] at h1
  exact D_ne_zero t h1.symm

theorem levelOne_smul {k : ℤ} (f : ModularForm 𝒮ℒ k) (g : SL(2, ℤ)) (τ : ℍ) :
    f (g • τ) = denom (g : GL (Fin 2) ℝ) τ ^ k * f τ := by
  have := SlashInvariantForm.slash_action_eqn'' f (γ := (g : GL (Fin 2) ℝ))
    (MonoidHom.mem_range.mpr ⟨g, rfl⟩) τ
  simpa using this

theorem levelOne_slash {k : ℤ} (f : ModularForm 𝒮ℒ k) (g : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] g = f := by
  rw [ModularForm.SL_slash]
  exact f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨g, rfl⟩)

theorem P_smul_self (t : ℍ) (g : SL(2, ℤ)) : P t (g • t) = 0 := by
  rw [levelOne_smul, P_self, mul_zero]

def restrict (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm Γ k where
  toFun := f
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, -, rfl⟩ : ∃ γ ∈ Γ, (γ : GL (Fin 2) ℝ) = A := by
      simp only [Subgroup.mem_map] at hA
      exact hA
    exact f.slash_action_eq' _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  holo' := f.holo'
  bdd_at_cusps' := fun {c} hc => f.bdd_at_cusps'
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)

@[scoped simp] theorem coe_restrict (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    (⇑(restrict Γ f) : ℍ → ℂ) = f := rfl

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm 𝒮ℒ k) : (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (by simpa using h)
  · rintro rfl
    rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) (hf : f ≠ 0) (τ : ℍ) :
    ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem D_bound : ∃ cD AD : ℝ, 0 ≤ cD ∧
    ∀ z : ℍ, AD ≤ z.im → ‖D z‖ ≤ cD * Real.exp (-2 * Real.pi * z.im) := by
  have h := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hc
  refine ⟨max c 0, A, le_max_right _ _, fun z hz => ?_⟩
  have h1 := hA z hz
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp, div_one] at h1
  have hDz : D z = CuspForm.discriminant z := by simp [D]
  rw [hDz]
  calc ‖CuspForm.discriminant z‖ ≤ c * Real.exp (-2 * Real.pi * z.im) := h1
    _ ≤ max c 0 * Real.exp (-2 * Real.pi * z.im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

theorem form_bound {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} (f : ModularForm Γ k) :
    ∃ M A : ℝ, 0 ≤ M ∧ ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ M := by
  have h := ModularFormClass.bdd_at_infty f
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at h
  obtain ⟨M, A, hMA⟩ := h
  exact ⟨max M 0, A, le_max_right _ _, fun z hz => (hMA z hz).trans (le_max_left _ _)⟩

theorem bound_of_isBigO {u : ℍ → ℂ} {C : ℝ}
    (h : u =O[atImInfty] fun τ : ℍ => Real.exp (C * τ.im)) :
    ∃ c A : ℝ, 0 ≤ c ∧ 0 < A ∧
      ∀ τ : ℍ, A ≤ τ.im → ‖u τ‖ ≤ c * Real.exp (max C 0 * τ.im) := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hc
  refine ⟨max c 0, max A 1, le_max_right _ _, by positivity, fun τ hτ => ?_⟩
  have h1 := hA τ ((le_max_left _ _).trans hτ)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp] at h1
  calc ‖u τ‖ ≤ c * Real.exp (C * τ.im) := h1
    _ ≤ max c 0 * Real.exp (C * τ.im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max c 0 * Real.exp (max C 0 * τ.im) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_left _ _) τ.im_pos.le)) (le_max_right _ _)

theorem norm_bound_aux {a d p y c C cD MP : ℝ} {n : ℕ}
    (ha : a ≤ c * Real.exp (C * y)) (hd : d ≤ cD * Real.exp (-2 * Real.pi * y)) (hp : p ≤ MP)
    (h0d : 0 ≤ d) (h0p : 0 ≤ p) (hc : 0 ≤ c) (hcD : 0 ≤ cD) (hMP : 0 ≤ MP)
    (hC : C ≤ n) (hy : 0 ≤ y) :
    a * (d * p) ^ n ≤ c * (cD * MP) ^ n := by
  have h1 : d * p ≤ cD * Real.exp (-2 * Real.pi * y) * MP :=
    mul_le_mul hd hp h0p (by positivity)
  have h2 : (d * p) ^ n ≤ (cD * Real.exp (-2 * Real.pi * y) * MP) ^ n :=
    pow_le_pow_left₀ (mul_nonneg h0d h0p) h1 n
  have h3 : a * (d * p) ^ n ≤
      c * Real.exp (C * y) * (cD * Real.exp (-2 * Real.pi * y) * MP) ^ n :=
    mul_le_mul ha h2 (pow_nonneg (mul_nonneg h0d h0p) n) (by positivity)
  refine h3.trans ?_
  have key : Real.exp (C * y) * Real.exp (-2 * Real.pi * y) ^ n ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hny : 0 ≤ (n : ℝ) * y := by positivity
    have hCy : C * y ≤ (n : ℝ) * y := mul_le_mul_of_nonneg_right hC hy
    nlinarith [Real.pi_gt_three, hny, hCy,
      mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hny]
  calc c * Real.exp (C * y) * (cD * Real.exp (-2 * Real.pi * y) * MP) ^ n
        = c * (cD * MP) ^ n * (Real.exp (C * y) * Real.exp (-2 * Real.pi * y) ^ n) := by
          rw [mul_pow, mul_pow, mul_pow]; ring
    _ ≤ c * (cD * MP) ^ n * 1 :=
          mul_le_mul_of_nonneg_left key (by positivity)
    _ = c * (cD * MP) ^ n := mul_one _

structure Datum (Γ : Subgroup SL(2, ℤ)) where

  F : ℍ → ℂ
  mer : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)
  inv : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ

  C : SL(2, ℤ) → ℝ

  c : SL(2, ℤ) → ℝ

  A : SL(2, ℤ) → ℝ
  C_nonneg : ∀ σ, 0 ≤ C σ
  c_nonneg : ∀ σ, 0 ≤ c σ
  A_pos : ∀ σ, 0 < A σ
  bound : ∀ σ (τ : ℍ), A σ ≤ τ.im → ‖F (σ • τ)‖ ≤ c σ * Real.exp (C σ * τ.im)

namespace Datum

variable {Γ : Subgroup SL(2, ℤ)} (X : Datum Γ)

def f : ℂ → ℂ := fun z => X.F (ofComplex z)

def ord (τ : ℍ) : WithTop ℤ := meromorphicOrderAt X.f (τ : ℂ)

theorem det_pos (g : SL(2, ℤ)) : 0 < ((g : GL (Fin 2) ℝ)).val.det := by
  have h : ((g : GL (Fin 2) ℝ)).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  rw [h]; exact one_pos

theorem ord_smul (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    X.ord (γ • τ) = X.ord τ := by
  unfold ord Datum.f
  rw [show (((γ • τ : ℍ)) : ℂ) = ↑(((γ : GL (Fin 2) ℝ)) • τ) by simp,
    ← meromorphicOrderAt_comp_smul (det_pos γ)]
  congr 1
  funext z
  rw [show (((γ : GL (Fin 2) ℝ)) • ofComplex z) = γ • ofComplex z by simp]
  exact X.inv γ hγ _

theorem ord_smul_nonneg (σ : SL(2, ℤ)) (τ : ℍ) (hτ : X.A σ < τ.im) : 0 ≤ X.ord (σ • τ) := by
  unfold ord Datum.f
  rw [show (((σ • τ : ℍ)) : ℂ) = ↑(((σ : GL (Fin 2) ℝ)) • τ) by simp,
    ← meromorphicOrderAt_comp_smul (det_pos σ)]
  have hu' : (fun z : ℂ => X.F (((σ : GL (Fin 2) ℝ)) • ofComplex z)) =
      fun z => X.F (σ • ofComplex z) := by
    funext z
    rw [show (((σ : GL (Fin 2) ℝ)) • ofComplex z) = σ • ofComplex z by simp]
  rw [hu']
  set u : ℂ → ℂ := fun z => X.F (σ • ofComplex z) with hu_def
  by_cases hu : MeromorphicAt u (τ : ℂ)
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hu]
  by_contra hneg
  rw [not_le] at hneg
  have hcob := (tendsto_cobounded_iff_meromorphicOrderAt_neg hu).mpr hneg
  rw [← tendsto_norm_atTop_iff_cobounded] at hcob
  refine Filter.not_isBoundedUnder_of_tendsto_atTop hcob ?_
  have hopen : IsOpen {z : ℂ | X.A σ < z.im ∧ z.im < τ.im + 1} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hev : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ), X.A σ < z.im ∧ z.im < τ.im + 1 :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds ⟨by simpa using hτ, by simp⟩)
  refine ⟨X.c σ * Real.exp (X.C σ * (τ.im + 1)), ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [hev] with z hz
  have hzpos : 0 < z.im := (X.A_pos σ).trans hz.1
  change ‖X.F (σ • ofComplex z)‖ ≤ X.c σ * Real.exp (X.C σ * (τ.im + 1))
  have him : (ofComplex z).im = z.im := im_ofComplex_of_im_pos hzpos
  calc ‖X.F (σ • ofComplex z)‖ ≤ X.c σ * Real.exp (X.C σ * (ofComplex z).im) :=
        X.bound σ _ (by rw [him]; exact hz.1.le)
    _ ≤ X.c σ * Real.exp (X.C σ * (τ.im + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (X.c_nonneg σ)
        apply Real.exp_le_exp.mpr
        rw [him]
        exact mul_le_mul_of_nonneg_left hz.2.le (X.C_nonneg σ)

theorem eventually_ord_nonneg (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, 0 ≤ X.ord w := by
  have h := (X.mer τ).eventually_analyticAt
  have h2 : ∀ᶠ y in 𝓝[≠] (τ : ℂ), 0 ≤ meromorphicOrderAt X.f y :=
    h.mono fun y hy => hy.meromorphicOrderAt_nonneg
  exact (tendsto_coe_nhdsNE τ).eventually h2

def S : Set ℍ := {τ | X.ord τ < 0}

theorem finite_S_inter {K : Set ℍ} (hK : IsCompact K) : (X.S ∩ K).Finite := by
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover (fun x => {w | w ≠ x → 0 ≤ X.ord w})
    (fun x _ => by
      have := X.eventually_ord_nonneg x
      rw [eventually_nhdsWithin_iff] at this
      exact this)
  refine (t.finite_toSet).subset ?_
  rintro τ ⟨hτS, hτK⟩
  obtain ⟨x, hx, hτx⟩ := Set.mem_iUnion₂.mp (hcover hτK)
  by_contra hne
  have hτx' : τ ≠ x := fun h => hne (h ▸ hx)
  exact absurd (hτx hτx') (not_le.mpr hτS)

def ρ (q : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ) := (Quotient.out q)⁻¹

variable [Γ.FiniteIndex]

def K : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Γ,
    (fun τ : ℍ => (ρ q) • τ) '' ModularGroup.truncatedFundamentalDomain (X.A (ρ q))

theorem isCompact_K : IsCompact X.K :=
  isCompact_iUnion fun q =>
    (ModularGroup.isCompact_truncatedFundamentalDomain _).image
      (show Continuous fun τ : ℍ => ((ρ q : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ from
        continuous_const_smul _)

theorem finite_T : (X.S ∩ X.K).Finite := X.finite_S_inter X.isCompact_K

def Tf : Finset ℍ := X.finite_T.toFinset

theorem mem_Tf {t : ℍ} : t ∈ X.Tf ↔ t ∈ X.S ∧ t ∈ X.K := by
  simp [Tf]

theorem exists_mem_Tf (τ : ℍ) (hτ : X.ord τ < 0) :
    ∃ γ ∈ Γ, ∃ t ∈ X.Tf, τ = γ • t := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  set q : SL(2, ℤ) ⧸ Γ := (g : SL(2, ℤ) ⧸ Γ)
    with hq
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
  have hρ : ρ q = ((h : SL(2, ℤ)))⁻¹ * g⁻¹ := by
    simp [ρ, hq, hh, mul_inv_rev]
  have ht : ρ q • (g • τ) = ((h : SL(2, ℤ)))⁻¹ • τ := by
    rw [hρ, mul_smul, inv_smul_smul]
  have hmem : ((h : SL(2, ℤ)))⁻¹ ∈ Γ := inv_mem h.2
  refine ⟨h, h.2, ρ q • (g • τ), ?_, ?_⟩
  · rw [mem_Tf]
    constructor
    · change X.ord (ρ q • (g • τ)) < 0
      rw [ht, X.ord_smul _ hmem]
      exact hτ
    · refine Set.mem_iUnion.mpr ⟨q, Set.mem_image_of_mem _ ⟨hg, ?_⟩⟩
      by_contra him
      rw [not_le] at him
      have h0 := X.ord_smul_nonneg (ρ q) (g • τ) him
      rw [ht, X.ord_smul _ hmem] at h0
      exact absurd hτ (not_lt.mpr h0)
  · rw [ht, smul_inv_smul]

def Pf : ModularForm 𝒮ℒ ((X.Tf.card : ℤ) * 12) := prodEqualWeights (s := X.Tf) P

theorem coe_Pf : (⇑X.Pf : ℍ → ℂ) = ∏ t ∈ X.Tf, ⇑(P t) := by
  simp [Pf, prodEqualWeights, coe_prod]

def Ψ : ModularForm 𝒮ℒ (12 + (X.Tf.card : ℤ) * 12) := D.mul X.Pf

theorem Ψ_apply (τ : ℍ) : X.Ψ τ = D τ * X.Pf τ := by
  simp [Ψ, coe_mul]

def negord (t : ℍ) : ℕ := Int.toNat (-(WithTop.untopD 0 (X.ord t)))

def n : ℕ := 1 + ∑ q : SL(2, ℤ) ⧸ Γ, ⌈X.C (ρ q)⌉₊ +
  ∑ t ∈ X.Tf, X.negord t

theorem one_le_n : 1 ≤ X.n := by
  unfold n; omega

theorem C_le_n (q : SL(2, ℤ) ⧸ Γ) : X.C (ρ q) ≤ X.n := by
  have h1 : X.C (ρ q) ≤ ⌈X.C (ρ q)⌉₊ := Nat.le_ceil _
  have h2 : ⌈X.C (ρ q)⌉₊ ≤ ∑ q' : SL(2, ℤ) ⧸ Γ, ⌈X.C (ρ q')⌉₊ :=
    Finset.single_le_sum (f := fun q' => ⌈X.C (ρ q')⌉₊) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ q)
  have h3 : (⌈X.C (ρ q)⌉₊ : ℝ) ≤ (X.n : ℝ) := by
    unfold n
    exact_mod_cast (h2.trans (by omega))
  exact h1.trans h3

theorem negord_le_n {t : ℍ} (ht : t ∈ X.Tf) : X.negord t ≤ X.n := by
  have h2 : X.negord t ≤ ∑ t' ∈ X.Tf, X.negord t' :=
    Finset.single_le_sum (f := fun t' => X.negord t') (fun _ _ => Nat.zero_le _) ht
  unfold n
  omega

abbrev k : ℤ := (X.n : ℤ) * (12 + (X.Tf.card : ℤ) * 12)

def Φ : ModularForm 𝒮ℒ X.k := X.Ψ.pow X.n

theorem Φ_apply (τ : ℍ) : X.Φ τ = X.Ψ τ ^ X.n := by
  simp [Φ, coe_pow]

theorem Ψ_eq_zero_of_ord_neg (τ : ℍ) (hτ : X.ord τ < 0) : X.Ψ τ = 0 := by
  obtain ⟨γ, hγ, t, ht, rfl⟩ := X.exists_mem_Tf τ hτ
  rw [Ψ_apply, coe_Pf, Finset.prod_apply, Finset.prod_eq_zero ht (P_smul_self t γ), mul_zero]

theorem eventually_Ψ_ne_zero (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, X.Ψ w ≠ 0 := by
  have h : ∀ᶠ w in 𝓝[≠] τ, ∀ t ∈ X.Tf, (P t : ℍ → ℂ) w ≠ 0 :=
    (Filter.eventually_all_finset X.Tf).mpr fun t _ => eventually_ne_zero (P t) (P_ne_zero t) τ
  filter_upwards [h] with w hw
  rw [Ψ_apply, coe_Pf, Finset.prod_apply]
  exact mul_ne_zero (D_ne_zero w) (Finset.prod_ne_zero_iff.mpr hw)

theorem eventually_Φ_ne_zero (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, X.Φ w ≠ 0 := by
  filter_upwards [X.eventually_Ψ_ne_zero τ] with w hw
  rw [Φ_apply]
  exact pow_ne_zero _ hw

theorem order_Ψ_pos (τ : ℍ) (hτ : X.ord τ < 0) :
    ∃ m : ℤ, 1 ≤ m ∧ meromorphicOrderAt (fun z : ℂ => X.Ψ (ofComplex z)) (τ : ℂ) = m := by
  have han := analyticAt_comp_ofComplex X.Ψ τ
  have hne_top : meromorphicOrderAt (fun z : ℂ => X.Ψ (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt]
    exact eventually_nhdsNE_coe_iff.mpr (X.eventually_Ψ_ne_zero τ)
  have hpos : 0 < meromorphicOrderAt (fun z : ℂ => X.Ψ (ofComplex z)) (τ : ℂ) := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos han.meromorphicAt).mp
    have h1 : Tendsto (fun z : ℂ => X.Ψ (ofComplex z)) (𝓝 (τ : ℂ)) (𝓝 (X.Ψ (ofComplex τ))) :=
      han.continuousAt.tendsto
    rw [ofComplex_apply, X.Ψ_eq_zero_of_ord_neg τ hτ] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne_top
  refine ⟨m, ?_, hm.symm⟩
  rw [← hm] at hpos
  have : (0 : ℤ) < m := by exact_mod_cast hpos
  omega

theorem ord_ge_of_neg (τ : ℍ) (hτ : X.ord τ < 0) :
    ∃ a : ℤ, X.ord τ = a ∧ -(X.n : ℤ) ≤ a := by
  obtain ⟨γ, hγ, t, ht, rfl⟩ := X.exists_mem_Tf τ hτ
  rw [X.ord_smul γ hγ] at hτ ⊢
  have hne : X.ord t ≠ ⊤ := by
    intro h; rw [h] at hτ; simp at hτ
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨a, ha.symm, ?_⟩
  have h1 : X.negord t ≤ X.n := X.negord_le_n ht
  have h2 : (X.negord t : ℤ) = -a ⊔ 0 := by
    simp [negord, ← ha, WithTop.untopD_coe]
  omega

def g₁ : ℂ → ℂ := fun z => X.F (ofComplex z) * X.Φ (ofComplex z)

theorem g₁_eq : X.g₁ = X.f * fun z : ℂ => X.Φ (ofComplex z) := rfl

omit [Γ.FiniteIndex] in
theorem mer' (τ : ℍ) : MeromorphicAt X.f (τ : ℂ) := X.mer τ

theorem order_g₁_nonneg (τ : ℍ) : 0 ≤ meromorphicOrderAt X.g₁ (τ : ℂ) := by
  have hφ := analyticAt_comp_ofComplex X.Φ τ
  rw [g₁_eq, meromorphicOrderAt_mul (X.mer' τ) hφ.meromorphicAt]
  by_cases hS : X.ord τ < 0
  · obtain ⟨m, hm1, hm⟩ := X.order_Ψ_pos τ hS
    have hΦord : meromorphicOrderAt (fun z : ℂ => X.Φ (ofComplex z)) (τ : ℂ) =
        (X.n : WithTop ℤ) * ((m : ℤ) : WithTop ℤ) := by
      rw [show (fun z : ℂ => X.Φ (ofComplex z)) = (fun z : ℂ => X.Ψ (ofComplex z)) ^ X.n from
          funext fun z => by simp [Φ_apply],
        meromorphicOrderAt_pow (analyticAt_comp_ofComplex X.Ψ τ).meromorphicAt, hm]
    obtain ⟨a, ha, hna⟩ := X.ord_ge_of_neg τ hS
    change 0 ≤ X.ord τ + _
    rw [hΦord, ha]
    have : (0 : ℤ) ≤ a + X.n * m := by nlinarith
    rw [← WithTop.coe_natCast, ← WithTop.coe_mul, ← WithTop.coe_add]
    exact_mod_cast this
  · exact add_nonneg (not_lt.mp hS) hφ.meromorphicOrderAt_nonneg

def U : Set ℂ := {z : ℂ | 0 < z.im}

theorem meromorphicOn_g₁ : MeromorphicOn X.g₁ U := by
  intro z hz
  have h1 : MeromorphicAt X.f z := X.mer ⟨z, hz⟩
  have h2 : AnalyticAt ℂ (fun w : ℂ => X.Φ (ofComplex w)) z := analyticAt_comp_ofComplex X.Φ ⟨z, hz⟩
  rw [g₁_eq]
  exact h1.mul h2.meromorphicAt

def G : ℂ → ℂ := toMeromorphicNFOn X.g₁ U

theorem G_eventuallyEq (τ : ℍ) : X.G =ᶠ[𝓝[≠] (τ : ℂ)] X.g₁ :=
  X.meromorphicOn_g₁.toMeromorphicNFOn_eq_self_on_nhdsNE (x := (τ : ℂ)) τ.im_pos

theorem G_analyticAt (τ : ℍ) : AnalyticAt ℂ X.G (τ : ℂ) := by
  have hnf : MeromorphicNFAt X.G (τ : ℂ) :=
    (meromorphicNFOn_toMeromorphicNFOn (f := X.g₁) (U := U)) (z := (τ : ℂ)) τ.im_pos
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_congr (X.G_eventuallyEq τ)]
  exact X.order_g₁_nonneg τ

def g₀ : ℍ → ℂ := fun τ => X.G (τ : ℂ)

theorem g₀_mdifferentiable : MDiff X.g₀ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have han : AnalyticAt ℂ X.G z := X.G_analyticAt ⟨z, hz⟩
  refine (han.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, g₀]
  rw [coe_ofComplex_of_im_pos hw]

theorem g₀_continuous : Continuous X.g₀ := X.g₀_mdifferentiable.continuous

theorem g₀_eventuallyEq (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, X.g₀ w = X.F w * X.Φ w := by
  have h := (tendsto_coe_nhdsNE τ).eventually (X.G_eventuallyEq τ)
  filter_upwards [h] with w hw
  simpa [g₀, g₁, ofComplex_apply] using hw

theorem g₀_slash (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    X.g₀ (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-X.k) = X.g₀ τ := by
  refine eq_of_eventuallyEq_of_continuousAt
    (u := fun τ : ℍ => X.g₀ (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-X.k)) (v := X.g₀)
    ?_ X.g₀_continuous.continuousAt ?_
  · have hc : Continuous fun w : ℍ => γ • w :=
      show Continuous fun w : ℍ => ((γ : GL (Fin 2) ℝ)) • w from continuous_const_smul _
    exact ((X.g₀_continuous.comp hc).mul
      (mdifferentiable_denom_zpow (γ : GL (Fin 2) ℝ) (-X.k)).continuous).continuousAt
  · have h1 := X.g₀_eventuallyEq τ
    have h2 := (tendsto_smul_nhdsNE γ τ).eventually (X.g₀_eventuallyEq (γ • τ))
    filter_upwards [h1, h2] with w hw1 hw2
    rw [hw2, hw1, X.inv γ hγ, levelOne_smul X.Φ γ w]
    have hd : denom (γ : GL (Fin 2) ℝ) w ^ X.k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
    rw [zpow_neg]
    field_simp

theorem g₀_bounded_slash (σ : SL(2, ℤ)) :
    IsBoundedAtImInfty (X.g₀ ∣[X.k] σ) := by
  set q : SL(2, ℤ) ⧸ Γ :=
    ((σ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) with hq
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ σ⁻¹
  have hσ : σ = ↑h * ρ q := by
    have : ρ q = (↑h)⁻¹ * σ := by simp [ρ, hq, hh, mul_inv_rev]
    rw [this, mul_inv_cancel_left]
  obtain ⟨cD, AD, hcD, hDb⟩ := D_bound
  obtain ⟨MP, AP, hMP, hPb⟩ := form_bound X.Pf
  set A₁ : ℝ := max (X.A (ρ q)) (max AD AP) with hA₁
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨X.c (ρ q) * (cD * MP) ^ X.n, A₁ + 1, fun z hz => ?_⟩
  have hfun : (X.g₀ ∣[X.k] σ) =
      fun w : ℍ => X.g₀ (σ • w) * denom (σ : GL (Fin 2) ℝ) w ^ (-X.k) := by
    funext w; rw [ModularForm.SL_slash_apply]
  have hcσ : Continuous fun w : ℍ => σ • w :=
    show Continuous fun w : ℍ => ((σ : GL (Fin 2) ℝ)) • w from continuous_const_smul _
  have hcont : Continuous (X.g₀ ∣[X.k] σ) := by
    rw [hfun]
    exact (X.g₀_continuous.comp hcσ).mul
      (mdifferentiable_denom_zpow (σ : GL (Fin 2) ℝ) (-X.k)).continuous
  have hlim : Tendsto (fun w => ‖(X.g₀ ∣[X.k] σ) w‖) (𝓝[≠] z) (𝓝 ‖(X.g₀ ∣[X.k] σ) z‖) :=
    ((hcont.continuousAt (x := z)).tendsto.mono_left nhdsWithin_le_nhds).norm
  refine le_of_tendsto hlim ?_
  have hev1 : ∀ᶠ w in 𝓝[≠] z, X.g₀ (σ • w) = X.F (σ • w) * X.Φ (σ • w) :=
    (tendsto_smul_nhdsNE σ z).eventually (X.g₀_eventuallyEq (σ • z))
  have hev2 : ∀ᶠ w : ℍ in 𝓝[≠] z, A₁ < w.im :=
    mem_nhdsWithin_of_mem_nhds
      ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds
        (show A₁ < z.im by linarith))
  filter_upwards [hev1, hev2] with w hw1 hw2
  rw [hfun]
  dsimp only
  rw [hw1]
  have hF : X.F (σ • w) = X.F (ρ q • w) := by
    rw [hσ, mul_smul, X.inv _ h.2]
  rw [hF, levelOne_smul X.Φ σ w]
  have hd : denom (σ : GL (Fin 2) ℝ) w ^ X.k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
  have halg : X.F (ρ q • w) * (denom (σ : GL (Fin 2) ℝ) w ^ X.k * X.Φ w) *
      denom (σ : GL (Fin 2) ℝ) w ^ (-X.k) = X.F (ρ q • w) * X.Φ w := by
    rw [zpow_neg]; field_simp
  rw [halg, norm_mul, Φ_apply, norm_pow, Ψ_apply, norm_mul]
  have hwA : X.A (ρ q) ≤ w.im := (le_max_left _ _).trans hw2.le
  have hwD : AD ≤ w.im := ((le_max_left _ _).trans (le_max_right _ _)).trans hw2.le
  have hwP : AP ≤ w.im := ((le_max_right _ _).trans (le_max_right _ _)).trans hw2.le
  exact norm_bound_aux (X.bound (ρ q) w hwA) (hDb w hwD) (hPb w hwP) (norm_nonneg _)
    (norm_nonneg _) (X.c_nonneg _) hcD hMP (X.C_le_n q) w.im_pos.le

def g : ModularForm Γ X.k where
  toFun := X.g₀
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ Γ, (γ : GL (Fin 2) ℝ) = A := by
      simp only [Subgroup.mem_map] at hA
      exact hA
    rw [← ModularForm.SL_slash]
    funext τ
    rw [ModularForm.SL_slash_apply]
    exact X.g₀_slash γ hγ τ
  holo' := X.g₀_mdifferentiable
  bdd_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro σ _
    exact X.g₀_bounded_slash σ

def h : ModularForm Γ X.k := restrict Γ X.Φ

theorem h_ne_zero : X.h ≠ 0 := by
  intro h0
  obtain ⟨w, hw⟩ := (X.eventually_Φ_ne_zero UpperHalfPlane.I).exists
  apply hw
  have : (X.h : ℍ → ℂ) w = 0 := by rw [h0]; rfl
  simpa [h] using this

theorem final (τ : ℍ) :
    (fun z : ℂ => X.F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (X.g : ℍ → ℂ) (ofComplex z) / (X.h : ℍ → ℂ) (ofComplex z) := by
  have h1 : X.G =ᶠ[𝓝[≠] (τ : ℂ)] X.g₁ := X.G_eventuallyEq τ
  have h2 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), X.Φ (ofComplex z) ≠ 0 :=
    eventually_nhdsNE_coe_iff.mpr (X.eventually_Φ_ne_zero τ)
  have h3 : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ), 0 < z.im := eventually_im_pos τ
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  change X.F (ofComplex z) = X.G ↑(ofComplex z) / X.Φ (ofComplex z)
  rw [eq_div_iff hz2, coe_ofComplex_of_im_pos hz3, hz1]
  rfl

end Datum

end ModularCurve.GAGAMeroFun

open ModularCurve.GAGAMeroFun in
theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℍ → ℂ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im)) :
    ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧
      ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by
  choose C₀ hC₀ using hcusp
  choose c A hc hA hb using fun σ => bound_of_isBigO (hC₀ σ)
  let X : Datum Γ :=
    { F := F
      mer := hmer
      inv := hinv
      C := fun σ => max (C₀ σ) 0
      c := c
      A := A
      C_nonneg := fun σ => le_max_right _ _
      c_nonneg := hc
      A_pos := hA
      bound := hb }
  exact ⟨X.k, X.g, X.h, X.h_ne_zero, X.final⟩

end

end

public section

open UpperHalfPlane
open scoped MatrixGroups Topology

/-- Every meromorphic modular function of controlled cusp growth is locally a quotient of
modular forms of a common weight, with nonzero denominator. -/
theorem ModularCurve.exists_modularForm_eventuallyEq_div_of_meromorphic_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℍ → ℂ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im)) :
    ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧
      ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) :=
  solution Γ F hmer hinv hcusp

end
