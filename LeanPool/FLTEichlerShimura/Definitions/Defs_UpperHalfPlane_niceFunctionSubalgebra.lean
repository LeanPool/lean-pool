/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

/-
Common constructions extracted from Prove2Me proofs by Claude (2026-09-05).
The primary source is node 5991adb3-f9e2-56b1-a149-d155a61b3080, submission
2875a369-3dff-5b65-afe5-d5211ce2c4c6; proofs include local simplifications.
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_LaurentCoeff
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_X0
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_JqCoeff

import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_tendsto_atImInfty_of_hasSum_qParam
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularForm_levelOne_weight_four_qCoeff_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularForm_levelOne_weight_six_qCoeff_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant

/-!
# Subalgebras of nice functions on the upper half-plane

`UpperHalfPlane.NiceFunction.niceSubalgebra` consists of period-one holomorphic functions
bounded at infinity. Their power-series and Laurent-series q-expansions are algebra maps,
and the latter is injective. The library also provides evaluation on the complex plane,
the elements defined by `E₄`, `E₆` and `discriminant`, their q-expansion identities, and
an analytic-order comparison for polynomial relations.

`UpperHalfPlane.NiceAtInfty` is the weaker condition of analyticity of the q-coordinate
germ at zero. It defines `UpperHalfPlane.niceAtInftySubalgebra`; no global holomorphy
or periodicity is required. The stronger `NiceFunction.Nice` implies `NiceAtInfty`.
-/

open UpperHalfPlane ModularCurve
open scoped MatrixGroups ModularForm Manifold

noncomputable section

public section

namespace UpperHalfPlane.NiceFunction

@[expose] def Nice (f : ℍ → ℂ) : Prop :=
  Function.Periodic (f ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ IsBoundedAtImInfty f

theorem Nice.mul {f g : ℍ → ℂ} (hf : Nice f) (hg : Nice g) : Nice (f * g) :=
  ⟨by simpa [Function.comp_def] using hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.mul hg.2.2⟩

theorem Nice.add {f g : ℍ → ℂ} (hf : Nice f) (hg : Nice g) : Nice (f + g) :=
  ⟨by simpa [Function.comp_def] using hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.add hg.2.2⟩

theorem Nice.const (c : ℂ) : Nice (fun _ => c) :=
  ⟨fun _ => rfl, mdifferentiable_const, Filter.const_boundedAtFilter _ _⟩

@[expose] def niceSubalgebra : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | Nice f}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' c := Nice.const c

local notation "𝒩" => niceSubalgebra

theorem an (f : 𝒩) : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos f.2.1 f.2.2.1 f.2.2.2

@[expose] def qexpHom : 𝒩 →ₐ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (f : ℍ → ℂ)
  map_one' := UpperHalfPlane.qExpansion_one 1
  map_mul' f g := UpperHalfPlane.qExpansion_mul (an f) (an g)
  map_zero' := UpperHalfPlane.qExpansion_zero 1
  map_add' f g := UpperHalfPlane.qExpansion_add (an f) (an g)
  commutes' c := by
    have h1 : ((algebraMap ℂ (ℍ → ℂ) c : ℍ → ℂ)) = c • (1 : ℍ → ℂ) := by
      funext z; simp
    have a1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := an (1 : 𝒩)
    change qExpansion 1 (algebraMap ℂ (ℍ → ℂ) c) = _
    rw [h1, UpperHalfPlane.qExpansion_smul a1 c, UpperHalfPlane.qExpansion_one,
      Algebra.algebraMap_eq_smul_one]

theorem qexpHom_apply (f : 𝒩) : qexpHom f = qExpansion 1 (f : ℍ → ℂ) := rfl

@[expose] def ψ : 𝒩 →ₐ[ℂ] LaurentSeries ℂ :=
  { (HahnSeries.ofPowerSeries ℤ ℂ).comp qexpHom.toRingHom with
    commutes' := fun c => by
      change HahnSeries.ofPowerSeries ℤ ℂ (qexpHom (algebraMap ℂ 𝒩 c)) = _
      rw [qexpHom.commutes, HahnSeries.algebraMap_apply'] }

theorem ψ_apply (f : 𝒩) : ψ f = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (f : ℍ → ℂ)) := rfl

theorem ψ_injective : Function.Injective ψ := by
  intro f g hfg
  rw [ψ_apply, ψ_apply] at hfg
  have h := HahnSeries.ofPowerSeries_injective hfg
  have h' : qExpansion 1 ((f : ℍ → ℂ) - (g : ℍ → ℂ)) = 0 := by
    rw [UpperHalfPlane.qExpansion_sub (an f) (an g), h, sub_self]
  have hn : Nice ((f : ℍ → ℂ) - (g : ℍ → ℂ)) := (f - g).2
  have h0 := (UpperHalfPlane.qExpansion_eq_zero_iff one_pos hn.1 hn.2.1 hn.2.2).mp h'
  grind

theorem ψ_eq_zero_iff (f : 𝒩) : ψ f = 0 ↔ f = 0 :=
  ⟨fun h => ψ_injective (by grind), by grind⟩

@[expose] def toC : 𝒩 →ₐ[ℂ] (ℂ → ℂ) where
  toFun f := (f : ℍ → ℂ) ∘ ofComplex
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem toC_apply (f : 𝒩) : toC f = (f : ℍ → ℂ) ∘ ofComplex := rfl

theorem analyticAt_toC (f : 𝒩) (τ : ℍ) : AnalyticAt ℂ (toC f) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.2.2.1
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

theorem nice_of_modularForm {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : Nice (f : ℍ → ℂ) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  refine ⟨?_, ModularFormClass.holo f, ModularFormClass.bdd_at_infty f⟩
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex (h := 1) f h1

@[expose] def ofMF {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : 𝒩 :=
  ⟨f, nice_of_modularForm f h1⟩

@[scoped simp] theorem coe_ofMF {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) :
    ((ofMF f h1 : 𝒩) : ℍ → ℂ) = f := rfl

@[expose] def 𝔞 : 𝒩 := ofMF ModularForm.E₄ one_mem_strictPeriods_SL

@[expose] def 𝔟 : 𝒩 := ofMF ModularForm.E₆ one_mem_strictPeriods_SL

@[expose] def 𝔡 : 𝒩 := ofMF CuspForm.discriminant one_mem_strictPeriods_SL

theorem ψ𝔞 : ψ 𝔞 = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) := rfl
theorem ψ𝔟 : ψ 𝔟 = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) := rfl
theorem ψ𝔡 : ψ 𝔡 = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant) := rfl
theorem toC𝔡_apply (τ : ℍ) : toC 𝔡 (τ : ℂ) = ModularForm.discriminant τ := by
  change ModularForm.discriminant (ofComplex (τ : ℂ)) = _
  rw [ofComplex_apply]

theorem coeff_one_mul (φ χ : PowerSeries ℂ) :
    PowerSeries.coeff 1 (φ * χ) = PowerSeries.coeff 0 φ * PowerSeries.coeff 1 χ +
      PowerSeries.coeff 1 φ * PowerSeries.coeff 0 χ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_zero_mul' (φ χ : PowerSeries ℂ) :
    PowerSeries.coeff 0 (φ * χ) = PowerSeries.coeff 0 φ * PowerSeries.coeff 0 χ := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]

theorem qA0 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
theorem qB0 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨3, rfl⟩
theorem qA1 : PowerSeries.coeff 1 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 240 := by
  have h := ModularForm.levelOne_weight_four_qCoeff_one ModularForm.E₄
  simp only [ModularFormClass.qCoeff] at h
  rw [h, qA0, mul_one]
theorem qB1 : PowerSeries.coeff 1 (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) = -504 := by
  have h := ModularForm.levelOne_weight_six_qCoeff_one ModularForm.E₆
  simp only [ModularFormClass.qCoeff] at h
  rw [h, qB0, mul_one]
theorem qD1 : PowerSeries.coeff 1 (qExpansion 1 ModularForm.discriminant) = 1 := by
  rw [ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, PowerSeries.coeff_map,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ModularCurve.constantCoeff_dedekindEtaUnit, map_one]

theorem A_cube_sub_B_sq : ψ 𝔞 ^ 3 - ψ 𝔟 ^ 2 = 1728 * ψ 𝔡 := by
  let T : ModularForm 𝒮ℒ 12 := ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)
  let U : ModularForm 𝒮ℒ 12 := ModularForm.E₆.mul ModularForm.E₆
  let Z : ModularForm 𝒮ℒ 12 := T - U
  have hZ : (Z : ℍ → ℂ) = ((𝔞 * (𝔞 * 𝔞) - 𝔟 * 𝔟 : 𝒩) : ℍ → ℂ) := by
    funext z
    change (T : ℍ → ℂ) z - (U : ℍ → ℂ) z = _
    rfl
  have hZq : qExpansion 1 (Z : ℍ → ℂ) =
      qExpansion 1 ⇑ModularForm.E₄ * (qExpansion 1 ⇑ModularForm.E₄ * qExpansion 1 ⇑ModularForm.E₄) -
        qExpansion 1 ⇑ModularForm.E₆ * qExpansion 1 ⇑ModularForm.E₆ := by
    rw [hZ, ← qexpHom_apply, map_sub, map_mul, map_mul, map_mul]
    rfl
  have h0 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 0 = 0 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_zero_mul', qA0, qB0]
    norm_num
  have h1 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 1 = 1728 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_one_mul, coeff_zero_mul', qA0, qA1, qB0,
      qB1]
    norm_num
  have hW := ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0
  have hZΔ :
      qExpansion 1 (Z : ℍ → ℂ) = PowerSeries.C 1728 * qExpansion 1 ModularForm.discriminant := by
    ext n
    have := hW n
    simp only [ModularFormClass.qCoeff] at this h1
    rw [PowerSeries.coeff_C_mul, this, h1]
  have hL : ψ (𝔞 * (𝔞 * 𝔞) - 𝔟 * 𝔟) = 1728 * ψ 𝔡 := by
    rw [ψ_apply, ← hZ, hZΔ, map_mul, HahnSeries.ofPowerSeries_C, map_ofNat, ψ𝔡]
  grind

theorem ψ𝔡_ne_zero : ψ 𝔡 ≠ 0 := by
  intro h
  have h0 : (𝔡 : 𝒩) = 0 := (ψ_eq_zero_iff _).mp h
  have : ModularForm.discriminant UpperHalfPlane.I = 0 := by
    have := congrArg (fun f : 𝒩 => (f : ℍ → ℂ) UpperHalfPlane.I) h0
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at this
    exact this
  exact ModularForm.discriminant_ne_zero _ this

theorem coeffEmb_jq : coeffEmb ℂ jq = jqModC ℂ := by
  exact map_jqModC _

theorem J_mul_D : coeffEmb ℂ jq * ψ 𝔡 = ψ 𝔞 ^ 3 := by
  rw [coeffEmb_jq, ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ← ψ𝔞, ← ψ𝔡,
    div_mul_cancel₀ _ ψ𝔡_ne_zero]

theorem J_sub_mul_D : (coeffEmb ℂ jq - algebraMap ℂ (LaurentSeries ℂ) 1728) * ψ 𝔡 = ψ 𝔟 ^ 2 := by
  rw [map_ofNat, sub_mul, J_mul_D]
  linear_combination A_cube_sub_B_sq

theorem le_analyticOrderAt_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ) (b : ℕ∞)
    (h : ∀ i ∈ s, b ≤ analyticOrderAt (F i) z) : b ≤ analyticOrderAt (∑ i ∈ s, F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, analyticOrderAt_eq_top.mpr (by simp)]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (by grind) le_analyticOrderAt_add

theorem order_le_of_identity {p q d₁ d : ℂ → ℂ} {n : ℕ} {C : ℕ → ℂ → ℂ} {z : ℂ}
    (hp : AnalyticAt ℂ p z) (hq : AnalyticAt ℂ q z) (hd₁ : AnalyticAt ℂ d₁ z)
    (hd : AnalyticAt ℂ d z)
    (hC : ∀ i ∈ Finset.range n, AnalyticAt ℂ (C i) z) (hd₁0 : d₁ z ≠ 0) (hd0 : d z ≠ 0)
    (hid : p ^ (6 * n) * d₁ + ∑ i ∈ Finset.range n, C i * (p ^ (6 * i) * (q ^ 6 * d) ^ (n - i)) =
      0) :
    analyticOrderAt q z ≤ analyticOrderAt p z := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = analyticOrderAt p z :=
    ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hd_ord : analyticOrderAt d z = 0 := hd.analyticOrderAt_eq_zero.mpr hd0
  have hd₁_ord : analyticOrderAt d₁ z = 0 := hd₁.analyticOrderAt_eq_zero.mpr hd₁0
  have hL : analyticOrderAt (p ^ (6 * n) * d₁) z = ((6 * n * k : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_mul (hp.pow _) hd₁, analyticOrderAt_pow hp, ← hk, hd₁_ord]
    grind
  have hq_ord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt q z := by
    rw [← hk] at hlt
    exact Order.add_one_le_of_lt hlt
  have hR : ∀ i ∈ Finset.range n, ((6 * n * k + 6 : ℕ) : ℕ∞) ≤
      analyticOrderAt (C i * (p ^ (6 * i) * (q ^ 6 * d) ^ (n - i))) z := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hqd : AnalyticAt ℂ (q ^ 6 * d) z := (hq.pow _).mul hd
    rw [analyticOrderAt_mul (hC i hi) ((hp.pow _).mul (hqd.pow _)),
      analyticOrderAt_mul (hp.pow _) (hqd.pow _), analyticOrderAt_pow hp, analyticOrderAt_pow hqd,
      analyticOrderAt_mul (hq.pow _) hd, analyticOrderAt_pow hq, hd_ord, ← hk, add_zero]
    have h1 : ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) ≤ (n - i) • (6 • analyticOrderAt q z) := by
      have : (n - i) • (6 • (((k + 1 : ℕ)) : ℕ∞)) ≤ (n - i) • (6 • analyticOrderAt q z) :=
        nsmul_le_nsmul_right (nsmul_le_nsmul_right hq_ord 6) (n - i)
      refine (le_of_eq ?_).trans this
      grind
    have h2 : ((6 * n * k + 6 : ℕ) : ℕ∞)
        ≤ ((6 * i) • (k : ℕ∞)) + ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) := by
      have e : ((6 * i) • (k : ℕ∞)) + ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) =
          ((6 * i * k + 6 * (n - i) * (k + 1) : ℕ) : ℕ∞) := by
        grind
      rw [e]
      exact_mod_cast (show 6 * n * k + 6 ≤ 6 * i * k + 6 * (n - i) * (k + 1) by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hin
        rw [show i + j + 1 - i = j + 1 by omega]
        nlinarith)
    calc ((6 * n * k + 6 : ℕ) : ℕ∞)
        ≤ (6 * i) • (k : ℕ∞) + ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) := h2
      _ ≤ (6 * i) • (k : ℕ∞) + (n - i) • (6 • analyticOrderAt q z) := add_le_add le_rfl h1
      _ ≤ analyticOrderAt (C i) z + ((6 * i) • (k : ℕ∞) + (n - i) • (6 • analyticOrderAt q z)) :=
          self_le_add_left _ _
  have hsum := le_analyticOrderAt_sum (Finset.range n) _ z _ hR
  have heq : p ^ (6 * n) * d₁ = -(∑ i ∈ Finset.range n, C i * (p ^ (6 * i) * (q ^ 6 * d) ^ (n -
    i))) :=
    eq_neg_of_add_eq_zero_left hid
  have : ((6 * n * k + 6 : ℕ) : ℕ∞) ≤ ((6 * n * k : ℕ) : ℕ∞) := by
    rwa [← hL, heq, analyticOrderAt_neg]
  have := ENat.natCast_le_natCast.mp this
  omega

end UpperHalfPlane.NiceFunction

namespace UpperHalfPlane

/-- Analyticity of the period-one cusp function at the origin, without global conditions
on the original function on the upper half-plane. -/
@[expose] def NiceAtInfty (f : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 f) 0

theorem NiceFunction.Nice.niceAtInfty {f : ℍ → ℂ} (hf : NiceFunction.Nice f) :
    NiceAtInfty f := NiceFunction.an ⟨f, hf⟩

theorem NiceAtInfty.const (c : ℂ) : NiceAtInfty (fun _ : ℍ => c) :=
  (NiceFunction.Nice.const c).niceAtInfty

theorem NiceAtInfty.zero : NiceAtInfty (0 : ℍ → ℂ) := NiceAtInfty.const 0

theorem NiceAtInfty.one : NiceAtInfty (1 : ℍ → ℂ) := NiceAtInfty.const 1

theorem NiceAtInfty.mul {f g : ℍ → ℂ} (hf : NiceAtInfty f) (hg : NiceAtInfty g) :
    NiceAtInfty (f * g) := by
  unfold NiceAtInfty at *
  rw [cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact hf.mul hg

theorem NiceAtInfty.add {f g : ℍ → ℂ} (hf : NiceAtInfty f) (hg : NiceAtInfty g) :
    NiceAtInfty (f + g) := by
  unfold NiceAtInfty at *
  rw [cuspFunction_add hf.continuousAt hg.continuousAt]
  exact hf.add hg

/-- The complex subalgebra of functions whose q-coordinate germs are analytic at zero. -/
@[expose] def niceAtInftySubalgebra : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | NiceAtInfty f}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' c := NiceAtInfty.const c

@[simp] theorem mem_niceAtInftySubalgebra (f : ℍ → ℂ) :
    f ∈ niceAtInftySubalgebra ↔ NiceAtInfty f := Iff.rfl

theorem NiceFunction.niceSubalgebra_le_niceAtInftySubalgebra :
    NiceFunction.niceSubalgebra ≤ niceAtInftySubalgebra := fun _ hf => hf.niceAtInfty

theorem NiceAtInfty.pow {f : ℍ → ℂ} (hf : NiceAtInfty f) : ∀ n : ℕ, NiceAtInfty (f ^ n)
  | 0 => by rw [pow_zero]; exact NiceAtInfty.one
  | n + 1 => by rw [pow_succ]; exact (NiceAtInfty.pow hf n).mul hf

theorem NiceAtInfty.qExpansion_pow {f : ℍ → ℂ} (hf : NiceAtInfty f) :
    ∀ n : ℕ, qExpansion 1 (f ^ n) = qExpansion 1 f ^ n
  | 0 => by rw [pow_zero, pow_zero, qExpansion_one]
  | n + 1 => by
    rw [pow_succ, pow_succ, qExpansion_mul (NiceAtInfty.pow hf n) hf,
      NiceAtInfty.qExpansion_pow hf n]

theorem NiceAtInfty.sum {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, NiceAtInfty (f i)) : NiceAtInfty (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact NiceAtInfty.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem
      hi))

theorem NiceAtInfty.qExpansion_sum {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, NiceAtInfty (f i)) :
    qExpansion 1 (∑ i ∈ s, f i) = ∑ i ∈ s, qExpansion 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExpansion_add (hf a (Finset.mem_insert_self a s))
        (NiceAtInfty.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end UpperHalfPlane
