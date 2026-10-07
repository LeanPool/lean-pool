/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingShiftEquation

/-!
# Time difference quotients of a strong solution

For `h > 0` put `s(x, t) = (x, t + h)` and
`v = (u ∘ s - u) / h`, `Dv = (Du ∘ s - Du) / h`, `D²v = (D²u ∘ s - D²u) / h`,
`∂ₜv = (∂ₜu ∘ s - ∂ₜu) / h`, `q = (p ∘ s - p) / h`,
`Hᵢⱼ = ((uᵢuⱼ) ∘ s - uᵢuⱼ) / h`. On the slab over `(t₀, T - h)` the difference quotient
`v` has the weak derivatives `Dv`, `D²v`, `∂ₜv`, all square integrable, is solenoidal,
and solves the linear equation `∂ₜv - Δv + div H + ∇q = 0` weakly, with
`Hᵢⱼ = vᵢ (uⱼ ∘ s) + uᵢ vⱼ`. This is the difference-quotient step of the
Kiselev–Ladyzhenskaya argument in `prop:lps-smoothing`; no square integrability of `H`
is used.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

/-- A scaled difference of two integration-by-parts identities. -/
private theorem lps_integral_smul_sub_pair {μ : Measure ParabolicPoint} (κ : ℝ)
    {f₁ f₂ g₁ g₂ ψ χ : ParabolicPoint → ℝ}
    (hf₁ : Integrable (fun z => f₁ z * ψ z) μ) (hf₂ : Integrable (fun z => f₂ z * ψ z) μ)
    (hg₁ : Integrable (fun z => g₁ z * χ z) μ) (hg₂ : Integrable (fun z => g₂ z * χ z) μ)
    (e₁ : ∫ z, f₁ z * ψ z ∂μ = -∫ z, g₁ z * χ z ∂μ)
    (e₂ : ∫ z, f₂ z * ψ z ∂μ = -∫ z, g₂ z * χ z ∂μ) :
    ∫ z, κ * (f₁ z - f₂ z) * ψ z ∂μ = -∫ z, κ * (g₁ z - g₂ z) * χ z ∂μ := by
  have hL : ∫ z, κ * (f₁ z - f₂ z) * ψ z ∂μ =
      κ * (∫ z, f₁ z * ψ z ∂μ - ∫ z, f₂ z * ψ z ∂μ) := by
    rw [← integral_sub hf₁ hf₂, ← integral_const_mul]
    congr 1
    funext z
    ring
  have hR : ∫ z, κ * (g₁ z - g₂ z) * χ z ∂μ =
      κ * (∫ z, g₁ z * χ z ∂μ - ∫ z, g₂ z * χ z ∂μ) := by
    rw [← integral_sub hg₁ hg₂, ← integral_const_mul]
    congr 1
    funext z
    ring
  rw [hL, hR, e₁, e₂]
  ring

/-- Space-time weak derivatives are compatible with scaled differences of square
integrable fields (`prop:lps-smoothing`). -/
theorem lps_hasSpaceTimeWeakDerivs_smul_sub {c d : ℝ} (κ : ℝ)
    {w₁ w₂ : ParabolicPoint → Vec3} {Dw₁ Dw₂ : ParabolicPoint → Fin 3 → Vec3}
    {D2w₁ D2w₂ : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw₁ Dtw₂ : ParabolicPoint → Vec3}
    (h₁ : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) w₁ Dw₁ D2w₁ Dtw₁)
    (h₂ : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) w₂ Dw₂ D2w₂ Dtw₂)
    (hw₁ : MemLp w₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hw₂ : MemLp w₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDw₁ : MemLp Dw₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDw₂ : MemLp Dw₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hD2w₁ : MemLp D2w₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hD2w₂ : MemLp D2w₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDtw₁ : MemLp Dtw₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDtw₂ : MemLp Dtw₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)))) :
    HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d)
      (fun z => κ • (w₁ z - w₂ z)) (fun z i => κ • (Dw₁ z i - Dw₂ z i))
      (fun z i j => κ • (D2w₁ z i j - D2w₂ z i j)) (fun z => κ • (Dtw₁ z - Dtw₂ z)) := by
  obtain ⟨-, -, -, -, hid₁⟩ := h₁
  obtain ⟨-, -, -, -, hid₂⟩ := h₂
  refine ⟨lps_locallyIntegrableOn_of_memLp ((hw₁.sub hw₂).const_smul κ),
    lps_locallyIntegrableOn_of_memLp ((hDw₁.sub hDw₂).const_smul κ),
    lps_locallyIntegrableOn_of_memLp ((hD2w₁.sub hD2w₂).const_smul κ),
    lps_locallyIntegrableOn_of_memLp ((hDtw₁.sub hDtw₂).const_smul κ), ?_⟩
  intro φ hφ
  have hφ2 := lps_spaceTimeTest_spatial_memLp_two hφ.1 hφ.2.1 (Ioo c d)
  have hφt : MemLp (fun z => timePartial φ z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))) :=
    (lps_spaceTimeTest_spatial_memLp_two (CKN.contDiff_timePartial hφ.1)
      (CKN.hasCompactSupport_timePartial hφ.2.1) (Ioo c d)).1
  obtain ⟨e₁, e₁', e₁''⟩ := hid₁ φ hφ
  obtain ⟨e₂, e₂', e₂''⟩ := hid₂ φ hφ
  refine ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact lps_integral_smul_sub_pair κ (f₁ := fun z => w₁ z i) (f₂ := fun z => w₂ z i)
      (g₁ := fun z => Dw₁ z i j) (g₂ := fun z => Dw₂ z i j)
      (ψ := fun z => spatialPartial φ j z) (χ := φ)
      ((hw₁.eval i).integrable_mul (hφ2.2 j)) ((hw₂.eval i).integrable_mul (hφ2.2 j))
      (((hDw₁.eval i).eval j).integrable_mul hφ2.1)
      (((hDw₂.eval i).eval j).integrable_mul hφ2.1) (e₁ i j) (e₂ i j)
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact lps_integral_smul_sub_pair κ (f₁ := fun z => Dw₁ z i j) (f₂ := fun z => Dw₂ z i j)
      (g₁ := fun z => D2w₁ z i j k) (g₂ := fun z => D2w₂ z i j k)
      (ψ := fun z => spatialPartial φ k z) (χ := φ)
      (((hDw₁.eval i).eval j).integrable_mul (hφ2.2 k))
      (((hDw₂.eval i).eval j).integrable_mul (hφ2.2 k))
      ((((hD2w₁.eval i).eval j).eval k).integrable_mul hφ2.1)
      ((((hD2w₂.eval i).eval j).eval k).integrable_mul hφ2.1) (e₁' i j k) (e₂' i j k)
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact lps_integral_smul_sub_pair κ (f₁ := fun z => w₁ z i) (f₂ := fun z => w₂ z i)
      (g₁ := fun z => Dtw₁ z i) (g₂ := fun z => Dtw₂ z i)
      (ψ := fun z => timePartial φ z) (χ := φ)
      ((hw₁.eval i).integrable_mul hφt) ((hw₂.eval i).integrable_mul hφt)
      ((hDtw₁.eval i).integrable_mul hφ2.1) ((hDtw₂.eval i).integrable_mul hφ2.1)
      (e₁'' i) (e₂'' i)

/-- The time difference quotient of a strong solution has space-time weak derivatives on
the slab over `(t₀, T - h)`, namely the difference quotients of the weak derivatives
(`prop:lps-smoothing`). -/
theorem lps_timeDifference_hasSpaceTimeWeakDerivs {t₀ T h : ℝ} (hh : 0 < h)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ (T - h))
      (fun z => (1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z))
      (fun z i => (1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i))
      (fun z i j => (1 / h) • (D2u ((z.1, z.2 + h) : ParabolicPoint) i j - D2u z i j))
      (fun z => (1 / h) • (Dtu ((z.1, z.2 + h) : ParabolicPoint) - Dtu z)) := by
  have hac : t₀ ≤ t₀ + h := by linarith only [hh]
  have hdb : T - h + h ≤ T := (sub_add_cancel T h).le
  have hdb' : T - h ≤ T := by linarith only [hh]
  exact lps_hasSpaceTimeWeakDerivs_smul_sub (1 / h)
    (lps_hasSpaceTimeWeakDerivs_forwardShift hac hdb hderiv hu hDu hD2u hDtu)
    (lps_hasSpaceTimeWeakDerivs_slab_mono le_rfl hdb' hderiv)
    (lps_memLp_forwardShift hac hdb hu) (lps_memLp_slab_mono le_rfl hdb' hu)
    (lps_memLp_forwardShift hac hdb hDu) (lps_memLp_slab_mono le_rfl hdb' hDu)
    (lps_memLp_forwardShift hac hdb hD2u) (lps_memLp_slab_mono le_rfl hdb' hD2u)
    (lps_memLp_forwardShift hac hdb hDtu) (lps_memLp_slab_mono le_rfl hdb' hDtu)

/-- The time difference quotient of a square integrable field on the slab over `(t₀, T)`
is square integrable on the slab over `(t₀, T - h)`. -/
theorem lps_timeDifference_memLp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t₀ T h : ℝ} (hh : 0 < h) {f : ParabolicPoint → E}
    (hf : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    MemLp (fun z => (1 / h) • (f ((z.1, z.2 + h) : ParabolicPoint) - f z)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) := by
  have hac : t₀ ≤ t₀ + h := by linarith only [hh]
  have hdb : T - h + h ≤ T := (sub_add_cancel T h).le
  have hdb' : T - h ≤ T := by linarith only [hh]
  exact ((lps_memLp_forwardShift hac hdb hf).sub (lps_memLp_slab_mono le_rfl hdb' hf)).const_smul
    (1 / h)

/-- The time difference quotient of a strong solution solves, on the slab over
`(t₀, T - h)`, the linear equation `∂ₜv - Δv + div H + ∇q = 0` in weak form, with the
difference quotients `H` of `u ⊗ u` and `q` of the pressure (`prop:lps-smoothing`). -/
theorem lps_timeDifference_equation {t₀ T h : ℝ} (hh : 0 < h) {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {Dtu : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
        (∑ i, Dtu z i * φ z i - ∑ i, ∑ j, (u z i * u z j) * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ (T - h)) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)),
        (∑ i, ((1 / h) • (Dtu ((z.1, z.2 + h) : ParabolicPoint) - Dtu z)) i * φ z i
          - ∑ i, ∑ j, ((1 / h) * (u ((z.1, z.2 + h) : ParabolicPoint) i *
              u ((z.1, z.2 + h) : ParabolicPoint) j - u z i * u z j)) *
              spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, ((1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i)) j *
              spatialPartial (fun y => φ y i) j z
          - ((1 / h) * (p ((z.1, z.2 + h) : ParabolicPoint) - p z)) *
              ∑ i, spatialPartial (fun y => φ y i) i z) = 0 := by
  intro φ hφ
  have hac : t₀ ≤ t₀ + h := by linarith only [hh]
  have hdb : T - h + h ≤ T := (sub_add_cancel T h).le
  have hdb' : T - h ≤ T := by linarith only [hh]
  have e₁ := lps_weakEquation_forwardShift (A := Dtu) (F := fun z i j => u z i * u z j)
    (G := Du) (q := p) hac hdb heq φ hφ
  have e₂ := lps_weakEquation_slab_mono (A := Dtu) (F := fun z i j => u z i * u z j)
    (G := Du) (q := p) le_rfl hdb' heq φ hφ
  have hus := lps_memLp_forwardShift hac hdb hu
  have hum := lps_memLp_slab_mono le_rfl hdb' hu
  have hI₁ := lps_weakEquation_integrand_integrable
    (A := fun z => Dtu ((z.1, z.2 + h) : ParabolicPoint))
    (F := fun z i j => u ((z.1, z.2 + h) : ParabolicPoint) i *
      u ((z.1, z.2 + h) : ParabolicPoint) j)
    (G := fun z => Du ((z.1, z.2 + h) : ParabolicPoint))
    (q := fun z => p ((z.1, z.2 + h) : ParabolicPoint))
    (lps_memLp_forwardShift hac hdb hDtu)
    (fun i j => (hus.eval i).integrable_mul (hus.eval j))
    (lps_memLp_forwardShift hac hdb hDu) (lps_memLp_forwardShift hac hdb hp) hφ
  have hI₂ := lps_weakEquation_integrand_integrable (A := Dtu)
    (F := fun z i j => u z i * u z j) (G := Du) (q := p)
    (lps_memLp_slab_mono le_rfl hdb' hDtu)
    (fun i j => (hum.eval i).integrable_mul (hum.eval j))
    (lps_memLp_slab_mono le_rfl hdb' hDu) (lps_memLp_slab_mono le_rfl hdb' hp) hφ
  have hsub := integral_sub hI₁ hI₂
  beta_reduce at hsub e₁ e₂
  rw [e₁, e₂, sub_zero] at hsub
  rw [← mul_zero (1 / h), ← hsub, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- The time difference quotient of a solenoidal field is solenoidal on the slab over
`(t₀, T - h)`. -/
theorem lps_timeDifference_div_free {t₀ T h : ℝ} (hh : 0 < h)
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hdiv : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))),
      ∑ i, Du z i i = 0) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))),
      ∑ i, ((1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i)) i = 0 := by
  have hac : t₀ ≤ t₀ + h := by linarith only [hh]
  have hdb : T - h + h ≤ T := (sub_add_cancel T h).le
  have hdb' : T - h ≤ T := by linarith only [hh]
  filter_upwards [lps_ae_forwardShift hac hdb hdiv, lps_ae_slab_mono le_rfl hdb' hdiv]
    with z h1 h2
  have h1' : ∑ i, Du ((z.1, z.2 + h) : ParabolicPoint) i i = 0 := h1
  have h2' : ∑ i, Du z i i = 0 := h2
  have e : ∑ i, ((1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i)) i =
      (1 / h) * (∑ i, Du ((z.1, z.2 + h) : ParabolicPoint) i i - ∑ i, Du z i i) := by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Fin.sum_univ_three]
    ring
  rw [e, h1', h2', sub_zero, mul_zero]

/-- The difference quotient of `uᵢuⱼ` splits as `vᵢ (uⱼ ∘ s) + uᵢ vⱼ` with `v` the
difference quotient of `u` and `s` the time translation by `h`. -/
theorem lps_timeDifference_flux_eq (h : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (i j : Fin 3) :
    (1 / h) * (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j
        - u z i * u z j) =
      ((1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) i *
          u ((z.1, z.2 + h) : ParabolicPoint) j +
        u z i * ((1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) j := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Time difference quotients of a strong solution (`prop:lps-smoothing`). Let `h > 0`,
`s(x, t) = (x, t + h)`, `v = (u ∘ s - u) / h` and likewise `Dv`, `D²v`, `∂ₜv`, `q` for
`Du`, `D²u`, `∂ₜu`, `p`, and `Hᵢⱼ = ((uᵢuⱼ) ∘ s - uᵢuⱼ) / h`. Given the weak derivatives,
square integrability, the weak equation with the time derivative and solenoidality of `u`
on the slab over `(t₀, T)`, on the slab over `(t₀, T - h)`:
(a) `v` has the weak derivatives `Dv`, `D²v`, `∂ₜv`; (b) `v`, `Dv`, `D²v`, `∂ₜv`, `q` are
square integrable; (c) `∂ₜv - Δv + div H + ∇q = 0` weakly; (d) `v` is solenoidal;
(e) `Hᵢⱼ = vᵢ (uⱼ ∘ s) + uᵢ vⱼ`. -/
theorem lps_time_difference_quotient {t₀ T h : ℝ} (hh : 0 < h)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T),
        (∑ i, Dtu z i * φ z i - ∑ i, ∑ j, (u z i * u z j) * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0)
    (hdiv : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))),
      ∑ i, Du z i i = 0) :
    HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ (T - h))
        (fun z => (1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z))
        (fun z i => (1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i))
        (fun z i j => (1 / h) • (D2u ((z.1, z.2 + h) : ParabolicPoint) i j - D2u z i j))
        (fun z => (1 / h) • (Dtu ((z.1, z.2 + h) : ParabolicPoint) - Dtu z)) ∧
      (MemLp (fun z => (1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) ∧
        MemLp (fun z i => (1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i)) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) ∧
        MemLp (fun z i j => (1 / h) • (D2u ((z.1, z.2 + h) : ParabolicPoint) i j - D2u z i j)) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) ∧
        MemLp (fun z => (1 / h) • (Dtu ((z.1, z.2 + h) : ParabolicPoint) - Dtu z)) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) ∧
        MemLp (fun z => (1 / h) * (p ((z.1, z.2 + h) : ParabolicPoint) - p z)) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h))))) ∧
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo t₀ (T - h)) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)),
          (∑ i, ((1 / h) • (Dtu ((z.1, z.2 + h) : ParabolicPoint) - Dtu z)) i * φ z i
            - ∑ i, ∑ j, ((1 / h) * (u ((z.1, z.2 + h) : ParabolicPoint) i *
                u ((z.1, z.2 + h) : ParabolicPoint) j - u z i * u z j)) *
                spatialPartial (fun y => φ y i) j z
            + ∑ i, ∑ j, ((1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i)) j *
                spatialPartial (fun y => φ y i) j z
            - ((1 / h) * (p ((z.1, z.2 + h) : ParabolicPoint) - p z)) *
                ∑ i, spatialPartial (fun y => φ y i) i z) = 0) ∧
      (∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))),
        ∑ i, ((1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) i - Du z i)) i = 0) ∧
      (∀ (z : ParabolicPoint) (i j : Fin 3),
        (1 / h) * (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j
            - u z i * u z j) =
          ((1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) i *
              u ((z.1, z.2 + h) : ParabolicPoint) j +
            u z i * ((1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) j) :=
  ⟨lps_timeDifference_hasSpaceTimeWeakDerivs hh hderiv hu hDu hD2u hDtu,
    ⟨lps_timeDifference_memLp hh hu, lps_timeDifference_memLp hh hDu,
      lps_timeDifference_memLp hh hD2u, lps_timeDifference_memLp hh hDtu,
      lps_timeDifference_memLp hh hp⟩,
    lps_timeDifference_equation hh hu hDu hDtu hp heq,
    lps_timeDifference_div_free hh hdiv,
    fun z i j => lps_timeDifference_flux_eq h u z i j⟩

end ESS.LPS
