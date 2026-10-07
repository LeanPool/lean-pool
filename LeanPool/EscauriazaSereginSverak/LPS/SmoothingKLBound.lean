/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLEstimate
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLBoundFlux

/-!
# The time derivative of a strong solution is bounded in `L²` after positive time

`prop:lps-smoothing`: the Kiselev–Ladyzhenskaya argument. For `h > 0` the energy
`E_h(t) = ∫ |v_h(x, t)|² dx` of the time-difference quotient `v_h = (u(·, · + h) - u)/h` of a
strong solution satisfies `E_h' ≤ -∫ |∇v_h|² + κ_h E_h` with
`κ_h(t) = 6K (M(t) + M(t + h))`, where `M(t)` is the squared `H²` norm of `u(·, t)` and `K`
the constant of the embedding `H² ⊂ L^∞`. The mean of `E_h` over `[t₀, t₀ + δ]` is controlled
by the `L²` norm of `∂ₜu`, so Grönwall's inequality bounds `E_h` on `[t₀ + δ, T - h]` uniformly
in `h`; letting `h → 0` bounds `∫ |∂ₜu(x, t)|² dx` for almost every `t ∈ (t₀ + δ, T)`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The slice integrals of a function integrable on a slab are integrable in time. -/
private theorem lps_slab_slice_integral_integrable {a b : ℝ} {F : ParabolicPoint → ℝ}
    (hF : Integrable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    Integrable (fun t => ∫ x : Vec3, F (x, t)) (volume.restrict (Ioo a b)) := by
  have h : Integrable (fun z : Vec3 × ℝ => F z)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [← lps_measure_slab_eq_prod]
    exact hF
  exact h.integral_prod_right

/-- The components of the difference quotient of the gradient are square integrable on the
slab over `(t₀, T - h)`. -/
private theorem lps_diffQuotient_grad_memLp {t₀ T h : ℝ} (hh : 0 < h)
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (i j : Fin 3) :
    MemLp (fun z : ParabolicPoint =>
      (1 / h) * (Du ((z.1, z.2 + h) : ParabolicPoint) i j - Du z i j)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) := by
  have h1 := ((LPS.lps_timeDifference_memLp hh hDu).eval i).eval j
  have e : (fun z : ParabolicPoint =>
      (1 / h) * (Du ((z.1, z.2 + h) : ParabolicPoint) i j - Du z i j)) =
      fun z : ParabolicPoint => ((1 / h) • (Du ((z.1, z.2 + h) : ParabolicPoint) - Du z)) i j := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [e]
  exact h1

/-- The differential inequality for the energy of the time-difference quotients: at almost every
time `τ` of `(t₀, T - h)`, `-2 ∫ |∇v|² + 2 ∫ H : ∇v ≤ -∫ |∇v|² + 6K (M(τ) + M(τ + h)) ∫ |v|²`,
given the pointwise bound `uᵢ(x, t)² ≤ K M(t)` (`prop:lps-smoothing`). -/
theorem lps_kl_energy_inequality {t₀ T h K : ℝ} {M : ℝ → ℝ} (hh : 0 < h)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hK : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
      (u (x, t) i) ^ 2 ≤ K * M t) :
    ∀ᵐ τ ∂(volume.restrict (Ioo t₀ (T - h))),
      -2 * (∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2) +
          2 * (∫ x : Vec3, ∑ i, ∑ j,
            ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) *
              ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j))) ≤
        -(∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2) +
          6 * K * (M τ + M (τ + h)) *
            ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2 := by
  have hDall : ∀ᵐ τ ∂(volume.restrict (Ioo t₀ (T - h))), ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => (1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) 2 volume := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact lps_ae_slice_memLp_of_slab (lps_diffQuotient_grad_memLp hh hDu i j)
  filter_upwards [lps_flux_slice_bound hh hslice hK, hDall] with τ hτ hDτ
  have hDD : Integrable (fun x : Vec3 =>
      ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hDτ i j).integrable_sq
  have hHH : Integrable (fun x : Vec3 => ∑ i, ∑ j,
      ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hτ.1 i j).integrable_sq
  have hHD : Integrable (fun x : Vec3 => ∑ i, ∑ j,
      ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) *
        ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j))) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hτ.1 i j).integrable_mul (hDτ i j)
  have hpt : ∀ a b : Fin 3 → Fin 3 → ℝ,
      2 * ∑ i, ∑ j, a i j * b i j ≤ ∑ i, ∑ j, b i j ^ 2 + ∑ i, ∑ j, a i j ^ 2 := by
    intro a b
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      nlinarith only [sq_nonneg (a i j - b i j)]
  have hcross : 2 * (∫ x : Vec3, ∑ i, ∑ j,
      ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) *
        ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j))) ≤
      (∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2) +
        ∫ x : Vec3, ∑ i, ∑ j,
          ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2 := by
    rw [← integral_const_mul, ← integral_add hDD hHH]
    refine integral_mono (hHD.const_mul 2) (hDD.add hHH) ?_
    intro x
    exact hpt (fun i j =>
      (1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j))
      (fun i j => (1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j))
  linarith only [hcross, hτ.2]

/-- The dissipation `∫ |∇v|²` and the flux pairing `∫ H : ∇v` of the time-difference quotient
are integrable in time on `(t₀, T - h)` (`prop:lps-smoothing`). -/
theorem lps_kl_dissipation_integrable {t₀ T h : ℝ} (hh : 0 < h)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hH : ∀ i j, MemLp (fun z : ParabolicPoint => (1 / h) *
      (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j -
        u z i * u z j)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h))))) :
    Integrable (fun τ =>
        ∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2)
        (volume.restrict (Ioo t₀ (T - h))) ∧
      Integrable (fun τ => ∫ x : Vec3, ∑ i, ∑ j,
          ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) *
            ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)))
        (volume.restrict (Ioo t₀ (T - h))) := by
  have hD := lps_diffQuotient_grad_memLp hh hDu
  exact ⟨lps_slab_slice_integral_integrable (F := fun z => ∑ i, ∑ j,
      ((1 / h) * (Du ((z.1, z.2 + h) : ParabolicPoint) i j - Du z i j)) ^ 2)
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hD i j).integrable_sq),
    lps_slab_slice_integral_integrable (F := fun z => ∑ i, ∑ j,
      ((1 / h) * (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j -
        u z i * u z j)) * ((1 / h) * (Du ((z.1, z.2 + h) : ParabolicPoint) i j - Du z i j)))
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hH i j).integrable_mul (hD i j))⟩

/-- The uniform bound of the energy of the time-difference quotients after the initial layer
(`prop:lps-smoothing`): if `0 < h`, `t₀ + δ ≤ T - h` and `uᵢ(x, t)² ≤ K M(t)` almost everywhere
with `M ≥ 0` integrable, then `∫ |v_h(x, t)|² dx ≤ (Θ/δ) e^Λ` for every `t ∈ [t₀ + δ, T - h]`,
where `Θ = ∫ₜ₀ᵀ ∫ |∂ₜu|²` and `Λ = 12K ∫ₜ₀ᵀ M` do not depend on `h`. -/
theorem lps_kl_diffQuotient_energy_le {t₀ T h δ K : ℝ} {M : ℝ → ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hδh : t₀ + δ ≤ T - h)
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
      ∑ i, Du z i i = 0)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    (hK0 : 0 ≤ K) (hM0 : ∀ t, 0 ≤ M t) (hM : Integrable M (volume.restrict (Ioo t₀ T)))
    (hK : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
      (u (x, t) i) ^ 2 ≤ K * M t) :
    ∀ t ∈ Icc (t₀ + δ) (T - h),
      ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, t + h) i - u (x, t) i)) ^ 2 ≤
        (∫ σ in t₀..T, ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, σ) i) ^ 2) / δ *
          Real.exp (12 * K * ∫ σ in t₀..T, M σ) := by
  have hhT : h < T - t₀ := by linarith only [hδh, hδ]
  have hT : t₀ < T := by linarith only [hhT, hh]
  have hcd : t₀ ≤ T - h := by linarith only [hδh, hδ]
  have hH := lps_flux_memLp hh hhT hu hslice hcont hK0 hM0 hM hK
  have hid := lps_kl_energy_identity hh hhT hderiv hu hDu hD2u hDtu hp heq hdiv hslice hcont hH
  have hEc := lps_diffQuotient_energy_continuousOn hh hslice hcont
  obtain ⟨hDdI, hCI⟩ := lps_kl_dissipation_integrable hh hDu hH
  have hDdII := (intervalIntegrable_iff_integrableOn_Ioo_of_le hcd).2 hDdI
  have hCII := (intervalIntegrable_iff_integrableOn_Ioo_of_le hcd).2 hCI
  have hMI : IntervalIntegrable M volume t₀ T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2 hM
  have hM1 : IntervalIntegrable M volume t₀ (T - h) := hMI.mono_set (by
    rw [uIcc_of_le hcd, uIcc_of_le hT.le]
    exact Icc_subset_Icc le_rfl (by linarith only [hh]))
  have hM2' : IntervalIntegrable M volume (t₀ + h) T := hMI.mono_set (by
    rw [uIcc_of_le (by linarith only [hhT]), uIcc_of_le hT.le]
    exact Icc_subset_Icc (by linarith only [hh]) le_rfl)
  have hM2 : IntervalIntegrable (fun τ => M (τ + h)) volume t₀ (T - h) := by
    have := hM2'.comp_add_right h
    rwa [add_sub_cancel_right] at this
  have hκI : IntervalIntegrable (fun τ => 6 * K * (M τ + M (τ + h))) volume t₀ (T - h) :=
    (hM1.add hM2).const_mul (6 * K)
  have htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z :=
    fun i φ hφ => (hderiv.2.2.2.2 φ hφ).2.2 i
  have hΘ := lps_initial_layer_bound hT hδ hh (by linarith only [hδh]) hu hDtu htime hslice hcont
    ((hEc.mono (Icc_subset_Icc le_rfl hδh)).intervalIntegrable_of_Icc (by linarith only [hδ]))
  have hΛ : ∫ τ in t₀..(T - h), 6 * K * (M τ + M (τ + h)) ≤ 12 * K * ∫ σ in t₀..T, M σ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hM1 hM2,
      intervalIntegral.integral_comp_add_right (f := M) h, sub_add_cancel]
    have h1 : ∫ τ in t₀..(T - h), M τ ≤ ∫ σ in t₀..T, M σ :=
      intervalIntegral.integral_mono_interval le_rfl hcd (by linarith only [hh])
        (ae_of_all _ fun τ => hM0 τ) hMI
    have h2 : ∫ τ in (t₀ + h)..T, M τ ≤ ∫ σ in t₀..T, M σ :=
      intervalIntegral.integral_mono_interval (by linarith only [hh]) (by linarith only [hhT])
        le_rfl (ae_of_all _ fun τ => hM0 τ) hMI
    have h6 : 0 ≤ 6 * K := by positivity
    linarith only [mul_le_mul_of_nonneg_left (add_le_add h1 h2) h6]
  have hineq := lps_kl_energy_inequality hh hDu hslice hK
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc, ae_restrict_iff' measurableSet_Icc] at hineq
  obtain ⟨-, -, -, hbd, -⟩ := LPS.lps_energy_uniform_bound
    (E := fun t => ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, t + h) i - u (x, t) i)) ^ 2)
    (g := fun τ =>
      -2 * (∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2) +
        2 * (∫ x : Vec3, ∑ i, ∑ j,
          ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) *
            ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j))))
    (Dd := fun τ =>
      ∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2)
    (κ := fun τ => 6 * K * (M τ + M (τ + h)))
    hδ hδh hEc (fun r _ => integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
    ((hDdII.const_mul (-2)).add (hCII.const_mul 2)) hDdII hκI
    (fun r _ => integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun r _ => by
      have := hM0 r
      have := hM0 (r + h)
      positivity)
    (fun s hs t ht hst => hid s t hs.1 hst ht.2) hineq hΘ hΛ
  exact hbd

/-- The time derivative of a strong solution is bounded in `L²` at almost every time after
`t₀ + δ` (`prop:lps-smoothing`): the uniform bound of the time-difference quotients passes to
the limit `h → 0`. -/
theorem lps_dtu_slice_bound {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hT : t₀ < T)
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
      ∑ i, Du z i i = 0)
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) T)), ∀ i : Fin 3,
      ∫ x : Vec3, (Dtu (x, t) i) ^ 2 ≤ B := by
  obtain ⟨K, hK0, hsup⟩ := lps_ae_slice_sup_bound_strong
  have hK := hsup hderiv hu hDu hD2u
  have hM := lps_sliceH2_integrable hderiv hu hDu hD2u
  have hM0 := lpsSliceH2_nonneg u Du D2u
  have htime : ∀ i : Fin 3,
      ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T),
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), u z i * timePartial φ z =
          -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T), Dtu z i * φ z :=
    fun i φ hφ => (hderiv.2.2.2.2 φ hφ).2.2 i
  have hΘ0 : 0 ≤ ∫ σ in t₀..T, ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, σ) i) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le fun σ _ =>
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ (∫ σ in t₀..T, ∫ x : Vec3, ∑ i : Fin 3, (Dtu (x, σ) i) ^ 2) / δ *
      Real.exp (12 * K * ∫ σ in t₀..T, lpsSliceH2 u Du D2u σ) :=
    mul_nonneg (div_nonneg hΘ0 hδ.le) (Real.exp_pos _).le
  refine ⟨_, hB0, lps_dtu_slice_bound_of_difference_bound hT (by linarith only [hδ]) hu hDtu
    htime hslice hcont hB0 (h₀ := (T - t₀ - δ) / 2) (by linarith only [hδT]) ?_⟩
  intro h hh t ht i
  have hδh : t₀ + δ ≤ T - h := by linarith only [hh.2, hδT]
  have hE := lps_kl_diffQuotient_energy_le hh.1 hδ hδh hderiv hu hDu hD2u hDtu hp heq hdiv
    hslice hcont hK0 hM0 hM hK t ht
  have htI : t ∈ Icc t₀ T := ⟨by linarith only [ht.1, hδ], by linarith only [ht.2, hh.1]⟩
  have ht1 : t + h ∈ Icc t₀ T := ⟨by linarith only [ht.1, hδ, hh.1], by linarith only [ht.2]⟩
  have hv : ∀ k : Fin 3,
      MemLp (fun x : Vec3 => (1 / h) * (u (x, t + h) k - u (x, t) k)) 2 volume :=
    fun k => (((hslice (t + h) ht1).eval k).sub ((hslice t htI).eval k)).const_mul (1 / h)
  refine le_trans (integral_mono (hv i).integrable_sq
    (integrable_finsetSum _ fun k _ => (hv k).integrable_sq) fun x => ?_) hE
  exact Finset.single_le_sum (f := fun k : Fin 3 => ((1 / h) * (u (x, t + h) k - u (x, t) k)) ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)

end ESS
