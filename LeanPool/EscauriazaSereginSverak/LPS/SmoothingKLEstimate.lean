/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEnergyIdentity
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingShift
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLSup
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLTheta
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLReal

/-!
# Uniform bound for the time-difference quotients of a strong solution

`prop:lps-smoothing`: the Kiselev–Ladyzhenskaya energy argument. The time-difference quotient of a
strong solution solves a linear Stokes-type system whose flux is bounded by `‖u‖_∞ |v|`; its energy
obeys a Grönwall inequality with a coefficient integrable in time, uniformly in the step.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The energy identity for the time-difference quotient of a strong solution
(`prop:lps-smoothing`), in scalar form. -/
theorem lps_kl_energy_identity {t₀ T h : ℝ} (hh : 0 < h) (hhT : h < T - t₀)
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
    (hH : ∀ i j, MemLp (fun z : ParabolicPoint => (1 / h) *
      (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j -
        u z i * u z j)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h))))) :
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ T - h →
      (∫ x : Vec3, ∑ i, ((1 / h) * (u (x, t + h) i - u (x, t) i)) ^ 2) -
          (∫ x : Vec3, ∑ i, ((1 / h) * (u (x, s + h) i - u (x, s) i)) ^ 2) =
        ∫ τ in s..t,
          (-2 * (∫ x : Vec3, ∑ i, ∑ j, ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)) ^ 2) +
            2 * (∫ x : Vec3, ∑ i, ∑ j,
              ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) *
                ((1 / h) * (Du (x, τ + h) i j - Du (x, τ) i j)))) := by
  obtain ⟨hd, ⟨hv, hDv, hD2v, hDtv, hq⟩, heqv, hdivv, -⟩ :=
    ESS.LPS.lps_time_difference_quotient hh hderiv hu hDu hD2u hDtu hp heq hdiv
  have hcd : t₀ < T - h := by linarith only [hhT]
  have hslice' : ∀ t ∈ Icc t₀ (T - h), MemLp (fun x : Vec3 =>
      ((1 / h) • (u ((x, t + h) : ParabolicPoint) - u ((x, t) : ParabolicPoint)) : Vec3)) 2
        volume := by
    intro t ht
    have h1 := hslice (t + h) ⟨by linarith only [ht.1, hh], by linarith only [ht.2]⟩
    have h2 := hslice t ⟨ht.1, by linarith only [ht.2, hh]⟩
    exact (h1.sub h2).const_smul (1 / h)
  have hcont' : ∀ t ∈ Icc t₀ (T - h), Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 =>
        ((1 / h) • (u ((x, s + h) : ParabolicPoint) - u ((x, s) : ParabolicPoint)) : Vec3) -
        ((1 / h) • (u ((x, t + h) : ParabolicPoint) - u ((x, t) : ParabolicPoint)) : Vec3)) 2
          volume)
      (𝓝[Icc t₀ (T - h)] t) (𝓝 0) := by
    intro t ht
    have htT : t ∈ Icc t₀ T := ⟨ht.1, by linarith only [ht.2, hh]⟩
    have htT' : t + h ∈ Icc t₀ T := ⟨by linarith only [ht.1, hh], by linarith only [ht.2]⟩
    have hmap1 : Tendsto (fun s : ℝ => s) (𝓝[Icc t₀ (T - h)] t) (𝓝[Icc t₀ T] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.mono_left le_rfl,
        by filter_upwards [self_mem_nhdsWithin] with s hs
           exact ⟨hs.1, by linarith only [hs.2, hh]⟩⟩
    have hmap2 : Tendsto (fun s : ℝ => s + h) (𝓝[Icc t₀ (T - h)] t) (𝓝[Icc t₀ T] (t + h)) :=
      tendsto_nhdsWithin_iff.mpr ⟨((continuous_id.add continuous_const).tendsto t).mono_left
        nhdsWithin_le_nhds, by
          filter_upwards [self_mem_nhdsWithin] with s hs
          exact ⟨by linarith only [hs.1, hh], by linarith only [hs.2]⟩⟩
    have hA := (hcont t htT).comp hmap1
    have hB := (hcont (t + h) htT').comp hmap2
    have hsum : Tendsto (fun s : ℝ => ‖(1 / h : ℝ)‖ₑ * (eLpNorm (fun x : Vec3 =>
        u (x, s + h) - u (x, t + h)) 2 volume + eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2
          volume))
        (𝓝[Icc t₀ (T - h)] t) (𝓝 0) := by
      have h0 : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 =>
          u (x, s + h) - u (x, t + h)) 2 volume + eLpNorm (fun x : Vec3 => u (x, s) - u (x, t))
            2 volume)
          (𝓝[Icc t₀ (T - h)] t) (𝓝 (0 + 0)) := hB.add hA
      rw [add_zero] at h0
      have := ENNReal.Tendsto.const_mul h0 (Or.inr (by simp : (‖(1 / h : ℝ)‖ₑ) ≠ ⊤))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun s => bot_le) ?_
    intro s
    have hfun : (fun x : Vec3 =>
        ((1 / h) • (u ((x, s + h) : ParabolicPoint) - u ((x, s) : ParabolicPoint)) : Vec3) -
        ((1 / h) • (u ((x, t + h) : ParabolicPoint) - u ((x, t) : ParabolicPoint)) : Vec3)) =
        (1 / h : ℝ) • ((fun x : Vec3 => u (x, s + h) - u (x, t + h)) -
          (fun x : Vec3 => u (x, s) - u (x, t))) := by
      funext x
      simp only [Pi.smul_apply, Pi.sub_apply]
      rw [← smul_sub]
      congr 1
      abel
    dsimp only
    rw [hfun, eLpNorm_const_smul]
    exact mul_le_mul_right (eLpNorm_sub_le (by norm_num)) _
  have hcontfun : ∀ t ∈ Icc t₀ (T - h), Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 =>
        ((fun z : ParabolicPoint => (1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) (x, s)) -
        ((fun z : ParabolicPoint => (1 / h) • (u ((z.1, z.2 + h) : ParabolicPoint) - u z)) (x,
          t))) 2 volume)
      (𝓝[Icc t₀ (T - h)] t) (𝓝 0) := hcont'
  have hmain := lps_energy_eq_intervalIntegral (H := fun z i j => (1 / h) *
      (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j - u z i * u
        z j))
    hcd hd hv hDv hD2v hDtv hH hq hdivv heqv hslice' hcontfun
  intro s t hs hst ht
  have := hmain s t hs hst ht
  simpa [Pi.smul_apply, smul_eq_mul] using this

end ESS
