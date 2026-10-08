/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingShift
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest
public import LeanPool.EscauriazaSereginSverak.PartV.PvLocalSolutionLerayHopfCore
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The flux of the time-difference quotients is square integrable

`prop:lps-smoothing`: let `u` be a strong solution, `h > 0`, `v = (u(·, · + h) - u)/h` and
`Hᵢⱼ = ((uᵢuⱼ)(·, · + h) - uᵢuⱼ)/h = vᵢ uⱼ(·, · + h) + uᵢ vⱼ`. If `uᵢ(x, t)² ≤ K M(t)` for almost
every `(x, t)` with `M` integrable in time, then at almost every time
`∑ᵢⱼ Hᵢⱼ² ≤ 6K (M(t) + M(t + h)) |v|²` pointwise, and `H` is square integrable on the slab over
`(t₀, T - h)`, since the energy `∫ |v(x, t)|² dx` is continuous on `[t₀, T - h]`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The flux `vᵢwⱼ + uᵢvⱼ` is bounded by the pointwise bounds of the components of `w` and `u`
(`prop:lps-smoothing`). -/
theorem lps_flux_sum_sq_le {v w u : Fin 3 → ℝ} {A B : ℝ} (hw : ∀ j, w j ^ 2 ≤ A)
    (hu : ∀ j, u j ^ 2 ≤ B) :
    ∑ i, ∑ j, (v i * w j + u i * v j) ^ 2 ≤ 6 * (A + B) * ∑ i, v i ^ 2 := by
  calc ∑ i, ∑ j, (v i * w j + u i * v j) ^ 2
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, (2 * A * v i ^ 2 + 2 * B * v j ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h1 := mul_le_mul_of_nonneg_left (hw j) (sq_nonneg (v i))
        have h2 := mul_le_mul_of_nonneg_left (hu i) (sq_nonneg (v j))
        nlinarith only [sq_nonneg (v i * w j - u i * v j), h1, h2]
    _ = 6 * (A + B) * ∑ i, v i ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring

/-- A property holding at almost every time of `(a, b)` holds at `t + h` for almost every
time `t` of `(a, b - h)`, when `h ≥ 0`. -/
theorem lps_ae_restrict_Ioo_shift {a b h : ℝ} (hh : 0 ≤ h) {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂(volume.restrict (Ioo a b)), P t) :
    ∀ᵐ t ∂(volume.restrict (Ioo a (b - h))), P (t + h) := by
  rw [ae_restrict_iff' measurableSet_Ioo] at hP ⊢
  filter_upwards [(measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae hP]
    with t ht htm
  exact ht ⟨by linarith only [htm.1, hh], by linarith only [htm.2]⟩

/-- The kinetic energy of an `L²`-continuous curve of square-integrable vector fields is
continuous. -/
theorem lps_curve_energy_continuousOn {S : Set ℝ} {f : ℝ → Vec3 → Vec3}
    (hf : ∀ t ∈ S, MemLp (f t) 2 volume)
    (hcont : ∀ t ∈ S,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => f s x - f t x) 2 volume) (𝓝[S] t) (𝓝 0)) :
    ContinuousOn (fun t => ∫ x : Vec3, ∑ i, (f t x i) ^ 2) S := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  let N : ℝ → ℝ := fun s => (eLpNorm (fun x : Vec3 => f s x - f t x) 2 volume).toReal
  have hN : Tendsto N (𝓝[S] t) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun s =>
      3 * (N s * N s) + 2 * (3 * (N s * (eLpNorm (f t) 2 volume).toReal))) (𝓝[S] t) (𝓝 0) := by
    have h := ((hN.mul hN).const_mul 3).add
      (((hN.mul_const (eLpNorm (f t) 2 volume).toReal).const_mul 3).const_mul 2)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdiff : MemLp (fun x : Vec3 => f s x - f t x) 2 volume := (hf s hs).sub (hf t ht)
  have hpairInt (g k : Vec3 → Vec3) (hg : MemLp g 2 volume) (hk : MemLp k 2 volume) :
      Integrable (fun x => ∑ i : Fin 3, g x i * k x i) :=
    integrable_finsetSum _ fun i _ =>
      (memLp_pi_iff.1 hg i).integrable_mul (memLp_pi_iff.1 hk i)
  have hsq (g : Vec3 → Vec3) :
      (fun x => ∑ i : Fin 3, (g x i) ^ 2) = fun x => ∑ i : Fin 3, g x i * g x i := by
    funext x
    simp only [sq]
  have hsplit :
      (∫ x : Vec3, ∑ i : Fin 3, (f s x i) ^ 2) - ∫ x : Vec3, ∑ i : Fin 3, (f t x i) ^ 2 =
        (∫ x : Vec3, ∑ i : Fin 3, (f s x - f t x) i * (f s x - f t x) i) +
          2 * ∫ x : Vec3, ∑ i : Fin 3, (f s x - f t x) i * f t x i := by
    rw [hsq (f s), hsq (f t),
      ← integral_sub (hpairInt _ _ (hf s hs) (hf s hs)) (hpairInt _ _ (hf t ht) (hf t ht)),
      ← integral_const_mul, ← integral_add
        (hpairInt (fun x => f s x - f t x) (fun x => f s x - f t x) hdiff hdiff)
        ((hpairInt (fun x => f s x - f t x) (f t) hdiff (hf t ht)).const_mul 2)]
    congr 1
    funext x
    simp only [Pi.sub_apply, Fin.sum_univ_three]
    ring
  rw [Real.norm_eq_abs, hsplit]
  refine (abs_add_le _ _).trans (add_le_add (pvLH_pair_le hdiff hdiff) ?_)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (pvLH_pair_le hdiff (hf t ht)) (by norm_num)

/-- The time-difference quotients of an `L²`-continuous curve of square-integrable slices form
an `L²`-continuous curve of square-integrable slices on `[t₀, T - h]`. -/
theorem lps_diffQuotient_slice_continuous {t₀ T h : ℝ} (hh : 0 < h) {u : ParabolicPoint → Vec3}
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0)) :
    (∀ t ∈ Icc t₀ (T - h),
      MemLp (fun x : Vec3 => (1 / h) • (u (x, t + h) - u (x, t))) 2 volume) ∧
    ∀ t ∈ Icc t₀ (T - h), Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 =>
        (1 / h) • (u (x, s + h) - u (x, s)) - (1 / h) • (u (x, t + h) - u (x, t))) 2 volume)
      (𝓝[Icc t₀ (T - h)] t) (𝓝 0) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have h1 := hslice (t + h) ⟨by linarith only [ht.1, hh], by linarith only [ht.2]⟩
    have h2 := hslice t ⟨ht.1, by linarith only [ht.2, hh]⟩
    exact (h1.sub h2).const_smul (1 / h)
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
      u (x, s + h) - u (x, t + h)) 2 volume +
        eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume))
      (𝓝[Icc t₀ (T - h)] t) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 =>
        u (x, s + h) - u (x, t + h)) 2 volume +
          eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
        (𝓝[Icc t₀ (T - h)] t) (𝓝 (0 + 0)) := hB.add hA
    rw [add_zero] at h0
    have := ENNReal.Tendsto.const_mul h0 (Or.inr (by simp : (‖(1 / h : ℝ)‖ₑ) ≠ ⊤))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun s => bot_le) ?_
  intro s
  have hfun : (fun x : Vec3 =>
      (1 / h) • (u (x, s + h) - u (x, s)) - (1 / h) • (u (x, t + h) - u (x, t))) =
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

/-- The energy `∫ |v(x, t)|² dx` of the time-difference quotient `v = (u(·, · + h) - u)/h` is
continuous on `[t₀, T - h]` (`prop:lps-smoothing`). -/
theorem lps_diffQuotient_energy_continuousOn {t₀ T h : ℝ} (hh : 0 < h)
    {u : ParabolicPoint → Vec3}
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0)) :
    ContinuousOn (fun t => ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, t + h) i - u (x, t) i)) ^ 2)
      (Icc t₀ (T - h)) := by
  obtain ⟨h1, h2⟩ := lps_diffQuotient_slice_continuous hh hslice hcont
  have := lps_curve_energy_continuousOn
    (f := fun t x => (1 / h) • (u (x, t + h) - u (x, t))) h1 h2
  simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using this

/-- At almost every time of `(t₀, T - h)`, the difference quotient of the convective flux is
square integrable in space and `∫ ∑ᵢⱼ Hᵢⱼ² ≤ 6K (M(t) + M(t + h)) ∫ |v|²`, given the pointwise
bound `uᵢ(x, t)² ≤ K M(t)` (`prop:lps-smoothing`). -/
theorem lps_flux_slice_bound {t₀ T h K : ℝ} {M : ℝ → ℝ} (hh : 0 < h)
    {u : ParabolicPoint → Vec3}
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hK : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
      (u (x, t) i) ^ 2 ≤ K * M t) :
    ∀ᵐ τ ∂(volume.restrict (Ioo t₀ (T - h))),
      (∀ i j : Fin 3, MemLp (fun x : Vec3 =>
        (1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) 2 volume) ∧
      (∫ x : Vec3, ∑ i, ∑ j,
        ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2) ≤
        6 * K * (M τ + M (τ + h)) *
          ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2 := by
  have hK1 : ∀ᵐ τ ∂(volume.restrict (Ioo t₀ (T - h))), ∀ᵐ x ∂(volume : Measure Vec3),
      ∀ i : Fin 3, (u (x, τ) i) ^ 2 ≤ K * M τ :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right (by linarith only [hh])) hK
  have hK2 := lps_ae_restrict_Ioo_shift hh.le hK
  filter_upwards [hK1, hK2, ae_restrict_mem measurableSet_Ioo] with τ h1 h2 hτ
  have h2' : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
      (u (x, τ + h) i) ^ 2 ≤ K * M (τ + h) := h2
  have hτ0 : τ ∈ Icc t₀ T := ⟨hτ.1.le, by linarith only [hτ.2, hh]⟩
  have hτ1 : τ + h ∈ Icc t₀ T := ⟨by linarith only [hτ.1, hh], by linarith only [hτ.2]⟩
  have hw := hslice (τ + h) hτ1
  have hu := hslice τ hτ0
  set κ := 6 * K * (M τ + M (τ + h)) with hκ
  have hv : ∀ i, MemLp (fun x : Vec3 => (1 / h) * (u (x, τ + h) i - u (x, τ) i)) 2 volume :=
    fun i => ((hw.eval i).sub (hu.eval i)).const_mul (1 / h)
  have hvint : Integrable (fun x : Vec3 => ∑ i, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2) :=
    integrable_finsetSum _ fun i _ => (hv i).integrable_sq
  have hpt : ∀ᵐ x ∂(volume : Measure Vec3), ∑ i, ∑ j,
      ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2 ≤
        κ * ∑ i, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2 := by
    filter_upwards [h1, h2'] with x hx1 hx2
    have hb := lps_flux_sum_sq_le (v := fun i => (1 / h) * (u (x, τ + h) i - u (x, τ) i))
      (w := fun j => u (x, τ + h) j) (u := fun j => u (x, τ) j) hx2 hx1
    beta_reduce at hb
    have e : (∑ i, ∑ j,
        ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2) =
        ∑ i, ∑ j, ((1 / h) * (u (x, τ + h) i - u (x, τ) i) * u (x, τ + h) j +
          u (x, τ) i * ((1 / h) * (u (x, τ + h) j - u (x, τ) j))) ^ 2 :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine hb.trans (le_of_eq ?_)
    rw [hκ]
    ring
  have hmeas : ∀ i j, AEStronglyMeasurable (fun x : Vec3 =>
      (1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) volume :=
    fun i j => (((hw.eval i).aestronglyMeasurable.mul (hw.eval j).aestronglyMeasurable).sub
      ((hu.eval i).aestronglyMeasurable.mul (hu.eval j).aestronglyMeasurable)).const_mul (1 / h)
  have hHsq : ∀ i j, Integrable (fun x : Vec3 =>
      ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2) := by
    intro i j
    refine (hvint.const_mul κ).mono' ((hmeas i j).pow 2) ?_
    filter_upwards [hpt] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine le_trans ?_ hx
    refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3,
      ((1 / h) * (u (x, τ + h) i' * u (x, τ + h) j' - u (x, τ) i' * u (x, τ) j')) ^ 2)
      (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin 3 =>
      ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j' - u (x, τ) i * u (x, τ) j')) ^ 2)
      (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
  refine ⟨fun i j => (memLp_two_iff_integrable_sq (hmeas i j)).2 (hHsq i j), ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hHsq i j)
    (hvint.const_mul κ) hpt

/-- The difference quotient of the convective flux is square integrable on the slab over
`(t₀, T - h)`, given the pointwise bound `uᵢ(x, t)² ≤ K M(t)` with `M` integrable in time
(`prop:lps-smoothing`). -/
theorem lps_flux_memLp {t₀ T h K : ℝ} {M : ℝ → ℝ} (hh : 0 < h) (hhT : h < T - t₀)
    {u : ParabolicPoint → Vec3}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hslice : ∀ t ∈ Icc t₀ T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc t₀ T, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (𝓝[Icc t₀ T] t) (𝓝 0))
    (hK0 : 0 ≤ K) (hM0 : ∀ t, 0 ≤ M t) (hM : Integrable M (volume.restrict (Ioo t₀ T)))
    (hK : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ᵐ x ∂(volume : Measure Vec3), ∀ i : Fin 3,
      (u (x, t) i) ^ 2 ≤ K * M t) :
    ∀ i j, MemLp (fun z : ParabolicPoint => (1 / h) *
      (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j -
        u z i * u z j)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) := by
  intro i j
  have hac : t₀ ≤ t₀ + h := by linarith only [hh]
  have hdb : T - h + h ≤ T := (sub_add_cancel T h).le
  have hdb' : T - h ≤ T := by linarith only [hh]
  have hus := LPS.lps_memLp_forwardShift hac hdb hu
  have hum := LPS.lps_memLp_slab_mono le_rfl hdb' hu
  have hmeas : AEStronglyMeasurable (fun z : ParabolicPoint => (1 / h) *
      (u ((z.1, z.2 + h) : ParabolicPoint) i * u ((z.1, z.2 + h) : ParabolicPoint) j -
        u z i * u z j)) (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (T - h)))) :=
    (((hus.eval i).aestronglyMeasurable.mul (hus.eval j).aestronglyMeasurable).sub
      ((hum.eval i).aestronglyMeasurable.mul (hum.eval j).aestronglyMeasurable)).const_mul (1 / h)
  rw [memLp_two_iff_integrable_sq hmeas]
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (lps_diffQuotient_energy_continuousOn hh hslice hcont)
  have hmeas' : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      ((1 / h) * (u (z.1, z.2 + h) i * u (z.1, z.2 + h) j - u z i * u z j)) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ (T - h)))) := by
    rw [← lps_measure_slab_eq_prod]
    exact hmeas.pow 2
  suffices hI : Integrable (fun z : Vec3 × ℝ =>
      ((1 / h) * (u (z.1, z.2 + h) i * u (z.1, z.2 + h) j - u z i * u z j)) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo t₀ (T - h)))) by
    rw [← lps_measure_slab_eq_prod] at hI
    exact hI
  have hMI : IntervalIntegrable M volume t₀ T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith only [hhT, hh])).2 hM
  have hM1 : IntegrableOn M (Ioo t₀ (T - h)) :=
    IntegrableOn.mono_set hM (Ioo_subset_Ioo_right hdb')
  have hM2 : IntegrableOn (fun t => M (t + h)) (Ioo t₀ (T - h)) := by
    have h1 : IntervalIntegrable M volume (t₀ + h) T := hMI.mono_set (by
      rw [uIcc_of_le (by linarith only [hhT]), uIcc_of_le (by linarith only [hhT, hh])]
      exact Icc_subset_Icc hac le_rfl)
    have h2 := h1.comp_add_right h
    rw [add_sub_cancel_right] at h2
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith only [hhT])).1 h2
  have hsl := lps_flux_slice_bound hh hslice hK
  rw [integrable_prod_iff' hmeas']
  refine ⟨?_, ?_⟩
  · filter_upwards [hsl] with τ hτ
    exact (hτ.1 i j).integrable_sq
  · refine Integrable.mono' ((hM1.add hM2).const_mul (6 * K * S))
      hmeas'.norm.prod_swap.integral_prod_right' ?_
    filter_upwards [hsl, ae_restrict_mem measurableSet_Ioo] with τ hτ hτm
    have hτI : τ ∈ Icc t₀ (T - h) := Ioo_subset_Icc_self hτm
    have hE := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hS τ hτI))
    have hEn : (0 : ℝ) ≤ ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hκ0 : 0 ≤ 6 * K * (M τ + M (τ + h)) := by
      have := hM0 τ
      have := hM0 (τ + h)
      positivity
    have hsq : ∀ i j, Integrable (fun x : Vec3 =>
        ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2) :=
      fun i j => (hτ.1 i j).integrable_sq
    have hint : (∫ x : Vec3, ‖((1 / h) *
        (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2‖) =
        ∫ x : Vec3, ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun x => Real.norm_of_nonneg (sq_nonneg _))
    have hle : (∫ x : Vec3,
        ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2) ≤
        ∫ x : Vec3, ∑ i, ∑ j,
          ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2 := by
      refine integral_mono (hsq i j)
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hsq i j) ?_
      intro x
      refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3,
        ((1 / h) * (u (x, τ + h) i' * u (x, τ + h) j' - u (x, τ) i' * u (x, τ) j')) ^ 2)
        (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg _) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j' : Fin 3 =>
        ((1 / h) * (u (x, τ + h) i * u (x, τ + h) j' - u (x, τ) i * u (x, τ) j')) ^ 2)
        (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    have hnn : (0 : ℝ) ≤ ∫ x : Vec3, ‖((1 / h) *
        (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2‖ :=
      integral_nonneg fun x => norm_nonneg _
    change ‖∫ x : Vec3, ‖((1 / h) *
        (u (x, τ + h) i * u (x, τ + h) j - u (x, τ) i * u (x, τ) j)) ^ 2‖‖ ≤
      6 * K * S * (M τ + M (τ + h))
    rw [Real.norm_of_nonneg hnn, hint]
    calc _ ≤ _ := hle
      _ ≤ 6 * K * (M τ + M (τ + h)) *
          ∫ x : Vec3, ∑ i, ((1 / h) * (u (x, τ + h) i - u (x, τ) i)) ^ 2 := hτ.2
      _ ≤ 6 * K * (M τ + M (τ + h)) * S := mul_le_mul_of_nonneg_left hE hκ0
      _ = 6 * K * S * (M τ + M (τ + h)) := by ring

end ESS
