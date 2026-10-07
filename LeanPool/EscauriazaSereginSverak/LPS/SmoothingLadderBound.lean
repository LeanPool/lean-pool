/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderTools
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingKLBoundFlux

/-!
# Uniform slice bounds from continuity

`prop:lps-smoothing`: the slices of an `L²`-continuous family of order `M` on a compact time
interval have uniformly bounded `H^M` energy, and the same bound holds for almost every slice
of the space-time family that the curves represent.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The square integral of a square-integrable real function is the square of its `L²` norm. -/
theorem lps_integral_sq_eq_toReal_sq {f : Vec3 → ℝ} (hf : MemLp f 2 volume) :
    ∫ x : Vec3, f x ^ 2 = (eLpNorm f 2 volume).toReal ^ 2 := by
  have h : lpNorm f 2 volume = Real.sqrt (∫ x : Vec3, f x ^ 2) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num)
      (by norm_num) hf.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have h2 : lpNorm f 2 volume = (eLpNorm f 2 volume).toReal := rfl
  rw [← h2, h, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x))]

/-- The `L²` norm of an `L²`-continuous curve is continuous. -/
theorem lps_l2Norm_continuousOn {S : Set ℝ} {f : ℝ → Vec3 → ℝ}
    (hf : ∀ t ∈ S, MemLp (f t) 2 volume)
    (hcont : ∀ t ∈ S,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => f s x - f t x) 2 volume) (𝓝[S] t) (𝓝 0)) :
    ContinuousOn (fun t => (eLpNorm (f t) 2 volume).toReal) S := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hN : Tendsto (fun s => (eLpNorm (fun x : Vec3 => f s x - f t x) 2 volume).toReal)
      (𝓝[S] t) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont t ht)
    rw [ENNReal.toReal_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hN
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' := hf s hs
  have ht' := hf t ht
  have hd : MemLp (fun x : Vec3 => f s x - f t x) 2 volume := hs'.sub ht'
  have tri : ∀ (g h : Vec3 → ℝ), MemLp g 2 volume → MemLp h 2 volume →
      (eLpNorm g 2 volume).toReal ≤ (eLpNorm h 2 volume).toReal +
        (eLpNorm (fun x => g x - h x) 2 volume).toReal := by
    intro g h hg hh
    have hgh : MemLp (fun x => g x - h x) 2 volume := hg.sub hh
    have h1 : eLpNorm g 2 volume ≤ eLpNorm h 2 volume + eLpNorm (fun x => g x - h x) 2 volume := by
      have := eLpNorm_add_le (μ := volume) (p := 2) (f := h) (g := fun x => g x - h x)
        (by norm_num)
      have e : (h + fun x => g x - h x) = g := funext fun x => by simp
      rwa [e] at this
    rw [← ENNReal.toReal_add hh.eLpNorm_ne_top hgh.eLpNorm_ne_top]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hh.eLpNorm_ne_top, hgh.eLpNorm_ne_top⟩) h1
  have a1 := tri _ _ hs' ht'
  have a2 := tri _ _ ht' hs'
  have e : eLpNorm (fun x : Vec3 => f t x - f s x) 2 volume =
      eLpNorm (fun x : Vec3 => f s x - f t x) 2 volume := by
    rw [← eLpNorm_neg]
    congr 1
    funext x
    simp
  rw [e] at a2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [a1, a2]

/-- Uniform `H^M` slice bounds for a family of order `M` whose slices are `L²`-continuous on a
compact interval `[a, b]` and represent, for almost every time, the derivatives of a space-time
family (`prop:lps-smoothing`). -/
theorem lps_ladder_slice_bound {a b : ℝ} {M : ℕ}
    {Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ} {DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ}
    (hfam : ∀ i, ∀ t ∈ Icc a b, IsSobolevFamilyOn M (Set.univ : Set Vec3) (Z i t []) (Z i t))
    (hcont : ∀ i α, α.length ≤ M → ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ i, ∀ α, α.length ≤ M →
      Z i t α =ᵐ[volume] fun x => DD i α (x, t)) :
    ∃ K : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ i,
      ∑ α ∈ sobolevWords M, ∫ x : Vec3, (DD i α (x, t)) ^ 2 ≤ K := by
  have hmem : ∀ i, ∀ α, α.length ≤ M → ∀ t ∈ Icc a b, MemLp (Z i t α) 2 volume := by
    intro i α hα t ht
    have h := (hfam i t ht).memL2 α hα
    rwa [Measure.restrict_univ] at h
  have hR : ∀ i α, ∃ R : ℝ, α.length ≤ M → ∀ t ∈ Icc a b,
      (eLpNorm (Z i t α) 2 volume).toReal ≤ R := by
    intro i α
    by_cases hα : α.length ≤ M
    · have hc := lps_l2Norm_continuousOn (S := Icc a b) (f := fun t => Z i t α)
        (fun t ht => hmem i α hα t ht) (fun t ht => hcont i α hα t ht)
      obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
      exact ⟨R, fun _ t ht => (le_abs_self _).trans (by simpa using hR t ht)⟩
    · exact ⟨0, fun h => absurd h hα⟩
  choose R hR using hR
  refine ⟨∑ i, ∑ α ∈ sobolevWords M, (R i α) ^ 2, ?_⟩
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htI i
  have htIcc : t ∈ Icc a b := ⟨htI.1.le, htI.2.le⟩
  have hterm : ∀ α ∈ sobolevWords M, ∫ x : Vec3, (DD i α (x, t)) ^ 2 ≤ (R i α) ^ 2 := by
    intro α hα
    have hα' := mem_sobolevWords.mp hα
    have e : ∫ x : Vec3, (DD i α (x, t)) ^ 2 = ∫ x : Vec3, (Z i t α x) ^ 2 :=
      integral_congr_ae ((ht i α hα').mono fun x hx => by simp only [hx])
    rw [e, lps_integral_sq_eq_toReal_sq (hmem i α hα' t htIcc)]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hR i α hα' t htIcc) 2
  refine (Finset.sum_le_sum hterm).trans ?_
  exact Finset.single_le_sum (f := fun i : Fin 3 => ∑ α ∈ sobolevWords M, (R i α) ^ 2)
    (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end ESS
