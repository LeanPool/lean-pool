/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderTools
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingWholeHeatGain
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSourceFamily
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingStrongHeat
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularitySpatial

/-!
# The regularity gain step of the ladder

`prop:lps-smoothing`: if the components of a strong solution form an `L²(I; H^{M+1})` family on
`(t₀ + δ/2, T)` and the convection field has an `L²(I; H^M)` family there, then the source
`∂ₜu - Δu` has an `L²(I; H^M)` family and the whole-space heat gain produces continuous slices
of order `M + 1` and an `L²(I; H^{M+2})` family on `(t₀ + δ, T)`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The heat-gain step of the regularity ladder (`prop:lps-smoothing`). -/
theorem lps_ladder_gain {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {M : ℕ} (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < T)
    (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ)
    (hDD : ∀ i, IsL2SobolevFamilyOn (M + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T)
      (fun z => u z i) (DD i))
    (hDD1 : ∀ i k, DD i [k] =ᵐ[volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T))] fun z => Du z i k)
    (hDD2 : ∀ i k, DD i [k, k] =ᵐ[volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T))] fun z => D2u z i k k)
    (DB : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ)
    (hB : ∀ i, IsL2SobolevFamilyOn M (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T)
      (fun z => ∑ j, u z j * Du z i j) (DB i)) :
    ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ) (DD' : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
      (∀ i, ∀ t ∈ Icc (t₀ + δ) T,
        IsSobolevFamilyOn (M + 1) (Set.univ : Set Vec3) (Z i t []) (Z i t)) ∧
      (∀ i α, α.length ≤ M + 1 → ∀ t ∈ Icc (t₀ + δ) T,
        Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume)
          (𝓝[Icc (t₀ + δ) T] t) (𝓝 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) T)), ∀ i, ∀ α, α.length ≤ M + 1 →
        Z i t α =ᵐ[volume] fun x => DD' i α (x, t)) ∧
      (∀ i, IsL2SobolevFamilyOn (M + 1 + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ) T)
        (fun z => u z i) (DD' i)) ∧
      (∀ i k, DD' i [k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => Du z i k) ∧
      (∀ i k, DD' i [k, k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => D2u z i k k) := by
  set a : ℝ := t₀ + δ / 2 with ha
  have hat₀ : t₀ ≤ a := by rw [ha]; linarith only [hδ]
  have hb : a + (T - a) = T := by ring
  have hs : a + δ / 2 = t₀ + δ := by rw [ha]; ring
  obtain ⟨DG, hG, -⟩ := lps_source_family hsol hderiv hu hDu hD2u hDtu hat₀ le_rfl DB hB
  obtain ⟨C, -, hC⟩ := lps_wholeHeatGain (M + 1) (by omega) (σ := δ / 2) (β := T - a)
    (by linarith only [hδ]) (by rw [ha]; linarith only [hδT])
  have hheat : ∀ i, IsHeatSolutionOn (Set.univ : Set Vec3) (Ioo a T) (fun z => u z i)
      (fun z => Dtu z i - ∑ j, D2u z i j j) := fun i =>
    lps_heat_mono_interval measurableSet_Ioo (Ioo_subset_Ioo hat₀ le_rfl)
      (lps_strong_isHeatSolution hderiv hu hD2u hDtu i)
  have key := fun i : Fin 3 => hC a (fun z => u z i) (fun z => Dtu z i - ∑ j, D2u z i j j)
    (DD i) (DG i) (by rw [hb]; exact hDD i) (by rw [hb]; exact hG i)
    (by rw [hb]; exact hheat i)
  choose Z Dz' hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 using key
  simp only [hb, hs] at hZ1 hZ2 hZ3 hZ4 hZ5 hZ6
  have hmono : (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T)) :
      Measure (Vec3 × ℝ)) ≤
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a T)) :=
    Measure.restrict_mono (prod_mono subset_rfl
      (Ioo_subset_Ioo (by rw [ha]; linarith only [hδ]) le_rfl)) le_rfl
  refine ⟨Z, Dz', fun i => hZ1 i, fun i => hZ2 i, ?_, fun i => hZ4 i, ?_, ?_⟩
  · rw [ae_all_iff]
    intro i
    filter_upwards [hZ3 i, LPS.lps_sobolevFamily_spatialSlices_ae (hZ4 i),
      ae_restrict_mem measurableSet_Ioo] with t h3 h4 htI α hα
    have htIcc : t ∈ Icc (t₀ + δ) T := ⟨htI.1.le, htI.2.le⟩
    have hzf := (hZ1 i t htIcc).congr_ae (f' := fun x => u (x, t) i)
      (by rw [Measure.restrict_univ]; exact h3) (fun α _ => Filter.EventuallyEq.rfl)
    have h4' := h4.of_le (m' := M + 1) (Nat.le_succ _)
    have := IsSobolevFamilyOn.ae_eq isOpen_univ hzf h4' α hα
    rwa [Measure.restrict_univ] at this
  · intro i k
    filter_upwards [hZ5 i [k] (by simp only [List.length_cons, List.length_nil]; omega),
      ae_mono hmono (hDD1 i k)] with q h1 h2
    exact h1.trans h2
  · intro i k
    filter_upwards [hZ5 i [k, k] (by simp only [List.length_cons, List.length_nil]; omega),
      ae_mono hmono (hDD2 i k)] with q h1 h2
    exact h1.trans h2

end ESS
