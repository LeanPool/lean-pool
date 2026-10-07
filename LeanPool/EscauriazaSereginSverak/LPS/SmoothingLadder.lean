/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderBase
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderStep

/-!
# The regularity ladder of a strong solution

`prop:lps-smoothing`: a strong solution has, for every order `M ≥ 1` and every `δ > 0`, an
`L²(t₀ + δ, T; H^{M+1})` family for each velocity component, whose spatial slices through
order `M` are `L²`-continuous on `[t₀ + δ, T]` and represent the family for almost every time.
The base of the induction is the `H²` bound of the slice equation; each step applies the
whole-space heat gain to the convection source.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The ladder at order two (`prop:lps-smoothing`). -/
theorem lps_ladder_two {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < T) :
    ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ) (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
      (∀ i, ∀ t ∈ Icc (t₀ + δ) T,
        IsSobolevFamilyOn 2 (Set.univ : Set Vec3) (Z i t []) (Z i t)) ∧
      (∀ i α, α.length ≤ 2 → ∀ t ∈ Icc (t₀ + δ) T,
        Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume)
          (𝓝[Icc (t₀ + δ) T] t) (𝓝 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) T)), ∀ i, ∀ α, α.length ≤ 2 →
        Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
      (∀ i, IsL2SobolevFamilyOn 3 (Set.univ : Set Vec3) (Ioo (t₀ + δ) T)
        (fun z => u z i) (DD i)) ∧
      (∀ i k, DD i [k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => Du z i k) ∧
      (∀ i k, DD i [k, k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => D2u z i k k) := by
  obtain ⟨K, hK⟩ := lps_sliceH2_ae_bound hsol hderiv hu hDu hD2u hDtu hδ hδT
  have hsub : Ioo (t₀ + δ / 2) T ⊆ Ioo t₀ T := Ioo_subset_Ioo (by linarith only [hδ]) le_rfl
  have hfam : ∀ i, IsL2SobolevFamilyOn (1 + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T)
      (fun z => u z i) (lpsStrongFamily u Du D2u i) := fun i =>
    lps_l2Family_mono_interval measurableSet_Ioo hsub
      (lps_strong_isL2SobolevFamily hderiv hu hDu hD2u i)
  obtain ⟨C, -, hprod⟩ := lps_spaceTime_mul_family_mixed
  have hfg : ∀ i j, IsL2SobolevFamilyOn 1 (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T)
      (fun z => u z j * Du z i j) (fun α => stLeibniz α (lpsStrongFamily u Du D2u j)
        (fun γ => lpsStrongFamily u Du D2u i (j :: γ))) := by
    intro i j
    have hg := lps_l2Family_shift (hfam i) j (Filter.EventuallyEq.rfl (f := fun z => Du z i j))
    refine (hprod (K := K) (hfam j) hg ?_).1
    filter_upwards [hK] with t ht
    refine le_trans ?_ ht
    unfold lpsSliceH2
    exact Finset.single_le_sum
      (f := fun j : Fin 3 => ∑ α ∈ sobolevWords 2,
        ∫ y : Vec3, (lpsStrongFamily u Du D2u j α (y, t)) ^ 2)
      (fun j _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
      (Finset.mem_univ j)
  exact lps_ladder_gain hsol hderiv hu hDu hD2u hDtu (M := 1) le_rfl hδ hδT
    (lpsStrongFamily u Du D2u) hfam (fun i k => Filter.EventuallyEq.rfl)
    (fun i k => Filter.EventuallyEq.rfl)
    (fun i α z => ∑ j, stLeibniz α (lpsStrongFamily u Du D2u j)
      (fun γ => lpsStrongFamily u Du D2u i (j :: γ)) z)
    (fun i => lps_l2Family_sum (fun j => hfg i j))

/-- The regularity ladder of a strong solution (`prop:lps-smoothing`): for every `M ≥ 1` and
`δ > 0`, each velocity component has an `L²(t₀ + δ, T; H^{M+1})` family, agreeing with the given
first and second derivatives, whose slices through order `M` are `L²`-continuous on
`[t₀ + δ, T]` and represent the family for almost every time. -/
theorem lps_ladder {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (M : ℕ) (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < T) :
    ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ) (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
      (∀ i, ∀ t ∈ Icc (t₀ + δ) T,
        IsSobolevFamilyOn M (Set.univ : Set Vec3) (Z i t []) (Z i t)) ∧
      (∀ i α, α.length ≤ M → ∀ t ∈ Icc (t₀ + δ) T,
        Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume)
          (𝓝[Icc (t₀ + δ) T] t) (𝓝 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) T)), ∀ i, ∀ α, α.length ≤ M →
        Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
      (∀ i, IsL2SobolevFamilyOn (M + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ) T)
        (fun z => u z i) (DD i)) ∧
      (∀ i k, DD i [k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => Du z i k) ∧
      (∀ i k, DD i [k, k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => D2u z i k k) := by
  have key : ∀ N : ℕ, 2 ≤ N → ∀ δ : ℝ, 0 < δ → t₀ + δ < T →
      ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ) (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
      (∀ i, ∀ t ∈ Icc (t₀ + δ) T,
        IsSobolevFamilyOn N (Set.univ : Set Vec3) (Z i t []) (Z i t)) ∧
      (∀ i α, α.length ≤ N → ∀ t ∈ Icc (t₀ + δ) T,
        Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume)
          (𝓝[Icc (t₀ + δ) T] t) (𝓝 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) T)), ∀ i, ∀ α, α.length ≤ N →
        Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
      (∀ i, IsL2SobolevFamilyOn (N + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ) T)
        (fun z => u z i) (DD i)) ∧
      (∀ i k, DD i [k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => Du z i k) ∧
      (∀ i k, DD i [k, k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => D2u z i k k) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact fun δ hδ hδT => lps_ladder_two hsol hderiv hu hDu hD2u hDtu hδ hδT
    | succ N hN ih =>
        exact fun δ hδ hδT => lps_ladder_step hsol hderiv hu hDu hD2u hDtu hN hδ hδT
          (ih (δ / 2) (by linarith only [hδ]) (by linarith only [hδT, hδ]))
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have hM1 : M = 1 := by omega
    subst hM1
    obtain ⟨Z, DD, h1, h2, h3, h4, h5, h6⟩ := key 2 le_rfl δ hδ hδT
    exact ⟨Z, DD, fun i t ht => (h1 i t ht).of_le (by norm_num),
      fun i α hα t ht => h2 i α (hα.trans (by norm_num)) t ht,
      h3.mono fun t ht i α hα => ht i α (hα.trans (by norm_num)),
      fun i => lps_l2Family_of_le (h4 i) (by norm_num), h5, h6⟩
  · exact key M hM2 δ hδ hδT

end ESS
