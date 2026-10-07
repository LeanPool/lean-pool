/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderGain
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLadderBound
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSpaceTimeProduct

/-!
# The induction step of the regularity ladder

`prop:lps-smoothing`: from the regularity `H^M` (`M ≥ 2`) on `[t₀ + δ/2, T]` to the regularity
`H^{M+1}` on `[t₀ + δ, T]`. The convection field is a product of `L²(I; H^M)` families with a
uniformly bounded factor, hence an `L²(I; H^M)` family, and the heat gain applies.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The induction step of the regularity ladder for `M ≥ 2` (`prop:lps-smoothing`). -/
theorem lps_ladder_step {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 < δ) (hδT : t₀ + δ < T)
    (hlad : ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ)
        (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
      (∀ i, ∀ t ∈ Icc (t₀ + δ / 2) T,
        IsSobolevFamilyOn M (Set.univ : Set Vec3) (Z i t []) (Z i t)) ∧
      (∀ i α, α.length ≤ M → ∀ t ∈ Icc (t₀ + δ / 2) T,
        Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume)
          (𝓝[Icc (t₀ + δ / 2) T] t) (𝓝 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ / 2) T)), ∀ i, ∀ α, α.length ≤ M →
        Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
      (∀ i, IsL2SobolevFamilyOn (M + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T)
        (fun z => u z i) (DD i)) ∧
      (∀ i k, DD i [k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T))] fun z => Du z i k) ∧
      (∀ i k, DD i [k, k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T))] fun z => D2u z i k k)) :
    ∃ (Z : Fin 3 → ℝ → List (Fin 3) → Vec3 → ℝ) (DD : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ),
      (∀ i, ∀ t ∈ Icc (t₀ + δ) T,
        IsSobolevFamilyOn (M + 1) (Set.univ : Set Vec3) (Z i t []) (Z i t)) ∧
      (∀ i α, α.length ≤ M + 1 → ∀ t ∈ Icc (t₀ + δ) T,
        Tendsto (fun s => eLpNorm (Z i s α - Z i t α) 2 volume)
          (𝓝[Icc (t₀ + δ) T] t) (𝓝 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) T)), ∀ i, ∀ α, α.length ≤ M + 1 →
        Z i t α =ᵐ[volume] fun x => DD i α (x, t)) ∧
      (∀ i, IsL2SobolevFamilyOn (M + 1 + 1) (Set.univ : Set Vec3) (Ioo (t₀ + δ) T)
        (fun z => u z i) (DD i)) ∧
      (∀ i k, DD i [k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => Du z i k) ∧
      (∀ i k, DD i [k, k] =ᵐ[volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo (t₀ + δ) T))] fun z => D2u z i k k) := by
  obtain ⟨Z, DD, h1, h2, h3, h4, h5, h6⟩ := hlad
  obtain ⟨K, hK⟩ := lps_ladder_slice_bound h1 h2 h3
  obtain ⟨C, -, hprod⟩ := lps_spaceTime_mul_family hM
  have hfg : ∀ i j, IsL2SobolevFamilyOn M (Set.univ : Set Vec3) (Ioo (t₀ + δ / 2) T)
      (fun z => u z j * Du z i j) (fun α => stLeibniz α (DD j) (fun γ => DD i (j :: γ))) := by
    intro i j
    have hf := lps_l2Family_of_le (h4 j) (Nat.le_succ M)
    have hg := lps_l2Family_shift (h4 i) j (h5 i j)
    exact (hprod hf hg (hK.mono fun t ht => ht j)).1
  exact lps_ladder_gain hsol hderiv hu hDu hD2u hDtu (by omega) hδ hδT DD h4 h5 h6
    (fun i α z => ∑ j, stLeibniz α (DD j) (fun γ => DD i (j :: γ)) z)
    (fun i => lps_l2Family_sum (fun j => hfg i j))

end ESS
