/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainSetup

/-!
# The cutoff solution and its derivative families

For a local solution `z` of `∂ₜ z - Δ z = G` on `B × I` with derivative
families `Dz` and `DG`, and a smooth cutoff `η` vanishing for `x` outside a
compact subset of `B`, the cutoff `w = ηz` and its source
`H = ηG + (∂ₜη - Δη) z - 2 ∇η · ∇z` have explicit Leibniz derivative families
`localHeatGainDw` and `localHeatGainDH` on `ℝ³ × I`, and `w` solves
`∂ₜ w - Δ w = H` there (`lem:local-heat-gain`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The multiplier `∂ₜη - Δη`. -/
@[expose] def localHeatGainZeta (η : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ :=
  fun p => timePartial η p - ∑ k : Fin 3, spatialSecondPartial η k k p

/-- The derivative family of the cutoff `ηz`. -/
@[expose] def localHeatGainDw (η : Vec3 × ℝ → ℝ) (Dz : List (Fin 3) → Vec3 × ℝ → ℝ) :
    List (Fin 3) → Vec3 × ℝ → ℝ :=
  fun α => stLeibniz α (fun γ => spaceTimeWord γ η) Dz

/-- The derivative family of the source `ηG + (∂ₜη - Δη) z - 2 ∇η · ∇z`. -/
@[expose] def localHeatGainDH (η : Vec3 × ℝ → ℝ) (Dz DG : List (Fin 3) → Vec3 × ℝ → ℝ) :
    List (Fin 3) → Vec3 × ℝ → ℝ :=
  fun α p => stLeibniz α (fun γ => spaceTimeWord γ η) DG p +
    (stLeibniz α (fun γ => spaceTimeWord γ (localHeatGainZeta η)) Dz p +
      (-2) * ∑ j : Fin 3, stLeibniz α
        (fun γ => spaceTimeWord γ (fun q => spatialPartial η j q)) (fun γ => Dz (j :: γ)) p)

/-- The zero family. -/
theorem isSpaceTimeFamily_zero (n : ℕ) (V : Set (Vec3 × ℝ)) :
    IsSpaceTimeFamily n V (fun _ _ => 0) := by
  refine ⟨fun α _ => MemLp.zero, fun α j _ φ _ _ _ => ?_⟩
  simp

/-- Finite sums of space-time derivative families. -/
theorem IsSpaceTimeFamily.finset_sum {ι : Type*} (s : Finset ι) {n : ℕ} {V : Set (Vec3 × ℝ)}
    {B : ι → List (Fin 3) → Vec3 × ℝ → ℝ} (h : ∀ i ∈ s, IsSpaceTimeFamily n V (B i)) :
    IsSpaceTimeFamily n V (fun α p => ∑ i ∈ s, B i α p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSpaceTimeFamily_zero n V
  | insert i s hi ih =>
      have h1 := h i (Finset.mem_insert_self i s)
      have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      have h3 := h1.add h2
      refine ⟨fun α hα => ?_, fun α j hα => ?_⟩
      · simpa [Finset.sum_insert hi] using h3.memL2 α hα
      · have e : (fun p => ∑ k ∈ insert i s, B k α p) = fun p => B i α p + ∑ k ∈ s, B k α p :=
          funext fun p => Finset.sum_insert hi
        have e' : (fun p => ∑ k ∈ insert i s, B k (α ++ [j]) p) =
            fun p => B i (α ++ [j]) p + ∑ k ∈ s, B k (α ++ [j]) p :=
          funext fun p => Finset.sum_insert hi
        rw [e, e']
        exact h3.weak α j hα

/-- The hypotheses on a cutoff: smoothness, compact spatial support inside `B`,
and all spatial word derivatives of `η`, `∂ₜη - Δη` and `∂_j η` bounded. -/
structure IsLocalHeatCutoff (B : Set Vec3) (K : Set Vec3) (η : Vec3 × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) η
  compact : IsCompact K
  subset : K ⊆ B
  zero : ∀ x, x ∉ K → ∀ t, η (x, t) = 0
  bound : ∀ γ : List (Fin 3), ∃ L : ℝ, ∀ p, |spaceTimeWord γ η p| ≤ L
  boundZeta : ∀ γ : List (Fin 3), ∃ L : ℝ, ∀ p, |spaceTimeWord γ (localHeatGainZeta η) p| ≤ L
  boundGrad : ∀ (j : Fin 3) (γ : List (Fin 3)), ∃ L : ℝ,
    ∀ p, |spaceTimeWord γ (fun q => spatialPartial η j q) p| ≤ L

namespace IsLocalHeatCutoff

variable {B K : Set Vec3} {η : Vec3 × ℝ → ℝ}

theorem smooth_zeta (h : IsLocalHeatCutoff B K η) :
    ContDiff ℝ (⊤ : ℕ∞) (localHeatGainZeta η) :=
  (vorticityHeatSmooth_timePartial_contDiff h.smooth).sub
    (ContDiff.sum (s := Finset.univ) fun k _ =>
      vorticityHeatSmooth_spatialPartial_contDiff
        (vorticityHeatSmooth_spatialPartial_contDiff h.smooth k) k)

theorem smooth_grad (h : IsLocalHeatCutoff B K η) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial η j q) :=
  vorticityHeatSmooth_spatialPartial_contDiff h.smooth j

theorem zeta_zero (h : IsLocalHeatCutoff B K η) :
    ∀ x, x ∉ K → ∀ t, localHeatGainZeta η (x, t) = 0 := by
  intro x hx t
  have h2 (k : Fin 3) : spatialSecondPartial η k k (x, t) = 0 :=
    spatialPartial_eq_zero_of_compl h.compact
      (spatialPartial_eq_zero_of_compl h.compact h.zero k) k x hx t
  change timePartial η (x, t) - ∑ k : Fin 3, spatialSecondPartial η k k (x, t) = 0
  rw [timePartial_eq_zero_of_compl h.zero x hx t, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_const_zero, sub_zero]

theorem grad_zero (h : IsLocalHeatCutoff B K η) (j : Fin 3) :
    ∀ x, x ∉ K → ∀ t, spatialPartial η j (x, t) = 0 :=
  spatialPartial_eq_zero_of_compl h.compact h.zero j

end IsLocalHeatCutoff

/-- The families of the cutoff solution and of its source. -/
theorem localHeatGain_families {m : ℕ} (hm1 : 1 ≤ m) {B K N : Set Vec3} {I : Set ℝ}
    (hBm : MeasurableSet B) (hIm : MeasurableSet I) {η : Vec3 × ℝ → ℝ}
    (hη : IsLocalHeatCutoff B K η) (hN : IsOpen N) (hKN : K ⊆ N) {κ : Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) (hκB : tsupport κ ⊆ B)
    (hκN : ∀ x ∈ N, κ x = 1) {Dz DG : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hDz : IsSpaceTimeFamily m (B ×ˢ I) Dz) (hDG : IsSpaceTimeFamily (m - 1) (B ×ˢ I) DG) :
    IsSpaceTimeFamily m ((univ : Set Vec3) ×ˢ I) (localHeatGainDw η Dz) ∧
      IsSpaceTimeFamily (m - 1) ((univ : Set Vec3) ×ˢ I) (localHeatGainDH η Dz DG) ∧
      (∀ α (p : Vec3 × ℝ), p.1 ∉ K → localHeatGainDw η Dz α p = 0) ∧
      (∀ α (p : Vec3 × ℝ), p.1 ∉ K → localHeatGainDH η Dz DG α p = 0) := by
  have hvη (p : Vec3 × ℝ) (hp : p.1 ∉ K) (γ : List (Fin 3)) : spaceTimeWord γ η p = 0 :=
    spaceTimeWord_eq_zero_of_compl hη.compact γ hη.zero p.1 hp p.2
  have hvζ (p : Vec3 × ℝ) (hp : p.1 ∉ K) (γ : List (Fin 3)) :
      spaceTimeWord γ (localHeatGainZeta η) p = 0 :=
    spaceTimeWord_eq_zero_of_compl hη.compact γ hη.zeta_zero p.1 hp p.2
  have hvj (j : Fin 3) (p : Vec3 × ℝ) (hp : p.1 ∉ K) (γ : List (Fin 3)) :
      spaceTimeWord γ (fun q => spatialPartial η j q) p = 0 :=
    spaceTimeWord_eq_zero_of_compl hη.compact γ (hη.grad_zero j) p.1 hp p.2
  have hDw0 : ∀ α (p : Vec3 × ℝ), p.1 ∉ K → localHeatGainDw η Dz α p = 0 :=
    fun α p hp => stLeibniz_eq_zero_of_forall α (hvη p hp)
  have hDH0 : ∀ α (p : Vec3 × ℝ), p.1 ∉ K → localHeatGainDH η Dz DG α p = 0 := by
    intro α p hp
    simp only [localHeatGainDH, stLeibniz_eq_zero_of_forall α (hvη p hp),
      stLeibniz_eq_zero_of_forall α (hvζ p hp),
      fun j => stLeibniz_eq_zero_of_forall α (B := fun γ => Dz (j :: γ)) (hvj j p hp),
      Finset.sum_const_zero, mul_zero, add_zero]
  have hDwV : IsSpaceTimeFamily m (B ×ˢ I) (localHeatGainDw η Dz) :=
    hDz.smooth_mul hη.smooth hη.bound
  have hDHV : IsSpaceTimeFamily (m - 1) (B ×ˢ I) (localHeatGainDH η Dz DG) := by
    have h1 := hDG.smooth_mul hη.smooth hη.bound
    have h2 := (hDz.mono_order (Nat.sub_le m 1)).smooth_mul hη.smooth_zeta hη.boundZeta
    have h3 := (IsSpaceTimeFamily.finset_sum Finset.univ fun j _ =>
      (hDz.shift hm1 j).smooth_mul (hη.smooth_grad j) (hη.boundGrad j)).const_mul (-2)
    exact h1.add (h2.add h3)
  refine ⟨hDwV.extend_univ hIm hBm hη.subset hN hKN hκ hκc hκB hκN
      (fun α _ p hp => hDw0 α p hp),
    hDHV.extend_univ hIm hBm hη.subset hN hKN hκ hκc hκB hκN
      (fun α _ p hp => hDH0 α p hp), hDw0, hDH0⟩

/-- The heat equation for the cutoff solution. -/
theorem localHeatGain_heat {B K : Set Vec3} {I : Set ℝ} (hIm : MeasurableSet I)
    {η : Vec3 × ℝ → ℝ} (hη : IsLocalHeatCutoff B K η) {m : ℕ} (hm1 : 1 ≤ m)
    {Dz DG : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hDz : IsSpaceTimeFamily m (B ×ˢ I) Dz) (hDG : IsSpaceTimeFamily (m - 1) (B ×ˢ I) DG)
    (hheat : IsHeatSolutionOn B I (Dz []) (DG [])) :
    IsHeatSolutionOn univ I (localHeatGainDw η Dz []) (localHeatGainDH η Dz DG []) := by
  intro φ hφ hφc hφV
  have h := heatCutoff_equation (U := B) (K := K) (I := I) hIm hη.compact hη.subset
    (z := Dz []) (G := DG []) (Dz := fun j => Dz [j]) hη.smooth hη.zero
    (hDz.memL2 [] (Nat.zero_le _))
    (fun j => hDz.memL2 [j] (by simp only [List.length_singleton]; omega))
    (hDG.memL2 [] (Nat.zero_le _))
    (fun j => hDz.weak [] j (by simp only [List.length_nil]; omega)) hheat
    φ hφ hφc hφV
  have e1 : ∫ p in (univ : Set Vec3) ×ˢ I, localHeatGainDw η Dz [] p *
      (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
      ∫ p in (univ : Set Vec3) ×ˢ I, η p * Dz [] p *
        (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) := rfl
  have e2 : ∫ p in (univ : Set Vec3) ×ˢ I, localHeatGainDH η Dz DG [] p * φ p =
      ∫ p in (univ : Set Vec3) ×ˢ I,
        (η p * DG [] p + (timePartial η p - ∑ j : Fin 3, spatialSecondPartial η j j p) *
          Dz [] p - 2 * ∑ j : Fin 3, spatialPartial η j p * Dz [j] p) * φ p := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [localHeatGainDH, stLeibniz]
    change (η p * DG [] p + ((timePartial η p - ∑ k : Fin 3, spatialSecondPartial η k k p) *
        Dz [] p + (-2) * ∑ j : Fin 3, spatialPartial η j p * Dz [j] p)) * φ p = _
    ring
  rw [e1, e2]
  exact h

end ESS
