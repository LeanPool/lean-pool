/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalInteriorChart

/-!
# Spatial propagation of vorticity vanishing

This is the closedness step of the continuation argument in the proof of
`thm:ess-local` (spatial unique continuation): if the weak
vorticity vanishes near `(x', t)` and `x'` is within `1/8` of `x`, then it
vanishes near `(x, t)`, provided the solution has bounded velocity on the unit
past cylinder with top `(x, t + 1/8)`.  The vorticity chart of
`thm:vorticity-regularity` supplies a regular representative, and unique
continuation (`thm:uc`, `lem:flat-from-vanishing`) is applied at every top time
near `t`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Vanishing of the weak vorticity near `(x', t)` propagates to a
neighborhood of `(x, t)` when `|x' - x| < 1/8` and the velocity is bounded on
the unit past cylinder with top `(x, t + 1/8)`. -/
theorem essLocal_vorticityZero_propagate
    {J : Set ℝ} {V : ParabolicPoint → Vec3} {DV : ParabolicPoint → Fin 3 → Vec3}
    {pv : ParabolicPoint → ℝ} (M : ℝ) (hM : 0 ≤ M)
    (hsws : IsSuitableWeakSolution Set.univ J 3 V DV pv (0 : ParabolicPoint → Vec3))
    (x : Vec3) (t : ℝ)
    (hcl : closure (parabolicCylinder x (t + 1 / 8) 1) ⊆ spaceTimeSet Set.univ J)
    (hV : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x (t + 1 / 8) 1)),
      vec3EuclideanNorm (V z) ≤ M)
    (x' : Vec3) (hx' : vec3EuclideanNorm (x' - x) < 1 / 8) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball x' r) (Ioo (t - r ^ 2) (t + r ^ 2)))),
      weakVorticity DV z = 0) :
    ∃ r' : ℝ, 0 < r' ∧ ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball x r') (Ioo (t - r' ^ 2) (t + r' ^ 2)))),
      weakVorticity DV z = 0 := by
  have htriangle : ∀ a b c : Vec3, vec3EuclideanNorm (a - c) ≤
      vec3EuclideanNorm (a - b) + vec3EuclideanNorm (b - c) := by
    intro a b c
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have : Measure.IsOpenPosMeasure (volume : Measure ParabolicPoint) :=
    ⟨fun U hU hne => by
      have ho : IsOpen (parabolicHomeomorph.symm ⁻¹' U) :=
        hU.preimage parabolicHomeomorph.symm.continuous
      have hn : (parabolicHomeomorph.symm ⁻¹' U).Nonempty := by
        obtain ⟨z, hz⟩ := hne
        exact ⟨parabolicHomeomorph z, hz⟩
      exact ho.measure_ne_zero (volume : Measure (Vec3 × ℝ)) hn⟩
  obtain ⟨C, hC, ω, Dω, D2ω, Dtω, hωae, hωcont, hωderiv, hωL2, hωineq, hωbd⟩ :=
    essLocal_vorticityChart M hM hsws x (t + 1 / 8) hcl hV
  have hxx' : vec3EuclideanNorm (x - x') < 1 / 8 := by
    rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, norm_sub_rev, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2]
    exact hx'
  let Q : Set ParabolicPoint := parabolicCylinder x (t + 1 / 8) (1 / 2 : ℝ)
  let O : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball x (1 / 2)) (Ioo (t - 1 / 8) (t + 1 / 8))
  have hOopen : IsOpen O := isOpen_spaceTimeSet _ _ (isOpen_vec3Ball x _) isOpen_Ioo
  have hOQ : O ⊆ Q := by
    rintro z ⟨hz1, hz2, hz3⟩
    exact ⟨hz1, by linarith only [hz2], le_of_lt hz3⟩
  have hωcontO : ContinuousOn ω O := hωcont.mono (hOQ.trans subset_closure)
  have hbdO : ∀ z ∈ O, vec3EuclideanNorm (ω z) ≤ C :=
    essLocal_le_of_ae_le_of_continuousOn hOopen
      (CKN.continuous_vec3EuclideanNorm.comp_continuousOn hωcontO)
      (ae_restrict_of_ae_restrict_of_subset hOQ hωbd)
  have hr2 : 0 < r ^ 2 := by positivity
  let r₁ : ℝ := min (r / 2) (1 / 4)
  let σ : ℝ := min (r ^ 2 / 2) (1 / 16)
  have hr₁pos : 0 < r₁ := lt_min (by positivity) (by norm_num)
  have hr₁r : r₁ ≤ r / 2 := min_le_left _ _
  have hr₁q : r₁ ≤ 1 / 4 := min_le_right _ _
  have hr₁sq : r₁ ^ 2 ≤ r ^ 2 / 4 := by
    nlinarith only [hr₁r, hr₁pos]
  have hr₁sq' : r₁ ^ 2 ≤ 1 / 16 := by
    nlinarith only [hr₁q, hr₁pos]
  have hσpos : 0 < σ := lt_min (by positivity) (by norm_num)
  have hσr : σ ≤ r ^ 2 / 2 := min_le_left _ _
  have hσq : σ ≤ 1 / 16 := min_le_right _ _
  have htop : ∀ t' ∈ Ioo (t - σ) (t + σ), ∀ y ∈ vec3Ball x' (1 / 4), ω (y, t') = 0 := by
    intro t' ht'
    let P : Set ParabolicPoint := spaceTimeSet (vec3Ball x' r₁) (Ioo (t' - r₁ ^ 2) t')
    have hPopen : IsOpen P := isOpen_spaceTimeSet _ _ (isOpen_vec3Ball x' _) isOpen_Ioo
    have hPzero : P ⊆ spaceTimeSet (vec3Ball x' r) (Ioo (t - r ^ 2) (t + r ^ 2)) := by
      rintro z ⟨hz1, hz2, hz3⟩
      refine ⟨vec3Ball_mono (by linarith only [hr₁r, hr]) hz1, ?_, ?_⟩
      · linarith only [hz2, ht'.1, hσr, hr₁sq, hr2]
      · linarith only [hz3, ht'.2, hσr, hr2]
    have hPO : P ⊆ O := by
      rintro z ⟨hz1, hz2, hz3⟩
      refine ⟨?_, ?_, ?_⟩
      · have htri := htriangle z.1 x' x
        have hz1' : vec3EuclideanNorm (z.1 - x') < r₁ := hz1
        change vec3EuclideanNorm (z.1 - x) < 1 / 2
        linarith only [htri, hz1', hr₁q, hx']
      · linarith only [hz2, ht'.1, hσq, hr₁sq']
      · linarith only [hz3, ht'.2, hσq]
    have hωP : ∀ z ∈ P, ω z = 0 := by
      have hae : ω =ᵐ[volume.restrict P] (fun _ => 0) := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (hPO.trans hOQ) hωae,
          ae_restrict_of_ae_restrict_of_subset hPzero hzero] with z h1 h2
        rw [h1, h2]
      exact Measure.eqOn_open_of_ae_eq hae hPopen (hωcontO.mono hPO) continuousOn_const
    have hsubUC : spaceTimeSet (vec3Ball x' (1 / 4)) (Ioc (t' - 1 / 16) t') ⊆ O := by
      rintro z ⟨hz1, hz2, hz3⟩
      refine ⟨?_, ?_, ?_⟩
      · have htri := htriangle z.1 x' x
        have hz1' : vec3EuclideanNorm (z.1 - x') < 1 / 4 := hz1
        change vec3EuclideanNorm (z.1 - x) < 1 / 2
        linarith only [htri, hz1', hx']
      · linarith only [hz2, ht'.1, hσq]
      · linarith only [hz3, ht'.2, hσq]
    have hsubUCo : spaceTimeSet (vec3Ball x' (1 / 4)) (Ioo (t' - 1 / 16) t') ⊆
        spaceTimeSet (vec3Ball x' (1 / 4)) (Ioc (t' - 1 / 16) t') :=
      fun z hz => ⟨hz.1, hz.2.1, le_of_lt hz.2.2⟩
    have hsubQ := hsubUCo.trans (hsubUC.trans hOQ)
    have hballsub : vec3Ball x' (1 / 4) ⊆ vec3Ball x (1 / 2) := by
      intro y hy
      have htri := htriangle y x' x
      have hy' : vec3EuclideanNorm (y - x') < 1 / 4 := hy
      change vec3EuclideanNorm (y - x) < 1 / 2
      linarith only [htri, hy', hx']
    have htimesub : Ioo (t' - 1 / 16) t' ⊆ Ioo (t + 1 / 8 - 1 / 4) (t + 1 / 8) := by
      rintro s ⟨hs1, hs2⟩
      exact ⟨by linarith only [hs1, ht'.1, hσq], by linarith only [hs2, ht'.2, hσq]⟩
    have hderivUC : HasSpaceTimeWeakDerivs (vec3Ball x' (1 / 4)) (Ioo (t' - 1 / 16) t')
        ω Dω D2ω Dtω :=
      essLocal_weakDerivs_restrict hballsub htimesub
        (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball x _) isOpen_Ioo).measurableSet hωderiv
    exact essLocal_uniqueContinuation_past (1 / 4) (1 / 16) C C r₁ (by norm_num)
      (by norm_num) hC hC hr₁pos hr₁q hr₁sq' x' t' ω Dω D2ω Dtω (hωcontO.mono hsubUC)
      hderivUC (lt_of_le_of_lt (lintegral_mono_set hsubQ) hωL2)
      (ae_restrict_of_ae_restrict_of_subset hsubQ hωineq)
      (fun z hz => hbdO z (hsubUC hz)) (fun y s hy hs => hωP (y, s) ⟨hy, hs⟩)
  let r' : ℝ := min (1 / 8) σ
  have hr'pos : 0 < r' := lt_min (by norm_num) hσpos
  have hr'q : r' ≤ 1 / 8 := min_le_left _ _
  have hr'σ : r' ≤ σ := min_le_right _ _
  have hr'sq : r' ^ 2 ≤ σ := by nlinarith only [hr'pos, hr'q, hr'σ]
  refine ⟨r', hr'pos, ?_⟩
  let N : Set ParabolicPoint := spaceTimeSet (vec3Ball x r') (Ioo (t - r' ^ 2) (t + r' ^ 2))
  have hNmeas : MeasurableSet N :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball x _) isOpen_Ioo).measurableSet
  have hNO : N ⊆ O := by
    rintro z ⟨hz1, hz2, hz3⟩
    refine ⟨?_, ?_, ?_⟩
    · have hz1' : vec3EuclideanNorm (z.1 - x) < r' := hz1
      change vec3EuclideanNorm (z.1 - x) < 1 / 2
      linarith only [hz1', hr'q]
    · linarith only [hz2, hr'sq, hσq]
    · linarith only [hz3, hr'sq, hσq]
  have hNzero : ∀ z ∈ N, ω z = 0 := by
    rintro ⟨y, s⟩ ⟨hy, hs1, hs2⟩
    refine htop s ⟨by linarith only [hs1, hr'sq], by linarith only [hs2, hr'sq]⟩ y ?_
    have htri := htriangle y x x'
    have hy' : vec3EuclideanNorm (y - x) < r' := hy
    change vec3EuclideanNorm (y - x') < 1 / 4
    linarith only [htri, hy', hr'q, hxx']
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (hNO.trans hOQ) hωae,
    ae_restrict_mem hNmeas] with z hz hzN
  rw [← hz]
  exact hNzero z hzN

end ESS
