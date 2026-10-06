/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundLocal
public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundTail
public import LeanPool.CaffarelliKohnNirenberg.Statements.AssociatedPressure

/-!
# A global bound on positive-time slabs

This file proves `lem:pv-positive-bound`: under the critical hypothesis
u ∈ L^∞_t L³_x of `thm:ess-global`, a Leray–Hopf solution on ℝ³ × (0, T) is
essentially bounded on every slab ℝ³ × (δ, T), δ > 0. The local regularity
theorem `thm:ess-local` is assumed in the form of hE1.

The proof fixes the scale R = √δ and, around each point z of the slab, the
backward cylinder of radius R / 4 ending at min (z.2 + R² / 32, T), which
may end at the terminal time. Far from the origin the tails of |u|³ and of
|p|^{3/2} for the canonical pressure of `thm:assoc-pressure` make the
normalized energy small, and `pv_epsilon_bound` gives the bound C / R. On the
bounded part `thm:ess-local` gives local bounds, and a finite subcover of the
compact set closure B × [δ, T] makes them uniform.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A property that holds almost everywhere on a neighbourhood of every point
of a set holds almost everywhere on the set. -/
private theorem pv_ae_of_local {S : Set ParabolicPoint} {P : ParabolicPoint → Prop}
    (h : ∀ z ∈ S, ∃ N : Set (Vec3 × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ᵐ y ∂volume.restrict ((N : Set ParabolicPoint) ∩ S), P y) :
    ∀ᵐ y ∂volume.restrict S, P y := by
  choose! N hNo hzN hNae using h
  let f : S → Set (Vec3 × ℝ) := fun z => N z
  obtain ⟨Tc, hTc, hUnion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable f (fun z => hNo z z.2)
  have hcover : S ⊆ ⋃ i ∈ Tc, ((f i : Set ParabolicPoint) ∩ S) := by
    intro z hz
    have hz' : z ∈ ⋃ i, f i := mem_iUnion.mpr ⟨⟨z, hz⟩, hzN z hz⟩
    rw [← hUnion] at hz'
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz'
    exact mem_iUnion₂.mpr ⟨i, hi, hzi, hz⟩
  have hall : ∀ᵐ y ∂volume.restrict (⋃ i ∈ Tc, ((f i : Set ParabolicPoint) ∩ S)), P y :=
    (ae_restrict_biUnion_iff _ hTc P).mpr (fun i _ => hNae i i.2)
  exact ae_restrict_of_ae_restrict_of_subset hcover hall

/-- A global bound on positive-time slabs, `lem:pv-positive-bound`. -/
theorem pvPositiveBound
    (hE1 : ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
    ∀ p : ParabolicPoint → ℝ,
      AEStronglyMeasurable u
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable Du
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable p
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
        HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) →
      (∀ ψ : ParabolicPoint → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0) →
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
      ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict
            (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
          ParabolicHolderVecOn
            (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ)
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))),
      vec3EuclideanNorm (u z) ≤ B := by
  rcases le_or_gt T δ with hTδ | hδT
  · refine ⟨0, ?_⟩
    have hempty : spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T) = ∅ := by
      rw [Ioo_eq_empty (not_lt.mpr hTδ)]
      exact Set.prod_empty
    rw [hempty, Measure.restrict_empty]
    exact ae_zero.symm ▸ Filter.eventually_bot
  obtain ⟨p, hpMem, hpMom, hpMixed⟩ := associatedPressure T a u Du hLH
  have hPMixed := hpMixed hL3
  have hpLp := pv_pressure_memLp_threeHalves_slab hpMem.aestronglyMeasurable hPMixed
  obtain ⟨η, C, hη, hC, hEps⟩ := pv_epsilon_bound
  set R : ℝ := Real.sqrt δ with hRdef
  have hR : 0 < R := Real.sqrt_pos.mpr hδ
  have hR2 : R ^ 2 = δ := Real.sq_sqrt hδ.le
  have hfin := pv_energyDensity_slab_lt_top hLH.2.2.1 hpMem.aestronglyMeasurable hL3
    hPMixed
  obtain ⟨ρ, hρ⟩ := pv_tail_goodPointEnergy_small hfin
    (ε := ENNReal.ofReal (η * R ^ 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  let t₀ : ParabolicPoint → ℝ := fun z => min (z.2 + R ^ 2 / 32) T
  let N : ParabolicPoint → Set (Vec3 × ℝ) := fun z =>
    vec3Ball z.1 (R * (1 / 4)) ×ˢ Ioo (t₀ z - R ^ 2 * (1 / 16)) (z.2 + R ^ 2 / 32)
  let Cyl : ParabolicPoint → Set ParabolicPoint := fun z =>
    spaceTimeSet (vec3Ball z.1 (R * (1 / 4))) (Ioo (t₀ z - R ^ 2 * (1 / 16)) (t₀ z))
  have hNopen : ∀ z, IsOpen (N z) := fun z => (isOpen_vec3Ball _ _).prod isOpen_Ioo
  have hfacts : ∀ z : ParabolicPoint, δ ≤ z.2 →
      R ^ 2 ≤ t₀ z ∧ t₀ z ≤ T ∧ z ∈ N z ∧
        (N z : Set ParabolicPoint) ∩ spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T) ⊆
          Cyl z := by
    intro z hz
    have hR2pos : 0 < R ^ 2 := by positivity
    have hmin1 : t₀ z ≤ z.2 + R ^ 2 / 32 := min_le_left _ _
    refine ⟨le_min (by linarith only [hR2, hz, hR2pos]) (by linarith only [hR2, hδT]),
      min_le_right _ _, ⟨?_, ?_, ?_⟩, ?_⟩
    · change vec3EuclideanNorm (z.1 - z.1) < R * (1 / 4)
      rw [sub_self, vec3EuclideanNorm_zero]
      positivity
    · linarith only [hmin1, hR2pos]
    · linarith only [hR2pos]
    · rintro y ⟨⟨hy1, hy2⟩, hy3⟩
      exact ⟨hy1, hy2.1, lt_min hy2.2 hy3.2.2⟩
  have hlocal : ∀ z : ParabolicPoint, δ ≤ z.2 →
      ∃ B : ℝ, ∀ᵐ y ∂volume.restrict (Cyl z), vec3EuclideanNorm (u y) ≤ B := by
    intro z hz
    obtain ⟨h1, h2, _, _⟩ := hfacts z hz
    obtain ⟨B, hB⟩ := pv_local_bound_of_essLocal hE1 hLH hpLp hpMom hL3 z.1 hR h1 h2
    refine ⟨B, ae_restrict_of_ae_restrict_of_subset ?_ hB⟩
    rintro y ⟨hy1, hy2⟩
    refine ⟨?_, ?_, hy2.2⟩
    · have hy1' : vec3EuclideanNorm (y.1 - z.1) < R * (1 / 4) := hy1
      change vec3EuclideanNorm (y.1 - z.1) < R * (1 / 2)
      linarith only [hy1', hR]
    · have hR2pos : 0 < R ^ 2 := by positivity
      linarith only [hy2.1, hR2pos]
  have hfar : ∀ z : ParabolicPoint, δ ≤ z.2 → ρ + R / 2 ≤ vec3EuclideanNorm z.1 →
      ∀ᵐ y ∂volume.restrict (Cyl z), vec3EuclideanNorm (u y) ≤ C / R := by
    intro z hz hzfar
    obtain ⟨h1, h2, _, _⟩ := hfacts z hz
    have hsq : (R / 2) ^ 2 ≤ t₀ z := by
      have hR2pos : 0 < R ^ 2 := by positivity
      nlinarith only [h1, hR2pos]
    exact hEps hLH hpLp hpMom hL3 z.1 hR h1 h2 (hρ z.1 (t₀ z) (R / 2) hzfar hsq h2)
  let K : Set (Vec3 × ℝ) := closure (vec3Ball (0 : Vec3) (|ρ| + R / 2)) ×ˢ Icc δ T
  have hK : IsCompact K :=
    (isCompact_closure_vec3Ball (by positivity)).prod isCompact_Icc
  have hKcover : K ⊆ ⋃ z : K, N z.1 := fun z hz =>
    mem_iUnion.mpr ⟨⟨z, hz⟩, (hfacts z hz.2.1).2.2.1⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun z : K => N z.1) (fun z => hNopen z.1)
    hKcover
  choose Bk hBk using fun z : K => hlocal z.1 z.2.2.1
  have hsum : 0 ≤ ∑ i ∈ F, |Bk i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hCR : 0 ≤ C / R := div_nonneg hC hR.le
  refine ⟨C / R + ∑ i ∈ F, |Bk i|, pv_ae_of_local ?_⟩
  intro z hz
  by_cases hzfar : ρ + R / 2 ≤ vec3EuclideanNorm z.1
  · obtain ⟨_, _, hzN, hsub⟩ := hfacts z hz.2.1.le
    refine ⟨N z, hNopen z, hzN, ?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hfar z hz.2.1.le hzfar)]
      with y hy
    linarith only [hy, hsum]
  · have hzK : z ∈ K := by
      refine ⟨subset_closure ?_, hz.2.1.le, hz.2.2.le⟩
      change vec3EuclideanNorm (z.1 - 0) < |ρ| + R / 2
      rw [sub_zero]
      linarith only [hzfar, le_abs_self ρ]
    obtain ⟨i, hiF, hzi⟩ := mem_iUnion₂.mp (hF hzK)
    obtain ⟨_, _, _, hsub⟩ := hfacts i.1 i.2.2.1
    refine ⟨N i.1, hNopen i.1, hzi, ?_⟩
    have hle : |Bk i| ≤ ∑ j ∈ F, |Bk j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (Bk j)) hiF
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hBk i)] with y hy
    linarith only [hy, hle, le_abs_self (Bk i), hCR]

end ESS
