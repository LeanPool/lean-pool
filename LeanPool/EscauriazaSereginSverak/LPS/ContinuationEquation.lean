/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationCutoff
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGlue
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationTestField
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# Boundary terms of the momentum equation

The weak momentum equation tested with a time cutoff picks up a boundary term
at the cut; this module identifies it through the slice pairing of the velocity
with the test field (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The integrand of the weak momentum equation of a strong solution tested with a
vector field `φ`. -/
@[expose] def lpsEqIntegrand (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (φ : Vec3 × ℝ → Vec3) (z : ParabolicPoint) : ℝ :=
  (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
    - ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * spatialPartial (fun y => φ y i) j z
    + ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * spatialPartial (fun y => φ y i) j z
    - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z

/-- Multiplying the test field by a smooth function of time adds only the
boundary pairing to the equation integrand. -/
theorem lps_eqIntegrand_cutoff {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → Vec3} {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : ParabolicPoint) :
    lpsEqIntegrand u Du p (fun y => η y.2 • φ y) z =
      η z.2 * lpsEqIntegrand u Du p φ z -
        deriv η z.2 * ∑ i : Fin 3, u z i * φ z i := by
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => φ y i) :=
    contDiff_pi.mp hφ i
  have hT (i : Fin 3) : timePartial (fun y : ParabolicPoint => η y.2 * φ y i) z =
      deriv η z.2 * φ z i + η z.2 * timePartial (fun y => φ y i) z :=
    lps_cutoff_timePartial hη (hφi i) z
  have hS (i j : Fin 3) : spatialPartial (fun y : ParabolicPoint => η y.2 * φ y i) j z =
      η z.2 * spatialPartial (fun y => φ y i) j z :=
    lps_cutoff_spatialPartial (η := η) (hφi i) j z
  unfold lpsEqIntegrand
  simp only [Pi.smul_apply, smul_eq_mul, hT, hS]
  have e1 : ∑ i : Fin 3, u z i * (deriv η z.2 * φ z i + η z.2 * timePartial (fun y => φ y i) z) =
      deriv η z.2 * ∑ i : Fin 3, u z i * φ z i +
        η z.2 * ∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * (η z.2 * spatialPartial (fun y => φ y i) j z) =
      η z.2 * ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * spatialPartial (fun y => φ y i) j z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * (η z.2 * spatialPartial (fun y => φ y i) j z) =
      η z.2 * ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * spatialPartial (fun y => φ y i) j z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ i : Fin 3, η z.2 * spatialPartial (fun y => φ y i) i z =
      η z.2 * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z := by
    rw [Finset.mul_sum]
  rw [e1, e2, e3, e4]
  ring

/-- The equation integrand of a strong solution tested with a test field is
integrable on the slab, and so is the pairing of the velocity with the field. -/
theorem lps_eqIntegrand_integrable {a b a₀ c : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a₀ c)) :
    Integrable (fun q : Vec3 × ℝ => lpsEqIntegrand u Du p φ (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) ∧
    Integrable (fun q : Vec3 × ℝ => ∑ i : Fin 3, u (parabolicHomeomorph.symm q) i * φ q i)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  obtain ⟨hφs, hφc, -⟩ := hφ
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) with hν
  have huν : ∀ i : Fin 3, MemLp (fun q : Vec3 × ℝ => u (parabolicHomeomorph.symm q) i) 2 ν :=
    fun i => lps_memLp_slab_to_prod (memLp_pi_iff.1 hu i)
  have hDuν : ∀ i j : Fin 3,
      MemLp (fun q : Vec3 × ℝ => Du (parabolicHomeomorph.symm q) i j) 2 ν :=
    fun i j => lps_memLp_slab_to_prod (memLp_pi_iff.1 (memLp_pi_iff.1 hDu i) j)
  have hpν : MemLp (fun q : Vec3 × ℝ => p (parabolicHomeomorph.symm q)) 2 ν :=
    lps_memLp_slab_to_prod hp
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => φ y i) :=
    contDiff_pi.mp hφs i
  have hφic (i : Fin 3) : HasCompactSupport (fun y : Vec3 × ℝ => φ y i) :=
    hφc.comp_left (g := fun v : Vec3 => v i) (by simp)
  have hbd : ∀ {g : Vec3 × ℝ → ℝ}, Continuous g → HasCompactSupport g →
      ∃ C : ℝ, ∀ q, ‖g q‖ ≤ C := fun hg hk => hg.bounded_above_of_compact_support hk
  have t1 (i : Fin 3) : Integrable (fun q : Vec3 × ℝ => u (parabolicHomeomorph.symm q) i *
      timePartial (fun y => φ y i) q) ν := by
    obtain ⟨hc, hk⟩ := lps_timePartial_cont_compact (hφi i) (hφic i)
    exact (huν i).integrable_mul (q := 2) (hc.memLp_of_hasCompactSupport hk)
  have t2 (i j : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm q) i * u (parabolicHomeomorph.symm q) j *
        spatialPartial (fun y => φ y i) j q) ν := by
    obtain ⟨hc, hk⟩ := lps_spatialPartial_cont_compact (hφi i) (hφic i) j
    obtain ⟨C, hC⟩ := hbd hc hk
    exact ((huν i).integrable_mul (huν j)).mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall hC)
  have t3 (i j : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      Du (parabolicHomeomorph.symm q) i j * spatialPartial (fun y => φ y i) j q) ν := by
    obtain ⟨hc, hk⟩ := lps_spatialPartial_cont_compact (hφi i) (hφic i) j
    exact (hDuν i j).integrable_mul (q := 2) (hc.memLp_of_hasCompactSupport hk)
  have t4 (i : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      p (parabolicHomeomorph.symm q) * spatialPartial (fun y => φ y i) i q) ν := by
    obtain ⟨hc, hk⟩ := lps_spatialPartial_cont_compact (hφi i) (hφic i) i
    exact hpν.integrable_mul (q := 2) (hc.memLp_of_hasCompactSupport hk)
  have t5 (i : Fin 3) : Integrable (fun q : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm q) i * φ q i) ν :=
    (huν i).integrable_mul (q := 2) ((hφi i).continuous.memLp_of_hasCompactSupport (hφic i))
  refine ⟨?_, integrable_finsetSum _ fun i _ => t5 i⟩
  have hsum : (fun q : Vec3 × ℝ => lpsEqIntegrand u Du p φ (parabolicHomeomorph.symm q)) =
      fun q => (-(∑ i : Fin 3, u (parabolicHomeomorph.symm q) i *
            timePartial (fun y => φ y i) q))
        - ∑ i : Fin 3, ∑ j : Fin 3, u (parabolicHomeomorph.symm q) i *
            u (parabolicHomeomorph.symm q) j * spatialPartial (fun y => φ y i) j q
        + ∑ i : Fin 3, ∑ j : Fin 3, Du (parabolicHomeomorph.symm q) i j *
            spatialPartial (fun y => φ y i) j q
        - ∑ i : Fin 3, p (parabolicHomeomorph.symm q) * spatialPartial (fun y => φ y i) i q := by
    funext q
    unfold lpsEqIntegrand
    rw [Finset.mul_sum]
    rfl
  rw [hsum]
  exact ((((integrable_finsetSum _ fun i _ => t1 i).neg).sub
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => t2 i j)).add
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => t3 i j)).sub
    (integrable_finsetSum _ fun i _ => t4 i)

/-- The cutoff-tested equation integral, expressed with the boundary pairing. -/
theorem lps_equation_cutoff_integral {a b a₀ c : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {S : (Vec3 × ℝ → Vec3) → Prop}
    (hS : ∀ (φ : Vec3 × ℝ → Vec3) (η : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → S φ →
      S (fun z => η z.2 • φ z))
    (hEq : ∀ ψ : Vec3 × ℝ → Vec3,
      ψ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) → S ψ →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), lpsEqIntegrand u Du p ψ z = 0)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a₀ c))
    (hSφ : S φ) {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hmem : (fun z : Vec3 × ℝ => η z.2 • φ z) ∈
      spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b)) :
    ∫ q : Vec3 × ℝ,
      (η q.2 * lpsEqIntegrand u Du p φ (parabolicHomeomorph.symm q) -
        deriv η q.2 * ∑ i : Fin 3, u (parabolicHomeomorph.symm q) i * φ q i)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) = 0 := by
  have h := hEq _ hmem (hS φ η hη hSφ)
  rw [lps_setIntegral_slab_to_prod] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  have := lps_eqIntegrand_cutoff (u := u) (Du := Du) (p := p) hη hφ.1 (parabolicHomeomorph.symm q)
  simpa [parabolicHomeomorph_symm_apply] using this.symm

/-- A limit along the closed interval gives the almost-everywhere approximate
form used by the boundary-term lemmas. -/
theorem lps_slice_limit_right {a b ℓ : ℝ} {f : ℝ → ℝ}
    (h : Tendsto f (nhdsWithin b (Icc a b)) (nhds ℓ)) :
    ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)), b - η < t → |f t - ℓ| < δ := by
  intro δ hδ
  obtain ⟨η, hη, hη'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) δ hδ
  refine ⟨η, hη, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht hbt
  have hd : dist t b < η := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2.le)]
    linarith only [hbt]
  have := hη' (show t ∈ Icc a b from ⟨ht.1.le, ht.2.le⟩) hd
  rwa [Real.dist_eq] at this

/-- The left-end version of `lps_slice_limit_right`. -/
theorem lps_slice_limit_left {a b ℓ : ℝ} {f : ℝ → ℝ}
    (h : Tendsto f (nhdsWithin a (Icc a b)) (nhds ℓ)) :
    ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)), t < a + η → |f t - ℓ| < δ := by
  intro δ hδ
  obtain ⟨η, hη, hη'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) δ hδ
  refine ⟨η, hη, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht hbt
  have hd : dist t a < η := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
    linarith only [hbt]
  have := hη' (show t ∈ Icc a b from ⟨ht.1.le, ht.2.le⟩) hd
  rwa [Real.dist_eq] at this

/-- Boundary term of the momentum equation at the right end of a slab: if the
equation holds for the test fields supported inside the slab, then tested with a
field that need not vanish at the end time it equals minus the slice pairing at
that time (`lem:lps-continuation`). -/
theorem lps_equation_boundary_right {a b c ℓ : ℝ} (hab : a < b)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {S : (Vec3 × ℝ → Vec3) → Prop}
    (hS : ∀ (φ : Vec3 × ℝ → Vec3) (η : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → S φ →
      S (fun z => η z.2 • φ z))
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hEq : ∀ ψ : Vec3 × ℝ → Vec3,
      ψ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) → S ψ →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), lpsEqIntegrand u Du p ψ z = 0)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a c))
    (hSφ : S φ)
    (hG : ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)), b - η < t →
      |(∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, t) i) - ℓ| < δ) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), lpsEqIntegrand u Du p φ z = -ℓ := by
  obtain ⟨hF1, hF2⟩ := lps_eqIntegrand_integrable hu hDu hp hφ
  rw [lps_setIntegral_slab_to_prod]
  refine lps_endpoint_boundary_right hab hF1 hF2 ?_ hG
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hηs : tsupport (lpsCutoffRight b ε) ⊆ Iic (b - ε) := by
    refine closure_minimal ?_ isClosed_Iic
    intro t ht
    by_contra hnot
    exact ht (lpsCutoffRight_eq_zero hε0 (le_of_lt (not_le.mp hnot)))
  have hmem := lps_cutoff_test_mem_right (β := b - ε) (b := b) hφ
    (lpsCutoffRight_contDiff b ε) hηs (by linarith only [hε0])
  exact lps_equation_cutoff_integral hS hEq hφ hSφ (lpsCutoffRight_contDiff b ε) hmem

/-- Boundary term of the momentum equation at the left end of a slab
(`lem:lps-continuation`). -/
theorem lps_equation_boundary_left {a b ℓ : ℝ} (hab : a < b)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {S : (Vec3 × ℝ → Vec3) → Prop}
    (hS : ∀ (φ : Vec3 × ℝ → Vec3) (η : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → S φ →
      S (fun z => η z.2 • φ z))
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hp : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hEq : ∀ ψ : Vec3 × ℝ → Vec3,
      ψ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) → S ψ →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), lpsEqIntegrand u Du p ψ z = 0)
    {φ : Vec3 × ℝ → Vec3} {a₀ : ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a₀ b))
    (hSφ : S φ)
    (hG : ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)), t < a + η →
      |(∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, t) i) - ℓ| < δ) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), lpsEqIntegrand u Du p φ z = ℓ := by
  obtain ⟨hF1, hF2⟩ := lps_eqIntegrand_integrable hu hDu hp hφ
  rw [lps_setIntegral_slab_to_prod]
  refine lps_endpoint_boundary_left hab hF1 hF2 ?_ hG
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hηs : tsupport (lpsCutoffLeft a ε) ⊆ Ici (a + ε) := by
    refine closure_minimal ?_ isClosed_Ici
    intro t ht
    by_contra hnot
    exact ht (lpsCutoffLeft_eq_zero hε0 (le_of_lt (not_le.mp hnot)))
  have hmem := lps_cutoff_test_mem_left (α := a + ε) (b := a) hφ
    (lpsCutoffLeft_contDiff a ε) hηs (by linarith only [hε0])
  exact lps_equation_cutoff_integral hS hEq hφ hSφ (lpsCutoffLeft_contDiff a ε) hmem

end ESS

end
