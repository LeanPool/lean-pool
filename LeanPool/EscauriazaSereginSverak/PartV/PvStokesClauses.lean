/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PvStokesForce
public import LeanPool.EscauriazaSereginSverak.PartV.PvStokesResponse
public import LeanPool.EscauriazaSereginSverak.PartV.PvStokesUniqueness
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionPairing

/-!
# The equation, the time derivative and uniqueness in `lem:pv-stokes`

For the zero-data Stokes response `z = forcedHeat G` of a tensor `F` on `Q_τ`,
with `G = Fᵀ - q I` and `q = -P[F]`:

* `z` solves `∂ₜz - Δz = div F - ∇q` in the sense of distributions on `Q_τ`, with
  `(div F)_j = ∑_i ∂_i F_ij`;
* against divergence-free tests, `∂ₜz = div H` with `H = ∇z + F ∈ L²(Q_τ)`, which
  is the membership `∂ₜz ∈ L²(0, τ; V')`;
* every square-integrable distributional solution with the same pressure and a
  zero weak initial trace coincides with `z` almost everywhere on `Q_τ`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A component of a vector test compactly supported in `Q_τ` is a scalar test
compactly supported in `Q_τ`. -/
theorem pvStokes_component_mem {τ : ℝ} {φ : ParabolicPoint → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ)) (i : Fin 3) :
    (fun y => φ y i) ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ) :=
  ⟨contDiff_pi.1 hφ.1 i, hφ.2.1.comp_left (g := fun v : Vec3 => v i) rfl,
    (tsupport_comp_subset (g := fun v : Vec3 => v i) rfl (fun p : Vec3 × ℝ => φ p)).trans hφ.2.2⟩

/-- The backward heat operator of a test compactly supported in `Q_τ` is square
integrable on `Q_τ`. -/
theorem pvStokes_testOp_memLp {τ : ℝ} {φ : ParabolicPoint → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ)) :
    MemLp (fun p => -timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  have hT := spaceTimeTest_derivs_memLp_two hφ.1 hφ.2.1 τ
  have hS (j : Fin 3) := (spaceTimeTest_derivs_memLp_two (pvStokes_spatialPartial_mem hφ j).1
    (pvStokes_spatialPartial_mem hφ j).2.1 τ).2 j
  exact hT.1.neg.sub (memLp_finsetSum (f := fun j p => spatialSecondPartial φ j j p) _
    fun j _ => hS j)

/-- The pairing of a square-integrable field with the backward heat operator of a
vector test is integrable on `Q_τ`. -/
theorem pvStokes_pairing_integrable {τ : ℝ} {z : ParabolicPoint → Vec3}
    (hz : MemLp z 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    {φ : ParabolicPoint → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ)) :
    Integrable (fun p => ∑ i : Fin 3, z p i * (-timePartial (fun y => φ y i) p -
        ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
  integrable_finsetSum _ fun i _ =>
    (memLp_pi_iff.1 hz i).integrable_mul (pvStokes_testOp_memLp (pvStokes_component_mem hφ i))

/-- Uniqueness: two square-integrable distributional solutions of the same
system on `Q_τ` with zero weak initial traces coincide almost everywhere. -/
theorem pvStokes_unique_of_eq {τ : ℝ} (hτ : 0 < τ) {z z' : ParabolicPoint → Vec3}
    (R : (ParabolicPoint → Vec3) → ℝ)
    (hz : MemLp z 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hz' : MemLp z' 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hzeq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z p i *
        (-timePartial (fun y => φ y i) p -
          ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) = R φ)
    (hz'eq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z' p i *
        (-timePartial (fun y => φ y i) p -
          ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) = R φ)
    (hztr : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, ∑ i : Fin 3, z (x, t) i * ψ x i)
    (hz'tr : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, ∑ i : Fin 3, z' (x, t) i * ψ x i) :
    z' =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))] z := by
  have hw : MemLp (fun p : Vec3 × ℝ => z' p - z p) 2 (volume.restrict (vlSlab 0 τ)) :=
    hz'.sub hz
  have hweakP : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, (z' p i - z p i) *
        (-timePartial (fun y => φ y i) p -
          ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) = 0 := by
    intro φ hφ
    have h1 := pvStokes_pairing_integrable hz hφ
    have h2 := pvStokes_pairing_integrable hz' hφ
    have hpt : (fun p : ParabolicPoint => ∑ i : Fin 3, (z' p i - z p i) *
        (-timePartial (fun y => φ y i) p -
          ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p)) =
        fun p => (∑ i : Fin 3, z' p i * (-timePartial (fun y => φ y i) p -
          ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p)) -
          ∑ i : Fin 3, z p i * (-timePartial (fun y => φ y i) p -
            ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) := by
      funext p
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hpt, integral_sub h2 h1, hz'eq φ hφ, hzeq φ hφ, sub_self]
  have htrP : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
        ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)),
          c t = ∫ x, ∑ i : Fin 3, (z' (x, t) i - z (x, t) i) * ψ x i := by
    intro ψ hψ hψc
    obtain ⟨c, hc, hc0, hct⟩ := hztr ψ hψ hψc
    obtain ⟨c', hc', hc'0, hc't⟩ := hz'tr ψ hψ hψc
    refine ⟨fun t => c' t - c t, hc'.sub hc, by simp only [hc0, hc'0, sub_zero], ?_⟩
    have hs := serrin_slice_memLp_ae (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top hz
    have hs' := serrin_slice_memLp_ae (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top hz'
    have hψi (i : Fin 3) : Continuous (fun x => ψ x i) := (continuous_apply i).comp hψ.continuous
    have hψic (i : Fin 3) : HasCompactSupport (fun x => ψ x i) :=
      hψc.comp_left (g := fun v : Vec3 => v i) rfl
    filter_upwards [hct, hc't, hs, hs'] with t ht ht' hst hst'
    have hI (v : Vec3 → Vec3) (hv : MemLp v 2 volume) :
        Integrable (fun x => ∑ i : Fin 3, v x i * ψ x i) :=
      integrable_finsetSum _ fun i _ => integrable_mul_of_memLp_two_of_hasCompactSupport
        (memLp_pi_iff.1 hv i) (hψi i) (hψic i)
    rw [ht, ht', ← integral_sub (hI _ hst') (hI _ hst)]
    congr 1
    funext x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero := pvStokes_heat_unique hτ hw (fun φ hφ => hweakP φ hφ)
    (fun ψ hψ hψc => htrP ψ hψ hψc)
  filter_upwards [hzero] with p hp
  exact sub_eq_zero.1 hp

/-- The weak initial trace of the forced heat response vanishes. -/
theorem pvStokes_forcedHeat_trace {τ : ℝ} (hτ : 0 < τ)
    {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hsupp : ∀ i j z, z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0)
    (ψ : Vec3 → Vec3) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, ∑ i : Fin 3, forcedHeat G (x, t) i * ψ x i := by
  obtain ⟨-, hcont, h0⟩ := forcedHeat_pairing_continuous hτ hG hsupp hψ hψc
  exact ⟨_, hcont, h0, Eventually.of_forall fun _ => rfl⟩

section

variable {τ : ℝ} {F : Fin 3 → Fin 3 → ParabolicPoint → ℝ}

/-- The pointwise form of `-∑_ij G_ij ∂_j φ_i` on the slab. -/
theorem pvStokesForce_pairing_eq {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) (a : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, pvStokesForce τ F i j z * a i j =
      ∑ i : Fin 3, ∑ j : Fin 3, F i j z * a j i - pvStokesPressureSlab τ F z * ∑ j : Fin 3, a j j := by
  simp only [pvStokesForce_of_mem hz, Fin.sum_univ_three]
  simp
  ring

/-- The Stokes response solves `∂ₜz - Δz = div F - ∇q` in the sense of
distributions on `Q_τ`, given the componentwise distributional heat system. -/
theorem pvStokes_equation {z : ParabolicPoint → Vec3}
    (hz : MemLp z 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hG2 : ∀ i j, MemLp (pvStokesForce τ F i j) 2 volume)
    (hcomp : ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ), ∀ i : Fin 3,
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        z p i * (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
      -∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        ∑ j : Fin 3, pvStokesForce τ F i j p * spatialPartial φ j p)
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ)) :
    ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z p i *
        (-timePartial (fun y => φ y i) p -
          ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) =
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        (-(∑ i : Fin 3, ∑ j : Fin 3, F i j p * spatialPartial (fun y => φ y j) i p) +
          pvStokesPressureSlab τ F p * ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p) := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  have hφi (i : Fin 3) := pvStokes_component_mem hφ i
  have hT (i : Fin 3) := spaceTimeTest_derivs_memLp_two (hφi i).1 (hφi i).2.1 τ
  have hLi (i : Fin 3) : Integrable (fun p => z p i * (-timePartial (fun y => φ y i) p -
      ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p)) (volume.restrict Q) :=
    (memLp_pi_iff.1 hz i).integrable_mul (pvStokes_testOp_memLp (hφi i))
  have hRi (i : Fin 3) : Integrable (fun p => ∑ j : Fin 3,
      pvStokesForce τ F i j p * spatialPartial (fun y => φ y i) j p) (volume.restrict Q) :=
    integrable_finsetSum _ fun j _ => ((hG2 i j).restrict _).integrable_mul ((hT i).2 j)
  rw [integral_finsetSum _ fun i _ => hLi i, Finset.sum_congr rfl fun i _ => hcomp _ (hφi i) i,
    Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hRi i, ← integral_neg]
  refine setIntegral_congr_fun (pvStokes_slab_measurableSet τ) fun p hp => ?_
  have h := pvStokesForce_pairing_eq (F := F) hp
    (fun i j => spatialPartial (fun y => φ y i) j p)
  rw [h, Finset.sum_comm (f := fun i j => F i j p * spatialPartial (fun y => φ y j) i p)]
  ring

/-- The time derivative of the Stokes response against divergence-free tests:
`∫ z · ∂ₜφ = ∫ ∑_ij H_ij ∂_i φ_j` with `H_ij = ∂_i z_j + F_ij`, given the
componentwise heat system in gradient form. -/
theorem pvStokes_timeDerivative {z : ParabolicPoint → Vec3}
    {DZ : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hz : MemLp z 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hDZ : ∀ i j, MemLp (DZ i j) 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hG2 : ∀ i j, MemLp (pvStokesForce τ F i j) 2 volume)
    (hgrad : ∀ φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 τ), ∀ i : Fin 3,
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        (-(z p i * timePartial φ p) +
          ∑ j : Fin 3, DZ i j p * spatialPartial φ j p +
          ∑ j : Fin 3, pvStokesForce τ F i j p * spatialPartial φ j p) = 0)
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ))
    (hdiv : ∀ p : ParabolicPoint, ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p = 0) :
    ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        ∑ j : Fin 3, z p j * timePartial (fun y => φ y j) p =
      ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        ∑ i : Fin 3, ∑ j : Fin 3, (DZ j i p + F i j p) * spatialPartial (fun y => φ y j) i p := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  have hφi (i : Fin 3) := pvStokes_component_mem hφ i
  have hT (i : Fin 3) := spaceTimeTest_derivs_memLp_two (hφi i).1 (hφi i).2.1 τ
  have hA (i : Fin 3) : Integrable (fun p => z p i * timePartial (fun y => φ y i) p)
      (volume.restrict Q) := (memLp_pi_iff.1 hz i).integrable_mul (hT i).1
  have hB (i : Fin 3) : Integrable (fun p => ∑ j : Fin 3, DZ i j p *
      spatialPartial (fun y => φ y i) j p) (volume.restrict Q) :=
    integrable_finsetSum _ fun j _ => (hDZ i j).integrable_mul ((hT i).2 j)
  have hC (i : Fin 3) : Integrable (fun p => ∑ j : Fin 3, pvStokesForce τ F i j p *
      spatialPartial (fun y => φ y i) j p) (volume.restrict Q) :=
    integrable_finsetSum _ fun j _ => ((hG2 i j).restrict _).integrable_mul ((hT i).2 j)
  have hrow (i : Fin 3) : ∫ p in Q, z p i * timePartial (fun y => φ y i) p =
      ∫ p in Q, (∑ j : Fin 3, DZ i j p * spatialPartial (fun y => φ y i) j p +
        ∑ j : Fin 3, pvStokesForce τ F i j p * spatialPartial (fun y => φ y i) j p) := by
    have h := hgrad _ (hφi i) i
    have hA' : Integrable (fun p => -(z p i * timePartial (fun y => φ y i) p))
        (volume.restrict Q) := (hA i).neg
    have hAB : Integrable (fun p => -(z p i * timePartial (fun y => φ y i) p) +
        ∑ j : Fin 3, DZ i j p * spatialPartial (fun y => φ y i) j p) (volume.restrict Q) :=
      hA'.add (hB i)
    rw [integral_add hAB (hC i), integral_add hA' (hB i), integral_neg] at h
    rw [integral_add (hB i) (hC i)]
    linarith only [h]
  have hBC (i : Fin 3) : Integrable (fun p => ∑ j : Fin 3, DZ i j p *
      spatialPartial (fun y => φ y i) j p + ∑ j : Fin 3, pvStokesForce τ F i j p *
        spatialPartial (fun y => φ y i) j p) (volume.restrict Q) := (hB i).add (hC i)
  rw [integral_finsetSum _ fun i _ => hA i, Finset.sum_congr rfl fun i _ => hrow i,
    ← integral_finsetSum _ fun i _ => hBC i]
  refine setIntegral_congr_fun (pvStokes_slab_measurableSet τ) fun p hp => ?_
  have h := pvStokesForce_pairing_eq (F := F) hp
    (fun i j => spatialPartial (fun y => φ y i) j p)
  rw [Finset.sum_add_distrib, h, hdiv p, mul_zero, sub_zero]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => DZ j i p * spatialPartial (fun y => φ y j) i p)]

end

end ESS

end
