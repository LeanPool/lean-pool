/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyScalarEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTestOperators

/-!
# Components of the localized vorticity equation

Testing the vector equation of `lem:localized-vorticity-energy` with a test
in a single coordinate direction gives, for each component, a scalar heat
equation with divergence-form source
`Hⱼ = Fⱼᵢ + Gⱼᵢ - (vⱼ zᵢ - zⱼ vᵢ)` and source `g₀ᵢ`. For measurable data this is
a `VlHeatSolution`.
-/

public section

open CKN

open MeasureTheory Set Filter


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

private theorem vl_timePartial_const_mul {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (c : ℝ) (p : Vec3 × ℝ) :
    CKN.timePartial (fun q : Vec3 × ℝ => c * φ q) p = c * CKN.timePartial φ p := by
  unfold CKN.timePartial
  have hd : DifferentiableAt ℝ (fun s : ℝ => φ (p.1, s)) p.2 :=
    ((hφ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
  change fderiv ℝ (fun s : ℝ => c * φ (p.1, s)) p.2 1 = _
  rw [fderiv_const_mul hd]
  rfl

private theorem vl_spatialPartial_const_mul {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (c : ℝ) (j : Fin 3) (p : Vec3 × ℝ) :
    CKN.spatialPartial (fun q : Vec3 × ℝ => c * φ q) j p = c * CKN.spatialPartial φ j p := by
  unfold CKN.spatialPartial
  have hd : DifferentiableAt ℝ (fun x : Vec3 => φ (x, p.2)) p.1 :=
    ((hφ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  change fderiv ℝ (fun x : Vec3 => c * φ (x, p.2)) p.1 (CKN.basisVec j) = _
  rw [fderiv_const_mul hd]
  rfl

private theorem vl_spatialPartial_contDiff {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) := by
  have h := (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (contDiff_const (c := ((CKN.basisVec j, (0 : ℝ)) : Vec3 × ℝ)))
  have heq : (fun p : Vec3 × ℝ => CKN.spatialPartial φ j p) =
      fun p => (fderiv ℝ φ p) ((CKN.basisVec j, (0 : ℝ)) : Vec3 × ℝ) := by
    funext p
    exact CKN.spatialPartial_eq_joint_fderiv hφ p j
  rw [heq]
  exact h

private theorem vl_spatialSecondPartial_const_mul {φ : Vec3 × ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (c : ℝ) (j : Fin 3) (p : Vec3 × ℝ) :
    CKN.spatialSecondPartial (fun q : Vec3 × ℝ => c * φ q) j j p =
      c * CKN.spatialSecondPartial φ j j p := by
  unfold CKN.spatialSecondPartial
  have hin : (fun w : ParabolicPoint => CKN.spatialPartial (fun q : Vec3 × ℝ => c * φ q) j w) =
      fun w : ParabolicPoint => c * CKN.spatialPartial φ j w := by
    funext w
    exact vl_spatialPartial_const_mul hφ c j w
  rw [hin]
  exact vl_spatialPartial_const_mul (vl_spatialPartial_contDiff hφ j) c j p

/-- The single-direction vector test. -/
@[expose] def vlDirTest (i : Fin 3) (φ : Vec3 × ℝ → ℝ) : Vec3 × ℝ → Vec3 :=
  fun p => φ p • (Pi.single i (1 : ℝ) : Vec3)

theorem vlDirTest_mem {a τ : ℝ} (i : Fin 3) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ)) :
    vlDirTest i φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (univ : Set Vec3) (Ioo a τ) := by
  refine ⟨hφ.1.smul contDiff_const, hφ.2.1.smul_right, ?_⟩
  exact (tsupport_smul_subset_left φ _).trans hφ.2.2

theorem vlDirTest_apply (i : Fin 3) (φ : Vec3 × ℝ → ℝ) (p : Vec3 × ℝ) (k : Fin 3) :
    vlDirTest i φ p k = (Pi.single i (1 : ℝ) : Vec3) k * φ p := by
  simp [vlDirTest, mul_comm]

/-- The scalar weak equation for one component. -/
theorem vlVectorWeak_component {a τ : ℝ} {z v g₀ : Vec3 × ℝ → Vec3}
    {F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    (hweak : (∀ φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (univ : Set Vec3) (Ioo a τ),
      ∫ p in vlSlab a τ, ∑ i : Fin 3, z p i *
          (-vorticityTestTimeDerivative φ p i - vorticityTestLaplacian φ p i) =
        ∫ p in vlSlab a τ, (∑ j : Fin 3, ∑ i : Fin 3,
          (v p j * z p i - z p j * v p i - F p j i - G p j i) *
            CKN.spatialPartial (fun q : Vec3 × ℝ => φ q i) j p +
          ∑ i : Fin 3, g₀ p i * φ p i))) (i : Fin 3)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ)) :
    ∫ p in vlSlab a τ, z p i * (-CKN.timePartial φ p -
        ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) =
      ∫ p in vlSlab a τ, (-(∑ j : Fin 3, (F p j i + G p j i - (v p j * z p i - z p j * v p i)) *
        CKN.spatialPartial φ j p) + g₀ p i * φ p) := by
  have h := hweak (vlDirTest i φ) (vlDirTest_mem i hφ)
  have hcomp : ∀ k : Fin 3, (fun q : Vec3 × ℝ => vlDirTest i φ q k) =
      fun q => (Pi.single i (1 : ℝ) : Vec3) k * φ q := fun k => by
    funext q
    exact vlDirTest_apply i φ q k
  have hL : ∀ p : Vec3 × ℝ, ∑ k : Fin 3, z p k *
      (-vorticityTestTimeDerivative (vlDirTest i φ) p k -
        vorticityTestLaplacian (vlDirTest i φ) p k) =
      z p i * (-CKN.timePartial φ p - ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) := by
    intro p
    have hk : ∀ k : Fin 3, z p k * (-vorticityTestTimeDerivative (vlDirTest i φ) p k -
        vorticityTestLaplacian (vlDirTest i φ) p k) =
        (Pi.single i (1 : ℝ) : Vec3) k * (z p k * (-CKN.timePartial φ p -
          ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p)) := by
      intro k
      have ht : vorticityTestTimeDerivative (vlDirTest i φ) p k =
          (Pi.single i (1 : ℝ) : Vec3) k * CKN.timePartial φ p := by
        change CKN.timePartial (fun q : Vec3 × ℝ => vlDirTest i φ q k) p = _
        rw [hcomp k]
        exact vl_timePartial_const_mul hφ.1 _ p
      have hl : vorticityTestLaplacian (vlDirTest i φ) p k =
          (Pi.single i (1 : ℝ) : Vec3) k * ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p := by
        change ∑ j : Fin 3, CKN.spatialSecondPartial (fun q : Vec3 × ℝ => vlDirTest i φ q k)
          j j p = _
        rw [hcomp k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => vl_spatialSecondPartial_const_mul hφ.1 _ j p
      rw [ht, hl]
      ring
    simp_rw [hk]
    simp [Pi.single_apply]
  have hR : ∀ p : Vec3 × ℝ, (∑ j : Fin 3, ∑ k : Fin 3,
      (v p j * z p k - z p j * v p k - F p j k - G p j k) *
        CKN.spatialPartial (fun q : Vec3 × ℝ => vlDirTest i φ q k) j p +
      ∑ k : Fin 3, g₀ p k * vlDirTest i φ p k) =
      -(∑ j : Fin 3, (F p j i + G p j i - (v p j * z p i - z p j * v p i)) *
        CKN.spatialPartial φ j p) + g₀ p i * φ p := by
    intro p
    have hsp : ∀ j k : Fin 3, CKN.spatialPartial (fun q : Vec3 × ℝ => vlDirTest i φ q k) j p =
        (Pi.single i (1 : ℝ) : Vec3) k * CKN.spatialPartial φ j p := fun j k => by
      rw [hcomp k]
      exact vl_spatialPartial_const_mul hφ.1 _ j p
    simp_rw [hsp, vlDirTest_apply]
    simp only [Pi.single_apply, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  simp_rw [hL, hR] at h
  exact h

/-- The trace of one component. -/
theorem vlVectorTrace_component {a τ : ℝ} {z : Vec3 × ℝ → Vec3} {z₀ : Vec3 → Vec3}
    (htrace : (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc a τ) ∧ c a = ∫ x, ∑ i : Fin 3, z₀ x i * ψ x i ∧
        ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = ∫ x, ∑ i : Fin 3, z (x, t) i * ψ x i))
    (i : Fin 3) {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∃ c : ℝ → ℝ, ContinuousOn c (Icc a τ) ∧ c a = ∫ x, z₀ x i * ψ x ∧
      ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = ∫ x, z (x, t) i * ψ x := by
  obtain ⟨c, hc, hca, hct⟩ := htrace (fun x => ψ x • (Pi.single i (1 : ℝ) : Vec3))
    (hψ.smul contDiff_const) hψc.smul_right
  have hsum : ∀ u : Vec3, ∀ x, ∑ k : Fin 3, u k * (ψ x • (Pi.single i (1 : ℝ) : Vec3)) k =
      u i * ψ x := fun u x => by
    simp [Pi.single_apply, mul_comm]
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hca]
    congr 1
    funext x
    exact hsum (z₀ x) x
  · filter_upwards [hct] with t ht
    rw [ht]
    congr 1
    funext x
    exact hsum (z (x, t)) x

/-- Slices of almost everywhere equal slab fields are almost everywhere equal
for almost every time. -/
theorem vlSlab_slice_ae_eq {a τ : ℝ} {g g' : Vec3 × ℝ → ℝ}
    (h : g =ᵐ[volume.restrict (vlSlab a τ)] g') :
    ∀ᵐ t ∂(volume.restrict (Ioo a τ)), (fun x => g (x, t)) =ᵐ[volume] fun x => g' (x, t) := by
  rw [vlSlab_measure] at h
  have hswap := (Measure.measurePreserving_swap (μ := volume.restrict (Ioo a τ))
    (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae_eq_comp h
  exact Measure.ae_ae_of_ae_prod hswap

end ESS

end
