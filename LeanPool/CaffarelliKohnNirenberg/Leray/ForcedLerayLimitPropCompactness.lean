/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitModulus
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitCompactnessInputs
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMain

/-!
# Forced Leray Limit Prop Compactness

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The forced regularized fields have a common local compactness limit on
positive time intervals, as required in `prop:forced-limit`. -/
theorem forcedLerayLimit_local_compactness
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ v : Vec3 × ℝ → Vec3, ∃ g : Vec3 × ℝ → CompactnessGradientFiber,
      Measurable v ∧ Measurable g ∧
      (∀ t : ℝ, 0 < t → ∀ C : Set Vec3, IsCompact C →
        ∃ hs : ∀ k, MemLp
          (fun x : Vec3 => (WithLp.toLp 2
            (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x,t)) : L2Vec3))
          2 (volume.restrict C),
        ∃ hv : MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (v (x,t)) : L2Vec3))
          2 (volume.restrict C),
        ∀ w : Lp L2Vec3 2 (volume.restrict C),
          Tendsto (fun k => inner ℝ ((hs k).toLp
            (fun x => (WithLp.toLp 2
              (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x,t)) : L2Vec3))) w)
            atTop (nhds (inner ℝ (hv.toLp
              (fun x => (WithLp.toLp 2 (v (x,t)) : L2Vec3))) w))) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆
        (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        Tendsto (fun k => eLpNorm
          ((fun z : Vec3 × ℝ => (WithLp.toLp 2
              (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (z.1,z.2)) : L2Vec3)) -
            (fun z : Vec3 × ℝ => (WithLp.toLp 2 (v z) : L2Vec3))) 2
          (volume.restrict Q)) atTop (nhds 0)) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆
        (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        ∃ hs : ∀ k, MemLp
          (fun z => toCompactnessGradientFiber
            (forcedRegGradient ρ a ha f hf (εseq (σ k)) z)) 2
          (volume.restrict Q),
        ∃ hg : MemLp g 2 (volume.restrict Q),
        ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict Q),
          Tendsto (fun k => inner ℝ ((hs k).toLp
            (fun z => toCompactnessGradientFiber
              (forcedRegGradient ρ a ha f hf (εseq (σ k)) z))) w)
            atTop (nhds (inner ℝ (hg.toLp g) w))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => v (x,t) i) (fun x m => g (x,t) i m)) ∧
      (∀ C : Set Vec3, IsCompact C →
        ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
        ∀ M : ℝ≥0∞, M < ⊤ →
          (∀ n t, t ∈ Icc b₁ b₂ →
            (∫⁻ x in C, ENNReal.ofReal
              (vec3EuclideanNorm
                (forcedRegVelocity ρ a ha f hf (εseq n) (x,t))) ^ (2 : ℝ)
              ∂volume) ≤ M) →
          ∀ t ∈ Icc b₁ b₂,
            (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (v (x,t))) ^ (2 : ℝ)
              ∂volume) ≤ M) ∧
      (∀ C : Set Vec3, IsCompact C →
        ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
        ∀ G : ℝ≥0∞, G < ⊤ →
          (∀ n,
            (∫⁻ t in Icc b₁ b₂, ∫⁻ x in C,
              ENNReal.ofReal (spatialGradientSq
                (forcedRegVelocity ρ a ha f hf (εseq n))
                (forcedRegGradient ρ a ha f hf (εseq n)) (x,t))
              ∂volume ∂volume) ≤ G) →
          (∫⁻ t in Icc b₁ b₂, ∫⁻ x in C,
            ENNReal.ofReal (spatialGradientSq
            (fun _ => (0 : Vec3))
            (fun z i j => g z i j) (x,t)) ∂volume ∂volume) ≤ G) ∧
      (∀ z : Vec3 × ℝ, v z = compactnessMollifiedLimit
        (fun n => forcedRegVelocity ρ a ha f hf (εseq n)) σ z) := by
  classical
  let U : ℕ → ParabolicPoint → Vec3 := fun n =>
    forcedRegVelocity ρ a ha f hf (εseq n)
  let D : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n =>
    forcedRegGradient ρ a ha f hf (εseq n)
  have hUmeas : ∀ n, Measurable (U n) := by
    intro n
    rw [show U n = forcedRegVelocity ρ a ha f hf (εseq n) from rfl,
      forcedRegVelocity_eq ρ ha hf (hseq n).1]
    exact (forcedRegRep_stronglyMeasurable ρ (εseq n) (hseq n).1 ha hf).measurable
  have hDmeas : ∀ n, Measurable (D n) := by
    intro n
    change Measurable (forcedMollifiedGrad
      (forcedRegVelocity ρ a ha f hf (εseq n)))
    rw [forcedRegVelocity_eq ρ ha hf (hseq n).1]
    exact measurable_forcedMollifiedGrad
      (forcedRegRep_stronglyMeasurable ρ (εseq n) (hseq n).1 ha hf)
      (fun t i => forcedRegRep_locallyIntegrable ρ (εseq n) (hseq n).1 ha hf t i)
  have hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => U n (x,t) i)
        (fun x => D n (x,t) i) := by
    intro n
    have h := forcedRegRep_weakGradient ρ (εseq n) (hseq n).1 ha hf
    filter_upwards [h] with t ht
    intro i
    simpa [U, D, forcedRegGradient, forcedRegVelocity_eq ρ ha hf (hseq n).1]
      using ht i
  have hbounds := forcedLerayLimit_compactness_bounds
    ρ a ha f hf εseq (fun n => (hseq n).1)
  have hmod₀ := forcedLerayLimit_compactness_modulus
    ρ a ha f hf (forcedRegMomentum ρ a ha f hf) εseq (fun n => (hseq n).1)
  have hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ a' b : ℝ, Icc a' b ⊆ Ioi (0 : ℝ) →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
          ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
            ∀ n s t, s ∈ Icc a' b → t ∈ Icc a' b →
              |(∫ x : Vec3, ∑ i : Fin 3, U n (x,t) i * w x i) -
                ∫ x : Vec3, ∑ i : Fin 3, U n (x,s) i * w x i| ≤
                A * dist t s + B * (dist t s) ^ θ := by
    intro C hC hCU a' b hab w hw hwc hwC
    let T : ℝ := max b 0 + 1
    have hT : 0 < T := by positivity
    have habT : Icc a' b ⊆ Ioo 0 T := by
      intro t ht
      refine ⟨hab ht, ?_⟩
      dsimp [T]
      exact lt_of_le_of_lt (ht.2.trans (le_max_left b 0)) (lt_add_one (max b 0))
    have h := hmod₀ T hT C hC hCU a' b habT w hw hwc hwC
    simpa [U] using h
  let hbound' := compact_time_slice_bounds_of_interval_bounds
    ordConnected_Ioi U hbounds.1
  let hgradBound' := compact_time_gradient_bounds_of_interval_bounds
    ordConnected_Ioi U D hbounds.2
  let hmod' := compact_time_pairing_modulus_of_interval_modulus
    ordConnected_Ioi U hmod
  obtain ⟨K, χ, J, hK, hKcover, hχ, hJ, hJcover,
      hmem, σ, hσ, V, Dlim, hweak, hVcont, huniform, hDweak⟩ :=
    exists_common_velocity_gradient_subsequence isOpen_univ isOpen_Ioi
      U D hUmeas hDmeas hbound' hgradBound' hmod'
  let v : Vec3 × ℝ → Vec3 := compactnessMollifiedLimit U σ
  have hv : Measurable v := measurable_compactnessMollifiedLimit U σ hUmeas
  have hstrongRect := strong_l2_to_compactnessMollifiedLimit_on_exhaustion
    isOpen_univ isOpen_Ioi U D hUmeas hDmeas hweakGrad hbound' hgradBound'
    K χ J hK hKcover hχ
    (fun j => ⟨(hJ j).1, (hJ j).2.1⟩)
    hmem σ V hweak hVcont huniform
  obtain ⟨g, hg, hgEq, hgWeak⟩ :=
    compactness_gradient_limit_of_joint_limits isOpen_univ
      U D v σ K J hK hKcover hJ hJcover hweakGrad Dlim hDweak
      hstrongRect
  refine ⟨σ, hσ, v, g, hv, hg, ?_, ?_, ?_, hgWeak,
    ?_, ?_, ?_⟩
  · intro t ht C hC
    exact weak_slices_to_compactnessMollifiedLimit_on_compact isOpen_Ioi
      U σ hUmeas K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx)
      hbound' hmem V hweak C hC (Set.subset_univ _) ⟨t, ht⟩
  · exact strong_l2_on_compacts_of_exhaustion K J
      (fun j => (hK j).2.2.1) (fun j => (hK j).2.2.2)
      hKcover (fun j => (hJ j).2.2.1) (fun j => (hJ j).2.2.2)
      hJcover (fun k z => (WithLp.toLp 2 (U (σ k) z) : L2Vec3))
      (fun z => (WithLp.toLp 2 (v z) : L2Vec3))
      (fun j => (hstrongRect j).2)
  · intro Q hQ hQI
    exact weak_gradient_to_measurable_limit_on_compact
      D σ K J hK hKcover hJ hJcover Dlim hDweak g hgEq Q hQ hQI
  · intro C hC b₁ b₂ hI M hM hsource t ht
    exact compactness_limit_slice_bound isOpen_Ioi U σ hUmeas K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx) hbound' hmem V hweak
      C hC (Set.subset_univ _) (Icc b₁ b₂) hI M hM hsource t ht
  · intro C hC b₁ b₂ hI G hG hsource
    exact compactness_limit_gradient_bound U D hDmeas σ K J hK hKcover
      hJ hJcover Dlim hDweak g hg hgEq C hC (Set.subset_univ _)
      (Icc b₁ b₂) isCompact_Icc hI G hG hsource
  · intro z
    rfl

end CKN.Leray

end
