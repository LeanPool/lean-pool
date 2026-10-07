/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessIntervalBridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessStrongLocal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakLocal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientWeakLocal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessPairingContinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLimitBounds

/-!
# Compactness Main

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Local energy, gradient, and time-pairing bounds yield a subsequence
with every-time weak slices, local strong `L²` convergence, and a jointly
measurable weak spatial gradient. This is `lem:compactness`. -/
theorem lem_compactness
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U)
    (hI : IsOpen I) (hIconn : OrdConnected I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u n (x,t) i)
        (fun x => Du n (x,t) i))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ Icc a b →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc a b, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G)
    (hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
          |(∫ x : Vec3, ∑ i : Fin 3, u n (x,t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, u n (x,s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ v : Vec3 × ℝ → Vec3,
      Measurable v ∧
    ∃ g : Vec3 × ℝ → CompactnessGradientFiber,
      Measurable g ∧
      (∀ t : I, ∀ C : Set Vec3, IsCompact C → C ⊆ U →
        ∃ hs : ∀ k, MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))
          2 (volume.restrict C),
        ∃ hl : MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (v (x,t.1)) : L2Vec3))
          2 (volume.restrict C),
          ∀ w : Lp L2Vec3 2 (volume.restrict C),
            Tendsto (fun k => inner ℝ ((hs k).toLp
              (fun x => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))) w)
              atTop (nhds (inner ℝ (hl.toLp
                (fun x => (WithLp.toLp 2 (v (x,t.1)) : L2Vec3))) w))) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ U ×ˢ I →
        Tendsto (fun k => eLpNorm
          ((fun z => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) -
            (fun z => (WithLp.toLp 2 (v z) : L2Vec3))) 2
          (volume.restrict Q)) atTop (nhds 0)) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ U ×ˢ I →
        ∃ hs : ∀ k, MemLp
          (fun z => toCompactnessGradientFiber (Du (σ k) z)) 2
            (volume.restrict Q),
        ∃ hl : MemLp g 2 (volume.restrict Q),
          ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict Q),
            Tendsto (fun k => inner ℝ ((hs k).toLp
              (fun z => toCompactnessGradientFiber (Du (σ k) z))) w)
              atTop (nhds (inner ℝ (hl.toLp g) w))) ∧
      (∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
        HasWeakGradientOn U (fun x => v (x,t) i)
          (fun x m => g (x,t) i m)) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ U →
        ∀ w : Lp L2Vec3 2 (volume.restrict C),
          Continuous (fun t : I =>
            ∫ x in C, ∑ i : Fin 3, v (x,t.1) i * w x i)) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ U →
        ∀ a b : ℝ, Icc a b ⊆ I →
        ∀ M : ℝ≥0∞, M < ⊤ →
          (∀ n t, t ∈ Icc a b →
            (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
              (2 : ℝ) ∂volume) ≤ M) →
          ∀ t ∈ Icc a b,
            (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (v (x,t))) ^
              (2 : ℝ) ∂volume) ≤ M) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ U →
        ∀ a b : ℝ, Icc a b ⊆ I →
        ∀ G : ℝ≥0∞, G < ⊤ →
          (∀ n,
            (∫⁻ t in Icc a b, ∫⁻ x in C,
              ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
                ∂volume) ≤ G) →
          (∫⁻ t in Icc a b, ∫⁻ x in C,
            ENNReal.ofReal (CKN.spatialGradientSq
              (fun _ => (0 : Vec3))
              (fun z i m => g z i m) (x,t)) ∂volume) ≤ G) := by
  let hbound' := compact_time_slice_bounds_of_interval_bounds
    hIconn u hbound
  let hgradBound' := compact_time_gradient_bounds_of_interval_bounds
    hIconn u Du hgradBound
  let hmod' := compact_time_pairing_modulus_of_interval_modulus
    hIconn u hmod
  obtain ⟨K, χ, J, hK, hKcover, hχ, hJ, hJcover,
      hmem, σ, hσ, V, D, hweak, hVcont, huniform, hDweak⟩ :=
    exists_common_velocity_gradient_subsequence hU hI u Du
      huMeas hDuMeas hbound' hgradBound' hmod'
  let v : Vec3 × ℝ → Vec3 := compactnessMollifiedLimit u σ
  have hv : Measurable v := measurable_compactnessMollifiedLimit u σ huMeas
  have hstrongRect := strong_l2_to_compactnessMollifiedLimit_on_exhaustion
    hU hI u Du huMeas hDuMeas hweakGrad hbound' hgradBound'
    K χ J hK hKcover hχ
    (fun j => ⟨(hJ j).1, (hJ j).2.1⟩)
    hmem σ V hweak hVcont huniform
  obtain ⟨g, hg, hgEq, hgWeak⟩ :=
    compactness_gradient_limit_of_joint_limits hU
      u Du v σ K J hK hKcover hJ hJcover
      hweakGrad D hDweak hstrongRect
  refine ⟨σ, hσ, v, hv, g, hg, ?_, ?_, ?_, hgWeak, ?_, ?_, ?_⟩
  · intro t C hC hCU
    exact weak_slices_to_compactnessMollifiedLimit_on_compact hI
      u σ huMeas K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx)
      hbound' hmem V hweak C hC hCU t
  · exact strong_l2_on_compacts_of_exhaustion K J
      (fun j => (hK j).2.2.1) (fun j => (hK j).2.2.2) hKcover
      (fun j => (hJ j).2.2.1) (fun j => (hJ j).2.2.2) hJcover
      (fun k z => (WithLp.toLp 2 (u (σ k) z) : L2Vec3))
      (fun z => (WithLp.toLp 2 (v z) : L2Vec3))
      (fun j => (hstrongRect j).2)
  · intro Q hQ hQI
    exact weak_gradient_to_measurable_limit_on_compact
      Du σ K J hK hKcover hJ hJcover D hDweak
      g hgEq Q hQ hQI
  · intro C hC hCU w
    exact continuous_compactnessMollifiedLimit_local_pairing
      u σ K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx)
      hmem V hweak hVcont C hC hCU w
  · intro C hC hCU a b habI M hM hMb
    exact compactness_limit_slice_bound hI u σ huMeas
      K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx)
      hbound' hmem V hweak C hC hCU (Icc a b) habI M hM hMb
  · intro C hC hCU a b habI G hG hGb
    exact compactness_limit_gradient_bound u Du hDuMeas σ
      K J hK hKcover hJ hJcover D hDweak g hg hgEq
      C hC hCU (Icc a b) isCompact_Icc habI G hG hGb

end CKN.Leray
