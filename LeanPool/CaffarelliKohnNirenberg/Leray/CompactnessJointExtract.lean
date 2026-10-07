/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientExtract

/-!
# Compactness Joint Extract

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The velocity slices and gradient fields admit a common subsequence on
countable spatial and temporal exhaustions. -/
theorem exists_common_velocity_gradient_subsequence
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ J →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in J, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G)
    (hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ J → t ∈ J →
          |(∫ x : Vec3, ∑ i : Fin 3, u n (x,t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, u n (x,s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ) :
    ∃ K : ℕ → Set Vec3, ∃ χ : ℕ → Vec3 → ℝ,
    ∃ J : ℕ → Set ℝ,
      (∀ j, IsCompact (K j) ∧ K j ⊆ U ∧ K j ⊆ K (j + 1) ∧
        K j ⊆ interior (K (j + 1))) ∧
      (⋃ j, K j = U) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧ HasCompactSupport (χ j) ∧
        tsupport (χ j) ⊆ U ∧ (∀ x, χ j x ∈ Icc (0 : ℝ) 1) ∧
        ∀ x ∈ K j, χ j x = 1) ∧
      (∀ j, IsCompact (J j) ∧ J j ⊆ I ∧ J j ⊆ J (j + 1) ∧
        J j ⊆ interior (J (j + 1))) ∧
      (⋃ j, J j = I) ∧
      ∃ hmem : ∀ n j (t : I), MemLp
        (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
        2 (volume : Measure Vec3),
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3),
      ∃ D : ∀ j, Lp CompactnessGradientFiber 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))),
        (∀ j t x, Tendsto
          (fun k => inner ℝ ((hmem (σ k) j t).toLp
            (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
          (nhds (inner ℝ (V j t) x))) ∧
        (∀ j x, Continuous (fun t => inner ℝ (V j t) x)) ∧
        (∀ j (p : RationalCompactTimeWindow I) x ε, 0 < ε →
          ∀ᶠ k in atTop, ∀ t : RationalTimeSlice p,
            dist (inner ℝ ((hmem (σ k) j
              ⟨t.1, p.property.2 t.property⟩).toLp
              (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x)
              (inner ℝ (V j ⟨t.1, p.property.2 t.property⟩) x) < ε) ∧
        (∀ j,
          ∃ hgrad : ∀ k, MemLp
            (fun z : Vec3 × ℝ => toCompactnessGradientFiber (Du (σ k) z)) 2
            ((volume.restrict (K j)).prod (volume.restrict (J j))),
            ∀ w, Tendsto
              (fun k => inner ℝ ((hgrad k).toLp
                (fun z => toCompactnessGradientFiber (Du (σ k) z))) w) atTop
              (nhds (inner ℝ (D j) w))) := by
  classical
  obtain ⟨K, χ, hK, hKcover, hχ, hmem⟩ :=
    exists_cutoff_l2_fields_of_local_slice_bounds hU hI u huMeas hbound
  obtain ⟨σ₀, hσ₀, V, hweak, hcont, huniform⟩ :=
    exists_common_subsequence_cutoff_weak_slices hI u huMeas χ
      (fun j => ⟨(hχ j).1, (hχ j).2.1, (hχ j).2.2.1,
        (hχ j).2.2.2.1⟩) hmem hbound hmod
  obtain ⟨J, hJcompact, hJI, hJmono, hJinner, hJcover⟩ :=
    exists_compact_exhaustion_of_open_real I hI
  have hJ (j : ℕ) : IsCompact (J j) ∧ J j ⊆ I ∧
      J j ⊆ J (j + 1) ∧ J j ⊆ interior (J (j + 1)) :=
    ⟨hJcompact j, hJI j, hJmono j, hJinner j⟩
  have hgradBound₀ : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in T, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u (σ₀ n))
            (Du (σ₀ n)) (x,t)) ∂volume) ≤ G := by
    intro C hC hCU T hT hTI
    obtain ⟨G, hG, hGb⟩ := hgradBound C hC hCU T hT hTI
    exact ⟨G, hG, fun n => hGb (σ₀ n)⟩
  obtain ⟨τ, hτ, D, hDweak⟩ :=
    exists_common_subsequence_gradient_weak_on_exhaustion
      (fun k => u (σ₀ k)) (fun k => Du (σ₀ k))
      (fun k => hDuMeas (σ₀ k)) K J
      (fun j => ⟨(hK j).1, (hK j).2.1⟩)
      (fun j => ⟨(hJ j).1, (hJ j).2.1⟩) hgradBound₀
  let σ : ℕ → ℕ := σ₀ ∘ τ
  have hσ : StrictMono σ := hσ₀.comp hτ
  refine ⟨K, χ, J, hK, hKcover, hχ, hJ, hJcover,
    hmem, σ, hσ, V, D, ?_, hcont, ?_, ?_⟩
  · intro j t x
    exact (hweak j t x).comp hτ.tendsto_atTop
  · intro j p x ε hε
    exact hτ.tendsto_atTop.eventually (huniform j p x ε hε)
  · intro j
    obtain ⟨hgrad, hweakGrad⟩ := hDweak j
    exact ⟨hgrad, hweakGrad⟩

end CKN.Leray
