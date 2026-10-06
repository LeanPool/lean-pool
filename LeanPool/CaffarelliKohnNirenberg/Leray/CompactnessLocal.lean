/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessStrongField
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection

/-!
# Compactness Local

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The common weak slice extraction and the local energy bounds give strong
`L²` convergence on every compact space-time rectangle. -/
theorem strong_l2_on_compact_rectangle_of_cutoff_weak_slices
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (u : ℕ → (Vec3 × ℝ) → Vec3)
    (Du : ℕ → (Vec3 × ℝ) → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u n (x,t) i)
        (fun x => Du n (x,t) i))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t, t ∈ J →
        (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
          (2 : ℝ) ∂volume) ≤ M)
    (hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in J, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G)
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧ K j ⊆ K (j + 1) ∧
      K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧
      HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ U ∧
      (∀ x, χ j x ∈ Icc (0 : ℝ) 1) ∧ ∀ x ∈ K j, χ j x = 1)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (σ : ℕ → ℕ) (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x)))
    (hVcont : ∀ j x, Continuous (fun t => inner ℝ (V j t) x))
    (huniform : ∀ j (p : RationalCompactTimeWindow I) x ε, 0 < ε →
      ∀ᶠ k in atTop, ∀ t : RationalTimeSlice p,
        dist (inner ℝ ((hmem (σ k) j
          ⟨t.1, p.property.2 t.property⟩).toLp
          (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x)
          (inner ℝ (V j ⟨t.1, p.property.2 t.property⟩) x) < ε)
    {C : Set Vec3} {J : Set ℝ}
    (hC : IsCompact C) (hCU : C ⊆ U)
    (hJ : IsCompact J) (hJI : J ⊆ I) :
    ∃ hf : ∀ k, MemLp
      (fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) 2
      ((volume.restrict C).prod (volume.restrict J)),
      ∃ g : Lp L2Vec3 2 ((volume.restrict C).prod (volume.restrict J)),
        Tendsto (fun k => (hf k).toLp
          (fun z => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)))
          atTop (nhds g) := by
  classical
  obtain ⟨W, δ, hδ, hW, hCW, hWc, hWcU, _⟩ :=
    CKN.exists_open_between_of_isCompact hC hU hCU
  obtain ⟨j, hj⟩ := compact_subset_eventually_in_exhaustion
    hWc hWcU K (fun j => (hK j).2.2.1)
    (fun j => (hK j).2.2.2) hKcover
  have hWj : W ⊆ K j := subset_trans subset_closure hj
  obtain ⟨M, hM, hMbound⟩ := hbound (closure W) hWc hWcU J hJ hJI
  obtain ⟨G, hG, hGbound⟩ := hgradBound (closure W) hWc hWcU J hJ hJI
  let Cχ : Set Vec3 := tsupport (χ j)
  obtain ⟨Mχ, hMχ, hMχbound⟩ :=
    hbound Cχ (hχ j).2.1 (hχ j).2.2.1 J hJ hJI
  have hnorm (k : ℕ) (t : ℝ) (ht : t ∈ J) :
      ‖(hmem (σ k) j ⟨t, hJI ht⟩).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t)))‖ ≤
        (Mχ ^ (1 / 2 : ℝ)).toReal :=
    cutoff_l2_norm_bound_on_time_window u huMeas (χ j)
      (hχ j).1 (hχ j).2.1 (hχ j).2.2.2.1
      (fun n t ht => hmem n j ⟨t, hJI ht⟩)
      Mχ hMχ hMχbound (σ k) t ht
  have hUniformJ (x : Lp L2Vec3 2 (volume : Measure Vec3))
      (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ k in atTop, ∀ t, (ht : t ∈ J) →
        dist (inner ℝ ((hmem (σ k) j ⟨t, hJI ht⟩).toLp
          (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t)))) x)
          (inner ℝ (V j ⟨t, hJI ht⟩) x) < ε := by
    apply eventually_uniform_on_compact_of_rational_windows hI hJ hJI
      (fun k t => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x)
      (fun t => inner ℝ (V j t) x)
    · intro p ε hε
      simpa only using huniform j p x ε hε
    · exact hε
  exact exists_strong_l2_limit_on_compact_rectangle
    hC hW hCW subset_closure hJ hJI
    (fun k => u (σ k)) (fun k => Du (σ k))
    (fun k => huMeas (σ k)) (fun k => hDuMeas (σ k))
    (fun k => by
      have h := ae_restrict_of_ae_restrict_of_subset hJI (hweakGrad (σ k))
      filter_upwards [h] with t ht
      intro i
      exact (ht i).mono hW (subset_trans subset_closure hWcU))
    M G hM hG (fun k t ht => hMbound (σ k) t ht)
    (fun k => hGbound (σ k)) (χ j)
    (fun x hx => (hχ j).2.2.2.2 x (hWj hx))
    (fun k t => hmem (σ k) j t) (V j)
    (hweak j) (hVcont j) hUniformJ
    (Mχ ^ (1 / 2 : ℝ)).toReal ENNReal.toReal_nonneg hnorm

end CKN.Leray
