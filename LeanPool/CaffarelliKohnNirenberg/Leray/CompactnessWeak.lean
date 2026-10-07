/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakCore

/-!
# Compactness Weak

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter Set Topology MeasureTheory
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray


/-- A uniform norm bound passes to a weak limit in a real Hilbert space. -/
theorem norm_le_of_weak_tendsto_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : ℕ → E} {v : E} {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ x, Tendsto (fun n => inner ℝ (u n) x) atTop
      (nhds (inner ℝ v x))) :
    ‖v‖ ≤ C := by
  by_cases hv : ‖v‖ = 0
  · simpa [hv] using hC
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  have hinner := hweak v
  have hle : ∀ᶠ n in atTop, inner ℝ (u n) v ≤ C * ‖v‖ := by
    filter_upwards [] with n
    calc
      inner ℝ (u n) v ≤ |inner ℝ (u n) v| := le_abs_self _
      _ ≤ ‖u n‖ * ‖v‖ := abs_real_inner_le_norm (u n) v
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
  have hsq : ‖v‖ * ‖v‖ ≤ C * ‖v‖ := by
    have hlim := le_of_tendsto hinner hle
    simpa only [real_inner_self_eq_norm_sq, pow_two] using hlim
  exact le_of_mul_le_mul_right hsq hvpos



/-- Continuity of a uniformly bounded family of Hilbert pairings extends from
a dense sequence of tests to every test. -/
theorem continuous_inner_of_dense_test_continuous
    {T E : Type*} [PseudoMetricSpace T] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : T → E) (ψ : ℕ → E)
    (hψ : DenseRange ψ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t x, |inner ℝ (v t) x| ≤ C * ‖x‖)
    (hcontinuous : ∀ m, Continuous (fun t => inner ℝ (v t) (ψ m))) :
    ∀ x, Continuous (fun t => inner ℝ (v t) x) := by
  intro x
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := ε / (3 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m, hxm⟩ := hψ.exists_dist_lt x hδ
  obtain ⟨η, hη, hGη⟩ := Metric.continuousAt_iff.mp
    ((hcontinuous m).continuousAt) (ε / 3) (by positivity)
  have hfrac : C / (3 * (C + 1)) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hC]
  have hsmall : C * dist x (ψ m) ≤ ε / 3 := by
    calc
      C * dist x (ψ m) ≤ C * δ := mul_le_mul_of_nonneg_left hxm.le hC
      _ = ε * (C / (3 * (C + 1))) := by dsimp [δ]; ring
      _ ≤ ε * (1 / 3) := mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε / 3 := by ring
  refine ⟨η, hη, fun t ht => ?_⟩
  have hleft : dist (inner ℝ (v t) x) (inner ℝ (v t) (ψ m)) ≤
      C * dist x (ψ m) := by
    rw [dist_eq_norm, Real.norm_eq_abs, ← inner_sub_right]
    exact (hbound t (x - ψ m)).trans_eq (by rw [dist_eq_norm])
  have hright : dist (inner ℝ (v t₀) (ψ m)) (inner ℝ (v t₀) x) ≤
      C * dist x (ψ m) := by
    rw [dist_comm, dist_eq_norm, Real.norm_eq_abs, ← inner_sub_right]
    calc
      |inner ℝ (v t₀) (x - ψ m)| ≤ C * ‖x - ψ m‖ := hbound t₀ _
      _ = C * dist x (ψ m) := by rw [dist_eq_norm]
  calc
    dist (inner ℝ (v t) x) (inner ℝ (v t₀) x) ≤
        dist (inner ℝ (v t) x) (inner ℝ (v t) (ψ m)) +
          (dist (inner ℝ (v t) (ψ m)) (inner ℝ (v t₀) (ψ m)) +
            dist (inner ℝ (v t₀) (ψ m)) (inner ℝ (v t₀) x)) := by
      calc
        dist (inner ℝ (v t) x) (inner ℝ (v t₀) x) ≤
            dist (inner ℝ (v t) x) (inner ℝ (v t) (ψ m)) +
              dist (inner ℝ (v t) (ψ m)) (inner ℝ (v t₀) x) := dist_triangle _ _ _
        _ ≤ _ := by gcongr; exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      apply add_lt_add_of_le_of_lt (hleft.trans hsmall)
      apply add_lt_add_of_lt_of_le _ (hright.trans hsmall)
      exact hGη ht
    _ = ε := by ring

/-- A single subsequence gives weakly convergent slices on every member of a
countable family of compact time regions. Pairings with every Hilbert test
are continuous on each region. This is the diagonal local form of the slice
selection in lem:compactness. -/
theorem exists_common_subsequence_weak_pairings_on_compact_times
    {ι : Type*} [Countable ι]
    (T : ι → Type*) [∀ i, PseudoMetricSpace (T i)]
      [∀ i, CompactSpace (T i)] [∀ i, CompactlyCoherentSpace (T i)]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
      [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
    (u : ℕ → ∀ i, T i → E i) (ψ : ∀ i, ℕ → E i)
    (hψ : ∀ (i : ι), DenseRange (ψ i)) (C : ι → ℝ)
    (hC : ∀ (i : ι), 0 ≤ C i)
    (hbound : ∀ n i t, ‖u n i t‖ ≤ C i)
    (F : ℕ → ∀ i, ℕ → C(T i, ℝ))
    (hpair : ∀ n i m t, F n i m t = inner ℝ (u n i t) (ψ i m))
    (hequi : ∀ i m, EquicontinuousOn
      (fun g : range fun n => F n i m => (g : T i → ℝ)) univ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ v : ∀ i, T i → E i,
      (∀ i t x, Tendsto (fun n => inner ℝ (u (σ n) i t) x) atTop
      (nhds (inner ℝ (v i t) x))) ∧
      (∀ (i : ι) x, Continuous (fun t => inner ℝ (v i t) x)) ∧
      (∀ (i : ι) t x, |inner ℝ (v i t) x| ≤ C i * ‖x‖) ∧
      ∃ L : ∀ (i : ι), ℕ → C(T i, ℝ),
        (∀ (i : ι) m t, L i m t = inner ℝ (v i t) (ψ i m)) ∧
        ∀ (i : ι) m, Tendsto (fun n => F (σ n) i m) atTop (nhds (L i m)) := by
  let κ := Σ i : ι, ℕ
  let F' : ℕ → ∀ p : κ, C(T p.1, ℝ) := fun n p => F n p.1 p.2
  have hequi' : ∀ p, EquicontinuousOn
      (fun g : range fun n => F' n p => (g : T p.1 → ℝ)) univ := by
    intro p
    exact hequi p.1 p.2
  have hvalues : ∀ p t, ∃ K : Set ℝ, IsCompact K ∧ ∀ n, F' n p t ∈ K := by
    intro p t
    let B : ℝ := C p.1 * ‖ψ p.1 p.2‖
    have hB : 0 ≤ B := mul_nonneg (hC p.1) (norm_nonneg _)
    refine ⟨Set.Icc (-B) B, isCompact_Icc, ?_⟩
    intro n
    have hinner : |F' n p t| ≤ B := by
      rw [hpair]
      exact (abs_real_inner_le_norm (u n p.1 t) (ψ p.1 p.2)).trans
        (mul_le_mul_of_nonneg_right (hbound n p.1 t) (norm_nonneg _))
    rw [Set.mem_Icc]
    exact ⟨(abs_le.mp hinner).1, (abs_le.mp hinner).2⟩
  obtain ⟨σ, hσ, G, hG⟩ := exists_common_subsequence_uniform_convergence
    F' hequi' hvalues
  have hpairTendsto (i : ι) (m : ℕ) (t : T i) :
      Tendsto (fun n => inner ℝ (u (σ n) i t) (ψ i m)) atTop
        (nhds (G ⟨i, m⟩ t)) := by
    have heval : Continuous (fun f : C(T i, ℝ) => f t) :=
      ContinuousEvalConst.continuous_eval_const t
    have h := heval.continuousAt.tendsto.comp (hG ⟨i, m⟩)
    change Tendsto (fun n => F (σ n) i m t) atTop (nhds (G ⟨i, m⟩ t)) at h
    simpa only [hpair] using h
  have hexists : ∀ i t, ∃ z : E i, ∀ x,
      Tendsto (fun n => inner ℝ (u (σ n) i t) x) atTop
        (nhds (inner ℝ z x)) := by
    intro i t
    exact exists_weak_limit_of_tendsto_pairings_on_dense_range
      (fun n => u (σ n) i t) (C i) (hC i) (fun n => hbound (σ n) i t)
      (ψ i) (hψ i) (fun m => ⟨G ⟨i, m⟩ t, hpairTendsto i m t⟩)
  let v : ∀ i, T i → E i := fun i t => Classical.choose (hexists i t)
  have hv (i : ι) (t : T i) (x : E i) :
      Tendsto (fun n => inner ℝ (u (σ n) i t) x) atTop
        (nhds (inner ℝ (v i t) x)) := Classical.choose_spec (hexists i t) x
  have htest (i : ι) (m : ℕ) (t : T i) :
      inner ℝ (v i t) (ψ i m) = G ⟨i, m⟩ t :=
    tendsto_nhds_unique (hv i t (ψ i m)) (hpairTendsto i m t)
  have hvBound (i : ι) (t : T i) (x : E i) :
      |inner ℝ (v i t) x| ≤ C i * ‖x‖ := by
    have hlim := (hv i t x).abs
    apply le_of_tendsto hlim
    filter_upwards [] with n
    exact (abs_real_inner_le_norm (u (σ n) i t) x).trans
      (mul_le_mul_of_nonneg_right (hbound (σ n) i t) (norm_nonneg x))
  have hcontinuous (i : ι) (x : E i) :
      Continuous (fun t => inner ℝ (v i t) x) := by
    have hdenseContinuous (m : ℕ) :
        Continuous (fun t => inner ℝ (v i t) (ψ i m)) := by
      have heq : (fun t => inner ℝ (v i t) (ψ i m)) = G ⟨i, m⟩ := by
        funext t
        exact htest i m t
      rw [heq]
      exact (G ⟨i, m⟩).continuous
    exact (continuous_inner_of_dense_test_continuous (v i) (ψ i) (hψ i)
      (C i) (hC i) (hvBound i) hdenseContinuous) x
  let L : ∀ i, ℕ → C(T i, ℝ) := fun i m => G ⟨i, m⟩
  have hLval (i : ι) (m : ℕ) (t : T i) :
      L i m t = inner ℝ (v i t) (ψ i m) := by
    exact (htest i m t).symm
  have hLconv (i : ι) (m : ℕ) :
      Tendsto (fun n => F (σ n) i m) atTop (nhds (L i m)) := by
    simpa [L, F'] using hG ⟨i, m⟩
  exact ⟨σ, hσ, v, fun i t x => hv i t x, hcontinuous, hvBound, L, hLval, hLconv⟩

/-- A uniform two-term time modulus makes a sequence of real continuous maps
equicontinuous. This converts the pairing estimate in lem:compactness into
the input required for Arzelà--Ascoli. -/
theorem equicontinuous_of_two_term_time_modulus
    {T : Type*} [PseudoMetricSpace T] (F : ℕ → C(T, ℝ))
    (C D θ : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hθ : 0 < θ)
    (hmod : ∀ n s t, |F n t - F n s| ≤
      C * dist t s + D * (dist t s) ^ θ) :
    EquicontinuousOn (fun g : range F => (g : T → ℝ)) univ := by
  intro t₀ _
  rw [equicontinuousWithinAt_univ]
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let δ₁ : ℝ := ε / (2 * (C + 1))
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hpowTendsto : Tendsto (fun x : ℝ => x ^ θ) (nhds 0) (nhds 0) :=
    Filter.Tendsto.rpow_const_nhds_zero tendsto_id hθ
  have hthreshold : 0 < ε / (2 * (D + 1)) := by positivity
  have hpowSmall : ∀ᶠ x : ℝ in nhds 0,
      x ^ θ < ε / (2 * (D + 1)) :=
    hpowTendsto.eventually (isOpen_Iio.mem_nhds hthreshold)
  obtain ⟨δ₂, hδ₂, hδ₂ball⟩ := Metric.eventually_nhds_iff.mp hpowSmall
  have hfracC : C / (2 * (C + 1)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hC]
  have hfracD : D / (2 * (D + 1)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hD]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht g => ?_⟩
  obtain ⟨n, hn⟩ := g.property
  rw [← hn]
  have ht₁ : dist t t₀ < δ₁ := (lt_min_iff.mp ht).1
  have ht₂ : dist t t₀ < δ₂ := (lt_min_iff.mp ht).2
  have hlinear : C * dist t t₀ < ε / 2 := by
    calc
      C * dist t t₀ ≤ C * δ₁ := mul_le_mul_of_nonneg_left ht₁.le hC
      _ = ε * (C / (2 * (C + 1))) := by dsimp [δ₁]; ring
      _ < ε * (1 / 2) := mul_lt_mul_of_pos_left hfracC hε
      _ = ε / 2 := by ring
  have hdistNonneg : 0 ≤ dist t t₀ := dist_nonneg
  have hpowMem : dist (dist t t₀) 0 < δ₂ := by
    rw [Real.dist_eq]
    rw [sub_zero, abs_of_nonneg hdistNonneg]
    exact ht₂
  have hpower : (dist t t₀) ^ θ < ε / (2 * (D + 1)) :=
    @hδ₂ball (dist t t₀) hpowMem
  have hpower' : D * (dist t t₀) ^ θ < ε / 2 := by
    calc
      D * (dist t t₀) ^ θ ≤ D * (ε / (2 * (D + 1))) :=
        mul_le_mul_of_nonneg_left hpower.le hD
      _ = ε * (D / (2 * (D + 1))) := by ring
      _ < ε * (1 / 2) := mul_lt_mul_of_pos_left hfracD hε
      _ = ε / 2 := by ring
  rw [Real.dist_eq]
  calc
    |F n t₀ - F n t| ≤ C * dist t₀ t + D * (dist t₀ t) ^ θ := hmod n t t₀
    _ = C * dist t t₀ + D * (dist t t₀) ^ θ := by rw [dist_comm]
    _ < ε / 2 + ε / 2 := add_lt_add hlinear hpower'
    _ = ε := by ring

end CKN.Leray
