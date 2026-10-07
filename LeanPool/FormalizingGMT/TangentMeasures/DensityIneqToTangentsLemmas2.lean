/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.TangentMeasures.Doubling
public import LeanPool.FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas1

/-!
# Good sets for Mattila's Lemma 14.7

This file constructs sets on which ball measures are uniformly comparable and proves the
approximation results used in Lemma 14.7.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-! ## Points with uniformly comparable ball measures -/
/-- `goodSet s p q m μ` is the set of points `z` such that
`p ρ ^ s ≤ μ (B (z, ρ)) ≤ q ρ ^ s` for every radius `0 < ρ < 1 / (m + 1)`. -/
def goodSet (s p q : ℝ) (m : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (m + 1) →
    ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall z ρ) ∧
      μ (closedBall z ρ) ≤ ENNReal.ofReal (q * ρ ^ s)}
/-- Enlarging the admissible range `[p, q]` enlarges `goodSet`. -/
lemma goodSet_subset {s p q p' q' : ℝ} {m : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hp : p' ≤ p) (hq : q ≤ q') :
    goodSet s p q m μ ⊆ goodSet s p' q' m μ := by
  intro z hz ρ hρ hρm
  obtain ⟨h1, h2⟩ := hz ρ hρ hρm
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) h1,
    le_trans h2 (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hρ.le s)
  · exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hρ.le s)
/-- Passing to a smaller range of radii enlarges `goodSet`. -/
lemma goodSet_mono_nat {s p q : ℝ} {m m' : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hm : m ≤ m') :
    goodSet s p q m μ ⊆ goodSet s p q m' μ := by
  intro z hz ρ hρ hρm
  refine hz ρ hρ (lt_of_lt_of_le hρm ?_)
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hm 1
/-- The sets `goodSet s p q m μ` are closed, hence Borel. -/
lemma isClosed_goodSet (s p q : ℝ) (m : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : IsClosed (goodSet s p q m μ) := by
  refine isClosed_of_closure_subset fun z hz ρ hρ hρm ↦ ⟨?_, ?_⟩
  · -- shrink the radius slightly and let the shrinking tend to `0`
    have hbase : ContinuousAt (fun δ : ℝ ↦ ρ - δ) 0 := by fun_prop
    have hrpow : ContinuousAt (fun x : ℝ ↦ x ^ s) (ρ - 0) := by
      simpa using Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne')
    have h1 : ContinuousAt (fun δ : ℝ ↦ p * (ρ - δ) ^ s) 0 :=
      continuousAt_const.mul (hrpow.comp hbase)
    have htend : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (p * (ρ - δ) ^ s)) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (p * ρ ^ s))) := by
      have h2 := (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto
      simp only [Function.comp_def, sub_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hρ)] with δ hδ hδρ
    have hδ0 : 0 < δ := Set.mem_Ioi.mp hδ
    obtain ⟨y, hyB, hdist⟩ := Metric.mem_closure_iff.mp hz δ hδ0
    have hsub : closedBall y (ρ - δ) ⊆ closedBall z ρ := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
        _ ≤ (ρ - δ) + δ := by
            gcongr
            rw [dist_comm]
            exact hdist.le
        _ = ρ := by ring
    exact le_trans (hyB (ρ - δ) (by linarith) (by linarith)).1 (measure_mono hsub)
  · -- enlarge the radius slightly and let the enlargement tend to `0`
    have hbase : ContinuousAt (fun δ : ℝ ↦ ρ + δ) 0 := by fun_prop
    have hrpow : ContinuousAt (fun x : ℝ ↦ x ^ s) (ρ + 0) := by
      simpa using Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne')
    have h1 : ContinuousAt (fun δ : ℝ ↦ q * (ρ + δ) ^ s) 0 :=
      continuousAt_const.mul (hrpow.comp hbase)
    have htend : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (q * (ρ + δ) ^ s)) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (q * ρ ^ s))) := by
      have h2 := (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto
      simp only [Function.comp_def, add_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 / (m + 1) - ρ by linarith))]
      with δ hδ hδρ
    have hδ0 : 0 < δ := Set.mem_Ioi.mp hδ
    obtain ⟨y, hyB, hdist⟩ := Metric.mem_closure_iff.mp hz δ hδ0
    have hsub : closedBall z ρ ⊆ closedBall y (ρ + δ) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
        _ ≤ ρ + δ := by gcongr
    exact le_trans (measure_mono hsub) (hyB (ρ + δ) (by linarith) (by linarith)).2
/-- Every point of `A` at which the density ratio exceeds `θ` lies in one of the sets
`goodSet s p q m μ` with `θ q ≤ p`. -/
lemma exists_goodSet_mem {s : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ positiveFiniteDensitySet s μ)
    {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : ENNReal.ofReal θ < RatioOfDensities s μ a) :
    ∃ (p q : ℚ) (m : ℕ), 0 < (p : ℝ) ∧ 0 < (q : ℝ) ∧ θ * (q : ℝ) ≤ (p : ℝ) ∧
      dimensionalUpperDensity μ.toOuterMeasure s a * ENNReal.ofReal ((2 : ℝ) ^ s) <
        ENNReal.ofReal (q : ℝ) ∧
      a ∈ goodSet s (p : ℝ) (q : ℝ) m μ := by
  obtain ⟨hl, hlu, hu⟩ := ha
  set l := dimensionalLowerDensity μ.toOuterMeasure s a with hldef
  set u := dimensionalUpperDensity μ.toOuterMeasure s a with hudef
  have hupos : 0 < u := lt_of_lt_of_le hl hlu
  have hltop : l ≠ ∞ := ne_top_of_le_ne_top hu.ne hlu
  set L := l.toReal with hLdef
  set U := u.toReal with hUdef
  have hLpos : 0 < L := ENNReal.toReal_pos hl.ne' hltop
  have hUpos : 0 < U := ENNReal.toReal_pos hupos.ne' hu.ne
  have hLl : ENNReal.ofReal L = l := ENNReal.ofReal_toReal hltop
  have hUu : ENNReal.ofReal U = u := ENNReal.ofReal_toReal hu.ne
  -- the density hypothesis, in real form
  have hθLU : θ * U < L := by
    have h1 : ENNReal.ofReal θ < ENNReal.ofReal (L / U) := by
      rw [ENNReal.ofReal_div_of_pos hUpos, hLl, hUu]
      exact hθ
    have h2 : θ < L / U := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h1
    rwa [lt_div_iff₀ hUpos] at h2
  -- a small margin `η`
  set D := L - θ * U with hD
  have hDpos : 0 < D := by simp only [hD]; linarith
  set η := min (L / 2) (D / (2 * (1 + θ))) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηL : η ≤ L / 2 := min_le_left _ _
  have hηD : η ≤ D / (2 * (1 + θ)) := min_le_right _ _
  have hLη : 0 < L - η := by linarith
  have hη2 : η * (2 * (1 + θ)) ≤ D := (le_div_iff₀ (by positivity)).mp hηD
  have hkey : θ * (U + η) < L - η := by
    have h3 : η * (1 + θ) < D := by nlinarith
    simp only [hD] at h3
    nlinarith
  -- the resulting constants
  set c2 : ℝ := (2 : ℝ) ^ s with hc2
  have hc2pos : 0 < c2 := Real.rpow_pos_of_pos (by norm_num) s
  set p₀ := c2 * (L - η) with hp₀def
  set q₀ := c2 * (U + η) with hq₀def
  have hp₀ : 0 < p₀ := mul_pos hc2pos hLη
  have hq₀ : 0 < q₀ := mul_pos hc2pos (by linarith)
  have hθq : θ * q₀ < p₀ := by
    simp only [hp₀def, hq₀def]
    nlinarith
  -- the two-sided ball bound at small scales
  have hev1 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (L - η) < μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s) := by
    refine eventually_lt_of_lt_liminf ?_
    have h' : ENNReal.ofReal (L - η) < l := by
      rw [← hLl]
      exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr (by linarith)
    rwa [hldef, dimensional_lower_density_toOuterMeasure_eq] at h'
  have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s) < ENNReal.ofReal (U + η) := by
    refine eventually_lt_of_limsup_lt ?_
    have h' : u < ENNReal.ofReal (U + η) := by
      rw [← hUu]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    rwa [hudef, dimensional_upper_density_toOuterMeasure_eq] at h'
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (p₀ * r ^ s) ≤ μ (closedBall a r) ∧
        μ (closedBall a r) ≤ ENNReal.ofReal (q₀ * r ^ s) := by
    filter_upwards [hev1, hev2, self_mem_nhdsWithin] with r h1 h2 hr0
    have hr : 0 < r := Set.mem_Ioi.mp hr0
    have hrs : (0 : ℝ) < (2 * r) ^ s := Real.rpow_pos_of_pos (by linarith) s
    have hden_ne : ENNReal.ofReal ((2 * r) ^ s) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hrs
    have hprod : ∀ v : ℝ, 0 ≤ v →
        ENNReal.ofReal v * ENNReal.ofReal ((2 * r) ^ s)
          = ENNReal.ofReal (c2 * v * r ^ s) := by
      intro v hv
      rw [← ENNReal.ofReal_mul hv, Real.mul_rpow (by norm_num) hr.le]
      congr 1
      simp only [hc2]
      ring
    constructor
    · have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hden_ne)
        (Or.inl ENNReal.ofReal_ne_top)).mp h1
      refine le_of_lt (lt_of_le_of_lt (le_of_eq ?_) hmul)
      rw [hprod (L - η) hLη.le, hp₀def]
    · have hmul := (ENNReal.div_lt_iff (Or.inl hden_ne)
        (Or.inl ENNReal.ofReal_ne_top)).mp h2
      refine le_of_lt (lt_of_lt_of_le hmul (le_of_eq ?_))
      rw [hprod (U + η) (by linarith), hq₀def]
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hh⟩ := hev
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  have hmem : a ∈ goodSet s p₀ q₀ m μ := by
    intro ρ hρ hρm
    refine hh (show dist ρ 0 < ε from ?_) (Set.mem_Ioi.mpr hρ)
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ]
    exact lt_trans hρm hm
  -- finally, rational constants
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show (θ * q₀ + p₀) / 2 < p₀ by linarith)
  have hppos : 0 < (p : ℝ) := by nlinarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show q₀ < (p : ℝ) / θ by rw [lt_div_iff₀ hθ0]; nlinarith)
  have hqpos : 0 < (q : ℝ) := lt_trans hq₀ hq1
  have hθqp : θ * (q : ℝ) ≤ (p : ℝ) := by
    have h := (lt_div_iff₀ hθ0).mp hq2
    nlinarith
  have hqsup : dimensionalUpperDensity μ.toOuterMeasure s a * ENNReal.ofReal ((2 : ℝ) ^ s) <
      ENNReal.ofReal (q : ℝ) := by
    rw [← hudef, ← hUu, ← ENNReal.ofReal_mul hUpos.le]
    refine (ENNReal.ofReal_lt_ofReal_iff hqpos).mpr ?_
    have : q₀ < (q : ℝ) := hq1
    simp only [hq₀def, hc2] at this
    nlinarith
  exact ⟨p, q, m, hppos, hqpos, hθqp, hqsup, goodSet_subset hp2.le hq1.le hmem⟩
/-! ## Points all of whose small balls are controlled -/
/-- `goodBallSet s q m μ` is the set of points `z` such that **every** closed ball of radius
`0 < w < 1 / (m + 1)` containing `z` has measure at most `q w ^ s`. -/
def goodBallSet (s q : ℝ) (m : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < 1 / (m + 1) →
    z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal (q * w ^ s)}
lemma goodBallSet_subset {s q q' : ℝ} {m : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hq : q ≤ q') :
    goodBallSet s q m μ ⊆ goodBallSet s q' m μ := by
  intro z hz y w hw hwm hmem
  refine le_trans (hz y w hw hwm hmem) (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hw.le s)
lemma goodBallSet_mono_nat {s q : ℝ} {m m' : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hm : m ≤ m') :
    goodBallSet s q m μ ⊆ goodBallSet s q m' μ := by
  intro z hz y w hw hwm hmem
  refine hz y w hw (lt_of_lt_of_le hwm ?_) hmem
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hm 1
lemma isClosed_goodBallSet (s q : ℝ) (m : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : IsClosed (goodBallSet s q m μ) := by
  refine isClosed_of_closure_subset fun z hz y w hw hwm hmem ↦ ?_
  have hbase : ContinuousAt (fun δ : ℝ ↦ w + δ) 0 := by fun_prop
  have hrpow : ContinuousAt (fun v : ℝ ↦ v ^ s) (w + 0) := by
    simpa using Real.continuousAt_rpow_const w s (Or.inl hw.ne')
  have h1 : ContinuousAt (fun δ : ℝ ↦ q * (w + δ) ^ s) 0 :=
    continuousAt_const.mul (hrpow.comp hbase)
  have htend : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (q * (w + δ) ^ s)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (q * w ^ s))) := by
    have h2 := (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto
    simp only [Function.comp_def, add_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 / (m + 1) - w by linarith))]
    with δ hδ hδw
  have hδ0 : 0 < δ := Set.mem_Ioi.mp hδ
  obtain ⟨z', hz'B, hdist⟩ := Metric.mem_closure_iff.mp hz δ hδ0
  have hz'mem : z' ∈ closedBall y (w + δ) := by
    rw [mem_closedBall] at hmem ⊢
    calc dist z' y ≤ dist z' z + dist z y := dist_triangle _ _ _
      _ ≤ δ + w := by
          gcongr
          rw [dist_comm]
          exact hdist.le
      _ = w + δ := by ring
  have hsub : closedBall y w ⊆ closedBall y (w + δ) :=
    closedBall_subset_closedBall (by linarith)
  exact le_trans (measure_mono hsub) (hz'B y (w + δ) (by linarith) (by linarith) hz'mem)
/-- Under the ball-density hypothesis of Lemma 14.7 (2), a point whose upper density is small
compared with `q` lies in one of the sets `goodBallSet s q m μ`. -/
lemma exists_goodBallSet_mem {s q : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (hq : 0 < q)
    (hball : upperBallSDensity s μ a ≤ dimensionalUpperDensity μ.toOuterMeasure s a)
    (hqsup : dimensionalUpperDensity μ.toOuterMeasure s a * ENNReal.ofReal ((2 : ℝ) ^ s) <
      ENNReal.ofReal q) :
    ∃ m : ℕ, a ∈ goodBallSet s q m μ := by
  set c2 : ℝ := (2 : ℝ) ^ s with hc2
  have hc2pos : 0 < c2 := Real.rpow_pos_of_pos (by norm_num) s
  have hc2ne : ENNReal.ofReal c2 ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hc2pos
  set Q : ℝ≥0∞ := ENNReal.ofReal q / ENNReal.ofReal c2 with hQ
  have hlt : dimensionalUpperDensity μ.toOuterMeasure s a < Q := by
    rw [hQ, ENNReal.lt_div_iff_mul_lt (Or.inl hc2ne) (Or.inl ENNReal.ofReal_ne_top)]
    exact hqsup
  have hlimsup : upperBallSDensity s μ a < Q := lt_of_le_of_lt hball hlt
  rw [upperBallSDensity] at hlimsup
  have hev := eventually_lt_of_limsup_lt hlimsup
  obtain ⟨δ, hδQ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ : 0 < δ := Set.mem_Ioi.mp hδpos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ / 2 by positivity)
  refine ⟨m, fun y w hw hwm hmem ↦ ?_⟩
  have h2w : 2 * w < δ := by
    have : w < δ / 2 := lt_trans hwm hm
    linarith
  have hratio : μ (closedBall y w) / ENNReal.ofReal ((2 * w) ^ s) < Q := by
    refine lt_of_le_of_lt ?_ hδQ
    exact le_iSup_of_le y (le_iSup_of_le w (le_iSup_of_le hw
      (le_iSup_of_le h2w (le_iSup_of_le hmem le_rfl))))
  have hden_ne : ENNReal.ofReal ((2 * w) ^ s) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (by linarith) s
  have hmul := (ENNReal.div_lt_iff (Or.inl hden_ne) (Or.inl ENNReal.ofReal_ne_top)).mp hratio
  refine le_of_lt (lt_of_lt_of_le hmul (le_of_eq ?_))
  have hsplit : ENNReal.ofReal ((2 * w) ^ s)
      = ENNReal.ofReal c2 * ENNReal.ofReal (w ^ s) := by
    rw [← ENNReal.ofReal_mul hc2pos.le, Real.mul_rpow (by norm_num) hw.le]
  rw [hsplit, hQ, ← mul_assoc, ENNReal.div_mul_cancel hc2ne ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hq.le]
/-! ## The density theorem in the form required by the reduction step -/
/-- **Besicovitch density theorem** for a Radon measure, in the form used in Mattila's
proof of Lemma 14.7 (1): outside a `μ`-null set, every point of a Borel set `B` is a density
point of `B`, in the sense that the portion of a small ball around it which misses `B` is an
arbitrarily small fraction of the ball. -/
lemma exists_null_of_not_density_point (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : Measure.Regular μ) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ B \ N, ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ) := by
  let _ : μ.Regular := hμ
  set P : EuclideanSpace ℝ (Fin n) → Prop := fun x ↦
    Tendsto (fun r ↦ μ (B ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 1)
    with hP
  have hae : ∀ᵐ x ∂μ.restrict B, P x := Besicovitch.ae_tendsto_measure_inter_div μ B
  have hbad : μ ({x | ¬ P x} ∩ B) = 0 :=
    le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp hae).le) zero_le
  obtain ⟨G, hGsub, hGmeas, hG0⟩ := exists_measurable_superset_of_null hbad
  refine ⟨G, ?_, ?_⟩
  · exact hG0
  rintro a ⟨haB, haG⟩ γ hγ
  have hPa : P a := by
    by_contra hcon
    exact haG (hGsub ⟨hcon, haB⟩)
  set γ' : ℝ≥0∞ := min γ 1 with hγ'
  have hγ'pos : 0 < γ' := lt_min hγ one_pos
  have hγ'le : γ' ≤ 1 := min_le_right _ _
  have hlt : (1 : ℝ≥0∞) - γ' < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hγ'pos.ne'
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (1 : ℝ≥0∞) - γ' < μ (B ∩ closedBall a ρ) / μ (closedBall a ρ) :=
    (tendsto_order.1 hPa).1 _ hlt
  filter_upwards [hev] with ρ hρ
  set A := μ (closedBall a ρ) with hA
  set Ai := μ (B ∩ closedBall a ρ) with hAi
  set Ac := μ (closedBall a ρ \ B) with hAc
  have hAtop : A ≠ ∞ := (isCompact_closedBall a ρ).measure_lt_top.ne
  have hsum : Ai + Ac = A := by
    rw [hAi, hAc, hA, Set.inter_comm]
    exact measure_inter_add_sdiff _ hB
  rcases eq_or_ne A 0 with hA0 | hA0
  · have : Ac ≤ A := by rw [← hsum]; exact le_add_self
    rw [hA0] at this ⊢
    simpa using this
  have hkey : ((1 : ℝ≥0∞) - γ') * A < Ai :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hA0) (Or.inl hAtop)).mp hρ
  have hmulle : γ' * A ≤ A := by
    calc γ' * A ≤ 1 * A := by gcongr
      _ = A := one_mul A
  have hsub' : A - γ' * A ≤ Ai := by
    refine le_of_lt (lt_of_le_of_lt (le_of_eq ?_) hkey)
    rw [ENNReal.sub_mul (fun _ _ ↦ hAtop), one_mul]
  have hstep : (A - γ' * A) + Ac ≤ A := by
    calc (A - γ' * A) + Ac ≤ Ai + Ac := by gcongr
      _ = A := hsum
  have hfinal : Ac ≤ γ' * A := by
    have h := ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top hAtop tsub_le_self) hstep
    rwa [ENNReal.sub_sub_cancel hAtop hmulle] at h
  exact hfinal.trans (by gcongr; exact min_le_left _ _)
/-! ## Passing to the limit in the constants -/
/-- If the two-sided ball estimate holds with constants `θ k` tending to `t`, then it holds
with the constant `t` itself. -/
lemma exists_uniform_constant_of_tendsto {s θ₀ : ℝ} {t : ℝ≥0∞} {θ : ℕ → ℝ}
    {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : Measure.Regular ν) (hν0 : ν ≠ 0)
    (hθ₀ : 0 < θ₀) (hθlb : ∀ k, θ₀ ≤ θ k)
    (hθ : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t))
    (h : ∀ k, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  choose c hcpos hctop hc using h
  obtain ⟨R, -, hRpos⟩ := exists_ball_pos_of_ne_zero hν0
  obtain ⟨x₀, -, hx₀⟩ := exists_mem_support_of_measure_pos hRpos
  set V := ν (closedBall x₀ 1) with hV
  have hVpos : 0 < V :=
    lt_of_lt_of_le (measure_ball_pos_of_mem_support hx₀ one_pos)
      (measure_mono ball_subset_closedBall)
  have hVtop : V ≠ ∞ := (regular_measure_closedBall_lt_top hν x₀ 1).ne
  have hθ₀ne : ENNReal.ofReal θ₀ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hθ₀
  have hVle : ∀ k, V ≤ c k := by
    intro k
    simpa using (hc k x₀ hx₀ 1 one_pos).2
  have hcub : ∀ k, ENNReal.ofReal θ₀ * c k ≤ V := by
    intro k
    have hk := (hc k x₀ hx₀ 1 one_pos).1
    simp only [Real.one_rpow, ENNReal.ofReal_one, mul_one] at hk
    exact le_trans (by gcongr; exact hθlb k) hk
  obtain ⟨cl, -, φ, hφ, hcl⟩ :=
    (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq (x := c) (fun k ↦ mem_univ _)
  have hclpos : 0 < cl := lt_of_lt_of_le hVpos (ge_of_tendsto' hcl fun j ↦ hVle (φ j))
  have hcltop : cl ≠ ∞ := by
    have hlim : ENNReal.ofReal θ₀ * cl ≤ V :=
      le_of_tendsto' (ENNReal.Tendsto.const_mul hcl (Or.inr ENNReal.ofReal_ne_top))
        fun j ↦ hcub (φ j)
    intro htop
    rw [htop, ENNReal.mul_top hθ₀ne] at hlim
    exact hVtop (top_le_iff.mp hlim)
  refine ⟨cl, hclpos, hcltop, fun x hx ρ hρ ↦ ⟨?_, ?_⟩⟩
  · have hmul : Tendsto (fun j ↦ ENNReal.ofReal (θ (φ j)) * c (φ j) * ENNReal.ofReal (ρ ^ s))
        atTop (𝓝 (t * cl * ENNReal.ofReal (ρ ^ s))) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr ENNReal.ofReal_ne_top)
      exact ENNReal.Tendsto.mul (hθ.comp hφ.tendsto_atTop) (Or.inr hcltop) hcl
        (Or.inl hclpos.ne')
    exact le_of_tendsto' hmul fun j ↦ (hc (φ j) x hx ρ hρ).1
  · have hmul : Tendsto (fun j ↦ c (φ j) * ENNReal.ofReal (ρ ^ s)) atTop
        (𝓝 (cl * ENNReal.ofReal (ρ ^ s))) :=
      ENNReal.Tendsto.mul_const hcl (Or.inr ENNReal.ofReal_ne_top)
    exact ge_of_tendsto' hmul fun j ↦ (hc (φ j) x hx ρ hρ).2
/-- The analogue of `exists_uniform_constant_of_tendsto` for the situation of Lemma 14.7 (2),
where the upper bound holds for balls with arbitrary centres. -/
lemma exists_uniform_constant_of_tendsto_ball {s θ₀ : ℝ} {t : ℝ≥0∞} {θ : ℕ → ℝ}
    {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : Measure.Regular ν) (hν0 : ν ≠ 0)
    (hθ₀ : 0 < θ₀) (hθlb : ∀ k, θ₀ ≤ θ k)
    (hθ : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t))
    (h : ∀ k, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  choose c hcpos hctop hclo hcup using h
  obtain ⟨R, -, hRpos⟩ := exists_ball_pos_of_ne_zero hν0
  obtain ⟨x₀, -, hx₀⟩ := exists_mem_support_of_measure_pos hRpos
  set V := ν (closedBall x₀ 1) with hV
  have hVpos : 0 < V :=
    lt_of_lt_of_le (measure_ball_pos_of_mem_support hx₀ one_pos)
      (measure_mono ball_subset_closedBall)
  have hVtop : V ≠ ∞ := (regular_measure_closedBall_lt_top hν x₀ 1).ne
  have hθ₀ne : ENNReal.ofReal θ₀ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hθ₀
  have hVle : ∀ k, V ≤ c k := by
    intro k
    simpa using hcup k x₀ 1 one_pos
  have hcub : ∀ k, ENNReal.ofReal θ₀ * c k ≤ V := by
    intro k
    have hk := hclo k x₀ hx₀ 1 one_pos
    simp only [Real.one_rpow, ENNReal.ofReal_one, mul_one] at hk
    exact le_trans (by gcongr; exact hθlb k) hk
  obtain ⟨cl, -, φ, hφ, hcl⟩ :=
    (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq (x := c) (fun k ↦ mem_univ _)
  have hclpos : 0 < cl := lt_of_lt_of_le hVpos (ge_of_tendsto' hcl fun j ↦ hVle (φ j))
  have hcltop : cl ≠ ∞ := by
    have hlim : ENNReal.ofReal θ₀ * cl ≤ V :=
      le_of_tendsto' (ENNReal.Tendsto.const_mul hcl (Or.inr ENNReal.ofReal_ne_top))
        fun j ↦ hcub (φ j)
    intro htop
    rw [htop, ENNReal.mul_top hθ₀ne] at hlim
    exact hVtop (top_le_iff.mp hlim)
  refine ⟨cl, hclpos, hcltop, fun x hx ρ hρ ↦ ?_, fun x ρ hρ ↦ ?_⟩
  · have hmul : Tendsto (fun j ↦ ENNReal.ofReal (θ (φ j)) * c (φ j) * ENNReal.ofReal (ρ ^ s))
        atTop (𝓝 (t * cl * ENNReal.ofReal (ρ ^ s))) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr ENNReal.ofReal_ne_top)
      exact ENNReal.Tendsto.mul (hθ.comp hφ.tendsto_atTop) (Or.inr hcltop) hcl
        (Or.inl hclpos.ne')
    exact le_of_tendsto' hmul fun j ↦ hclo (φ j) x hx ρ hρ
  · have hmul : Tendsto (fun j ↦ c (φ j) * ENNReal.ofReal (ρ ^ s)) atTop
        (𝓝 (cl * ENNReal.ofReal (ρ ^ s))) :=
      ENNReal.Tendsto.mul_const hcl (Or.inr ENNReal.ofReal_ne_top)
    exact ge_of_tendsto' hmul fun j ↦ hcup (φ j) x ρ hρ



/-- The set of points `a ∈ F` which stay at distance at least `ε d` from every touching point
of a hole of `F` of size `d ≤ d₀`. -/
def farFromTouching (F : Set (EuclideanSpace ℝ (Fin n))) (ε d₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {a | a ∈ F ∧ ∀ y ∈ F, ∀ z : EuclideanSpace ℝ (Fin n), dist z y = infDist z F →
    0 < infDist z F → infDist z F ≤ d₀ → ε * infDist z F ≤ dist y a}
lemma isClosed_farFromTouching {F : Set (EuclideanSpace ℝ (Fin n))} (hF : IsClosed F)
    (ε d₀ : ℝ) : IsClosed (farFromTouching F ε d₀) := by
  have hrw : farFromTouching F ε d₀ = F ∩ ⋂ (y : EuclideanSpace ℝ (Fin n)) (_ : y ∈ F)
      (z : EuclideanSpace ℝ (Fin n)) (_ : dist z y = infDist z F) (_ : 0 < infDist z F)
      (_ : infDist z F ≤ d₀), {a | ε * infDist z F ≤ dist y a} := by
    ext a
    simp only [farFromTouching, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [hrw]
  refine hF.inter (isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun z ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_)
  exact isClosed_le continuous_const (continuous_const.dist continuous_id)
/-- **Almost no point of `F` is uniformly far from all touching points.** -/
theorem measure_farFromTouching_eq_zero {s p q r₀ ε d₀ : ℝ} (hsn : s < n)
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd₀ : 0 < d₀)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    {F : Set (EuclideanSpace ℝ (Fin n))} (hFclosed : IsClosed F)
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ)) :
    μ (farFromTouching F ε d₀) = 0 := by
  obtain ⟨κ, hκ0, hκ1, hhole⟩ := exists_hole_of_ball_bounds hsn hp hq μ hμ hupper hlower
  set B := farFromTouching F ε d₀ with hBdef
  obtain ⟨N, hN0, hN⟩ :=
    exists_null_of_not_density_point μ hμ (isClosed_farFromTouching hFclosed ε d₀).measurableSet
  have hsub : B ⊆ N := by
    intro a haB
    by_contra haN
    obtain ⟨haF, haprop⟩ := haB
    -- the proportion of the measure of a small ball which is guaranteed to miss `B`
    set γ : ℝ≥0∞ := ENNReal.ofReal (p * (ε * κ / 2) ^ s / (q * 3 ^ s)) with hγdef
    have hγpos : 0 < γ := by
      rw [hγdef, ENNReal.ofReal_pos]
      have h1 : (0 : ℝ) < (ε * κ / 2) ^ s := Real.rpow_pos_of_pos (by positivity) s
      have h2 : (0 : ℝ) < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      positivity
    have hγtop : γ ≠ ∞ := ENNReal.ofReal_ne_top
    -- the density property of `a`
    have hev := hN a ⟨⟨haF, haprop⟩, haN⟩ (γ / 2) (ENNReal.half_pos hγpos.ne')
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨η, hη, hh⟩ := hev
    -- a scale which is small enough for all the constraints
    set δ : ℝ := min (η / 4) (min (r₀ / 4) d₀) with hδdef
    have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) hd₀)
    have hδη : 3 * δ < η := by
      have : δ ≤ η / 4 := min_le_left _ _
      linarith
    have hδr₀ : 3 * δ < r₀ := by
      have : δ ≤ r₀ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hδd₀ : δ ≤ d₀ := le_trans (min_le_right _ _) (min_le_right _ _)
    have hδhalf : δ < r₀ / 2 := by linarith
    -- the hole and its touching point
    obtain ⟨z, hzdist, hzfar⟩ := hhole a haF δ hδ hδhalf
    set d : ℝ := infDist z F with hddef
    have hdpos : 0 < d := lt_trans (by positivity) hzfar
    have hdle : d ≤ δ := le_trans (infDist_le_dist_of_mem haF) hzdist
    obtain ⟨y, hyF, hyd⟩ := hFclosed.exists_infDist_eq_dist ⟨a, haF⟩ z
    have hya : dist y a ≤ 2 * δ := by
      have h1 : dist y z = d := by rw [dist_comm, ← hyd]
      have h2 : dist y a ≤ dist y z + dist z a := dist_triangle _ _ _
      rw [h1] at h2
      linarith
    -- a ball around the touching point which misses `B`
    set w : ℝ := ε * κ * δ / 2 with hwdef
    have hwpos : 0 < w := by positivity
    have hwδ : w ≤ δ := by
      have h1 : ε * κ ≤ 1 := by nlinarith
      rw [hwdef]
      nlinarith
    have hwd : w < ε * d := by
      have h1 : ε * (κ * δ) < ε * d := by
        exact mul_lt_mul_of_pos_left hzfar hε
      rw [hwdef]
      nlinarith
    have hball : closedBall y w ⊆ closedBall a (3 * δ) \ B := by
      intro b hb
      have hby : dist b y ≤ w := mem_closedBall.mp hb
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall]
        have : dist b a ≤ dist b y + dist y a := dist_triangle _ _ _
        linarith
      · intro hbB
        have := hbB.2 y hyF z hyd.symm hdpos (le_trans hdle hδd₀)
        rw [dist_comm y b] at this
        linarith
    -- the two sides of the density inequality
    have hlow2 : ENNReal.ofReal (p * w ^ s) ≤ μ (closedBall y w) :=
      hlower y hyF w hwpos (by linarith)
    have hMup : μ (closedBall a (3 * δ)) ≤ ENNReal.ofReal (q * (3 * δ) ^ s) :=
      hupper a haF _ (by linarith) hδr₀
    have hMlow : ENNReal.ofReal (p * (3 * δ) ^ s) ≤ μ (closedBall a (3 * δ)) :=
      hlower a haF _ (by linarith) hδr₀
    have hdiff : ENNReal.ofReal (p * w ^ s) ≤ μ (closedBall a (3 * δ) \ B) :=
      le_trans hlow2 (measure_mono hball)
    have hdens : μ (closedBall a (3 * δ) \ B) ≤ γ / 2 * μ (closedBall a (3 * δ)) := by
      have hd1 : dist (3 * δ) (0 : ℝ) < η := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 3 * δ)]
        exact hδη
      have hd2 : (0 : ℝ) < 3 * δ := by positivity
      exact hh hd1 hd2
    -- the identity relating `γ` to the two bounds
    have hident : γ * ENNReal.ofReal (q * (3 * δ) ^ s) = ENNReal.ofReal (p * w ^ s) := by
      rw [hγdef, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have h3 : (3 * δ) ^ s = (3 : ℝ) ^ s * δ ^ s := Real.mul_rpow (by norm_num) hδ.le
      have hw : w ^ s = (ε * κ / 2) ^ s * δ ^ s := by
        rw [hwdef, show ε * κ * δ / 2 = (ε * κ / 2) * δ by ring]
        exact Real.mul_rpow (by positivity) hδ.le
      have h3pos : (0 : ℝ) < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      rw [h3, hw]
      field_simp
    -- and the contradiction
    set M : ℝ≥0∞ := μ (closedBall a (3 * δ)) with hM
    have hM0 : M ≠ 0 := by
      have : (0 : ℝ≥0∞) < ENNReal.ofReal (p * (3 * δ) ^ s) := by
        rw [ENNReal.ofReal_pos]
        have : (0 : ℝ) < (3 * δ) ^ s := Real.rpow_pos_of_pos (by linarith) s
        positivity
      exact (lt_of_lt_of_le this hMlow).ne'
    have hMtop : M ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMup
    have hchain : γ * M ≤ γ / 2 * M := by
      calc γ * M ≤ γ * ENNReal.ofReal (q * (3 * δ) ^ s) := by gcongr
        _ = ENNReal.ofReal (p * w ^ s) := hident
        _ ≤ μ (closedBall a (3 * δ) \ B) := hdiff
        _ ≤ γ / 2 * M := hdens
    have hle : γ ≤ γ / 2 := (ENNReal.mul_le_mul_iff_left hM0 hMtop).mp hchain
    exact absurd hle (not_le.2 (ENNReal.half_lt_self hγpos.ne' hγtop))
  exact le_antisymm (le_trans (measure_mono hsub) hN0.le) (zero_le)
/-- **At almost every point of `F` there are touching points of relatively large holes.**
If the balls centred on the closed set `F` have measure comparable to `ρ ^ s` with `s < n`, then
outside a `μ`-null set every `a ∈ F` has, for every `ε > 0` and every `d₀ > 0`, a touching point
`y ∈ F` of a hole `B (z, d)` with `0 < d ≤ d₀` and `dist y a < ε d`. -/
theorem exists_touching_points_ae {s p q r₀ : ℝ} (hsn : s < n)
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    {F : Set (EuclideanSpace ℝ (Fin n))} (hFclosed : IsClosed F)
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ)) :
    ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ F \ N, ∀ ε d₀ : ℝ, 0 < ε → 0 < d₀ →
        ∃ y z : EuclideanSpace ℝ (Fin n), y ∈ F ∧ dist z y = infDist z F ∧
          0 < infDist z F ∧ infDist z F ≤ d₀ ∧ dist y a < ε * infDist z F := by
  classical
  refine ⟨⋃ ij : ℕ × ℕ, farFromTouching F (1 / (ij.1 + 1)) (1 / (ij.2 + 1)), ?_, ?_⟩
  · refine measure_iUnion_null fun ij ↦ ?_
    refine measure_farFromTouching_eq_zero hsn hp hq hr₀ (by positivity) ?_ (by positivity)
      μ hμ hFclosed hupper hlower
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (ij.1 : ℝ) := Nat.cast_nonneg _
    linarith
  · rintro a ⟨haF, haN⟩ ε d₀ hε hd₀
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hd₀
    have hnot : a ∉ farFromTouching F (1 / (i + 1)) (1 / (j + 1)) := fun h ↦
      haN (mem_iUnion.2 ⟨(i, j), h⟩)
    rw [farFromTouching, mem_ofPred_eq, not_and_or] at hnot
    have hfail : ¬ ∀ y ∈ F, ∀ z : EuclideanSpace ℝ (Fin n), dist z y = infDist z F →
        0 < infDist z F → infDist z F ≤ 1 / (j + 1) →
        1 / ((i : ℝ) + 1) * infDist z F ≤ dist y a := by
      rcases hnot with h | h
      · exact absurd haF h
      · exact h
    push Not at hfail
    obtain ⟨y, hyF, z, hz1, hz2, hz3, hz4⟩ := hfail
    refine ⟨y, z, hyF, hz1, hz2, le_trans hz3 hj.le, lt_of_lt_of_le hz4 ?_⟩
    exact mul_le_mul_of_nonneg_right hi.le hz2.le


/-- A point whose balls have positive measure lies in the support. -/
lemma mem_support_of_ball_lower_bound {s p r₀ : ℝ} (hp : 0 < p) (hr₀ : 0 < r₀)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)}
    (hlower : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ)) :
    a ∈ Measure.support μ := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  set ρ' : ℝ := min (ρ / 2) (r₀ / 2) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min (by positivity) (by positivity)
  have h1 : ρ' < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h2 : closedBall a ρ' ⊆ U :=
    subset_trans (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))) hball
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (p * ρ' ^ s) := by
    rw [ENNReal.ofReal_pos]
    have : (0 : ℝ) < ρ' ^ s := Real.rpow_pos_of_pos hρ'pos s
    positivity
  exact lt_of_lt_of_le hpos (le_trans (hlower ρ' hρ'pos h1) (measure_mono h2))
/-- Two-sided ball bounds at a single point `a` already give Mattila's assumption 14.3 (1)
at `a`. -/
lemma limsup_ball_ratio_lt_top_of_ball_bounds_at {s p q r₀ : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr₀ : 0 < r₀) {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)}
    (hupper : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (closedBall a ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ)) :
    limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞ := by
  set K : ℝ := q * (4 : ℝ) ^ s / p with hK
  have h4 : (0 : ℝ) < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hKpos : 0 < K := by rw [hK]; positivity
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      μ (ball a (2 * ρ)) / μ (ball a ρ) ≤ ENNReal.ofReal K := by
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (0 : ℝ) < ρ := self_mem_nhdsWithin
    have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r₀ / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by positivity))
    filter_upwards [h1, h2] with ρ hρ hρ'
    have hρ2 : (0 : ℝ) < 2 * ρ := by linarith
    have hρhalf : (0 : ℝ) < ρ / 2 := by linarith
    have hkey : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal K * μ (ball a ρ) := by
      have hup : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (q * (2 * ρ) ^ s) :=
        le_trans (measure_mono ball_subset_closedBall) (hupper _ hρ2 (by linarith))
      have hlo : ENNReal.ofReal (p * (ρ / 2) ^ s) ≤ μ (ball a ρ) :=
        le_trans (hlower _ hρhalf (by linarith))
          (measure_mono (closedBall_subset_ball (by linarith)))
      have hid : q * (2 * ρ) ^ s = K * (p * (ρ / 2) ^ s) := by
        have h2ρ : (2 : ℝ) * ρ = 4 * (ρ / 2) := by ring
        rw [h2ρ, Real.mul_rpow (by norm_num) hρhalf.le, hK]
        field_simp
      calc μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (q * (2 * ρ) ^ s) := hup
        _ = ENNReal.ofReal K * ENNReal.ofReal (p * (ρ / 2) ^ s) := by
            rw [hid, ENNReal.ofReal_mul hKpos.le]
        _ ≤ ENNReal.ofReal K * μ (ball a ρ) := by gcongr
    exact ENNReal.div_le_of_le_mul hkey
  exact lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) hev) ENNReal.ofReal_lt_top
/-- **Half-space tangent measures at asymptotic touching points.**
If `a ∈ F` is a density point of `F`, the balls centred on `F` carry measure comparable to
`ρ ^ s`, and `a` is an asymptotic touching point of holes of `F`, then `μ` has a tangent measure
at `a` whose support lies in a closed half-space. -/
theorem exists_halfSpace_tangentMeasure_of_touching {s p q r₀ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    {F : Set (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)} (haF : a ∈ F)
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ))
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ F) ≤ γ * μ (closedBall a ρ))
    (htouch : ∀ ε d₀ : ℝ, 0 < ε → 0 < d₀ →
      ∃ y z : EuclideanSpace ℝ (Fin n), y ∈ F ∧ dist z y = infDist z F ∧
        0 < infDist z F ∧ infDist z F ≤ d₀ ∧ dist y a < ε * infDist z F) :
    ∃ (e : EuclideanSpace ℝ (Fin n)) (ν : Measure (EuclideanSpace ℝ (Fin n))),
      ‖e‖ = 1 ∧ IsTangentMeasure μ ν a ∧
        Measure.support ν ⊆ {x : EuclideanSpace ℝ (Fin n) | 0 ≤ inner ℝ x e} := by
  classical
  -- the touching data at the scales `1 / (k + 1)`
  have hchoice : ∀ k : ℕ, ∃ yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      yz.1 ∈ F ∧ dist yz.2 yz.1 = infDist yz.2 F ∧ 0 < infDist yz.2 F ∧
        infDist yz.2 F ≤ 1 / ((k : ℝ) + 1) ∧
        dist yz.1 a < 1 / ((k : ℝ) + 1) * infDist yz.2 F := by
    intro k
    obtain ⟨y, z, h1, h2, h3, h4, h5⟩ := htouch (1 / ((k : ℝ) + 1)) (1 / ((k : ℝ) + 1))
      (by positivity) (by positivity)
    exact ⟨(y, z), h1, h2, h3, h4, h5⟩
  choose YZ hYF hYZdist hDpos hDle hYa using hchoice
  set D : ℕ → ℝ := fun k ↦ infDist (YZ k).2 F with hDdef
  set ee : ℕ → EuclideanSpace ℝ (Fin n) :=
    fun k ↦ (D k)⁻¹ • ((YZ k).1 - (YZ k).2) with heedef
  have hDpos' : ∀ k, 0 < D k := hDpos
  have hDle' : ∀ k, D k ≤ 1 / ((k : ℝ) + 1) := hDle
  have hYa' : ∀ k, dist (YZ k).1 a < 1 / ((k : ℝ) + 1) * D k := hYa
  have hnormYZ : ∀ k, ‖(YZ k).1 - (YZ k).2‖ = D k := by
    intro k
    rw [← dist_eq_norm, dist_comm]
    exact hYZdist k
  have heeval : ∀ k, ee k = (D k)⁻¹ • ((YZ k).1 - (YZ k).2) := fun _ ↦ rfl
  have hee : ∀ k, ‖ee k‖ = 1 := by
    intro k
    rw [heeval k, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hDpos' k)), hnormYZ k,
      inv_mul_cancel₀ (hDpos' k).ne']
  -- a subsequence along which the directions converge
  obtain ⟨e, hesphere, ψ, hψ, hetend⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).tendsto_subseq
      (x := ee) (fun k ↦ by simpa [mem_sphere_zero_iff_norm] using hee k)
  have henorm : ‖e‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hesphere
  -- the blow-up scales
  set S : ℕ → ℝ := fun j ↦ Real.sqrt ((j : ℝ) + 1) with hSdef
  have hS1 : ∀ j, (1 : ℝ) ≤ S j := by
    intro j
    have h : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    change (1 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1)
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_le_sqrt h
  have hSpos : ∀ j, 0 < S j := fun j ↦ lt_of_lt_of_le one_pos (hS1 j)
  have hSsq : ∀ j, S j ^ 2 = (j : ℝ) + 1 := fun j ↦ Real.sq_sqrt (by positivity)
  have hStend : Tendsto S atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  set rr : ℕ → ℝ := fun j ↦ D (ψ j) / S j with hrrdef
  have hrrpos : ∀ j, 0 < rr j := fun j ↦ div_pos (hDpos' _) (hSpos j)
  have hrrval : ∀ j, rr j = D (ψ j) / S j := fun _ ↦ rfl
  have hrrS : ∀ j, D (ψ j) = rr j * S j := by
    intro j
    rw [hrrval j, div_mul_cancel₀ _ (hSpos j).ne']
  have hψle : ∀ j : ℕ, (j : ℝ) ≤ (ψ j : ℝ) := by
    intro j
    exact_mod_cast hψ.le_apply
  have hrr0 : Tendsto rr atTop (𝓝 0) := by
    refine squeeze_zero (fun j ↦ (hrrpos j).le) (fun j ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : D (ψ j) ≤ 1 / ((ψ j : ℝ) + 1) := hDle' _
    have h3 : 1 / ((ψ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith [hψle j]
    calc rr j ≤ D (ψ j) := by
          rw [hrrval j, div_le_iff₀ (hSpos j)]
          nlinarith [hDpos' (ψ j), hS1 j]
      _ ≤ 1 / ((j : ℝ) + 1) := le_trans h1 h3
  -- the tangent measure obtained by blowing up along these scales
  have hlowa : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ) :=
    fun ρ h1 h2 ↦ hlower a haF ρ h1 h2
  have huppa : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (closedBall a ρ) ≤ ENNReal.ofReal (q * ρ ^ s) :=
    fun ρ h1 h2 ↦ hupper a haF ρ h1 h2
  have ha : a ∈ Measure.support μ := mem_support_of_ball_lower_bound hp hr₀ hlowa
  have hdoub := limsup_ball_ratio_lt_top_of_ball_bounds_at hp hq hr₀ huppa hlowa
  obtain ⟨φ, ν, hφ, htan, hconv⟩ :=
    exists_subseq_blowUp_weaklyConverges_tangentMeasure μ hμ a ha hdoub rr hrrpos hrr0
  have hseq : ∀ j, Measure.Regular
      ((μ (ball a (rr (φ j))))⁻¹ • Measure.map (blowUpMap a (rr (φ j))) μ) := fun j ↦
    regular_smul_map_blowUp hμ a (hrrpos _).ne'
      (ENNReal.inv_ne_top.2 (measure_ball_pos_of_mem_support ha (hrrpos _)).ne')
  refine ⟨e, ν, henorm, htan, ?_⟩
  intro x hx
  by_contra hcon
  simp only [mem_ofPred_eq, not_le] at hcon
  set β : ℝ := -inner ℝ x e with hβdef
  have hxe : inner ℝ x e = -β := by rw [hβdef]; ring
  have hβ : 0 < β := by rw [hβdef]; linarith
  -- four eventual consequences of `S j → ∞`
  have hineq1 : ∀ᶠ j in atTop, inner ℝ x (ee (ψ j)) ≤ -(β / 2) := by
    have hcont : Tendsto (fun j ↦ (inner ℝ x (ee (ψ j)) : ℝ)) atTop (𝓝 (inner ℝ x e)) := by
      have hc : Continuous fun y : EuclideanSpace ℝ (Fin n) ↦ (inner ℝ x y : ℝ) := by fun_prop
      exact (hc.tendsto e).comp hetend
    have hlt : (inner ℝ x e : ℝ) < -(β / 2) := by rw [hxe]; linarith
    exact ((tendsto_order.1 hcont).2 _ hlt).mono fun j hj ↦ hj.le
  have hineq2 : ∀ᶠ j in atTop, rr j * ‖x‖ ^ 2 ≤ D (ψ j) * (β / 2) := by
    filter_upwards [hStend.eventually_ge_atTop (2 * ‖x‖ ^ 2 / β)] with j hj
    rw [div_le_iff₀ hβ] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (hrrpos j).le
    rw [hrrS j]
    nlinarith [hrrpos j, hSpos j]
  have hineq3 : ∀ᶠ j in atTop, dist (YZ (ψ j)).1 a ≤ rr j * (β / 8) := by
    filter_upwards [hStend.eventually_ge_atTop (8 / β)] with j hj
    have hSβ : 8 ≤ S j * β := by
      rw [div_le_iff₀ hβ] at hj
      linarith
    have hA : dist (YZ (ψ j)).1 a < 1 / ((ψ j : ℝ) + 1) * D (ψ j) := hYa' _
    have h3 : 1 / ((ψ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith [hψle j]
    have hB : 1 / ((ψ j : ℝ) + 1) * D (ψ j) ≤ 1 / ((j : ℝ) + 1) * D (ψ j) :=
      mul_le_mul_of_nonneg_right h3 (hDpos' _).le
    have hC : 1 / ((j : ℝ) + 1) * D (ψ j) ≤ rr j * (β / 8) := by
      rw [← hSsq j, hrrS j, div_mul_eq_mul_div, one_mul,
        div_le_iff₀ (by positivity : (0 : ℝ) < S j ^ 2)]
      nlinarith [hrrpos j, hSpos j, mul_pos (hrrpos j) (hSpos j)]
    linarith
  have hineq4 : ∀ᶠ j in atTop, rr j * (β / 4) ≤ D (ψ j) := by
    filter_upwards [hStend.eventually_ge_atTop (β / 4)] with j hj
    rw [hrrS j]
    nlinarith [hrrpos j]
  -- the blow-ups eventually push the points of `F` away from `x`
  have hfar : ∀ᶠ i in atTop, ∀ y' ∈ F, rr i * (β / 8) ≤ dist y' (a + rr i • x) := by
    filter_upwards [hineq1, hineq2, hineq3, hineq4] with i h1 h2 h3 h4 y' hy'
    have hdpos : 0 < D (ψ i) := hDpos' _
    have hejn : ‖ee (ψ i)‖ = 1 := hee _
    have hZ : (YZ (ψ i)).1 - (YZ (ψ i)).2 = D (ψ i) • ee (ψ i) := by
      rw [heeval (ψ i), smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    set v : EuclideanSpace ℝ (Fin n) := rr i • x + D (ψ i) • ee (ψ i) with hvdef
    have hexp : ‖v‖ ^ 2 = rr i ^ 2 * ‖x‖ ^ 2
        + 2 * (rr i * D (ψ i)) * inner ℝ x (ee (ψ i)) + D (ψ i) ^ 2 := by
      rw [hvdef, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
        real_inner_smul_right, hejn]
      simp only [Real.norm_eq_abs, abs_of_pos (hrrpos i), abs_of_pos hdpos, mul_one]
      ring
    have hT : 0 ≤ D (ψ i) - rr i * (β / 4) := by linarith
    have hvle : ‖v‖ ≤ D (ψ i) - rr i * (β / 4) := by
      have hsq : ‖v‖ ^ 2 ≤ (D (ψ i) - rr i * (β / 4)) ^ 2 := by
        rw [hexp]
        have hA := mul_le_mul_of_nonneg_left h1 (mul_pos (hrrpos i) hdpos).le
        have hB := mul_le_mul_of_nonneg_left h2 (hrrpos i).le
        nlinarith [hA, hB, sq_nonneg (rr i * β), hrrpos i, hdpos]
      have hs := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg v), Real.sqrt_sq hT] at hs
    have hudiff : (a + rr i • x) - (YZ (ψ i)).2 = (a - (YZ (ψ i)).1) + v := by
      rw [hvdef, ← hZ]; abel
    have hnormu : ‖(a + rr i • x) - (YZ (ψ i)).2‖ ≤ dist (YZ (ψ i)).1 a + ‖v‖ := by
      rw [hudiff]
      refine le_trans (norm_add_le _ _) ?_
      have hrw : ‖a - (YZ (ψ i)).1‖ = dist (YZ (ψ i)).1 a := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [hrw]
    have hfarZ : D (ψ i) ≤ dist (YZ (ψ i)).2 y' := infDist_le_dist_of_mem hy'
    have htri : dist (YZ (ψ i)).2 y'
        ≤ dist (YZ (ψ i)).2 (a + rr i • x) + dist (a + rr i • x) y' := dist_triangle _ _ _
    have hZu : dist (YZ (ψ i)).2 (a + rr i • x) = ‖(a + rr i • x) - (YZ (ψ i)).2‖ := by
      rw [dist_comm, dist_eq_norm]
    rw [dist_comm y' (a + rr i • x)]
    linarith
  -- but the density of `F` at `a` forces points of `F` to be near `a + rr i • x`
  have hnear := tangent_exists_nearby_point_of_density hp hq hr₀ haF hupper hlower hdens
    (fun j ↦ hrrpos (φ j)) (hrr0.comp hφ.tendsto_atTop) hseq htan.1 hconv hx
    (show (0 : ℝ) < β / 8 by positivity)
  obtain ⟨j, hj1, hj2⟩ := (hnear.and (hφ.tendsto_atTop.eventually hfar)).exists
  obtain ⟨y', hy'F, hy'lt⟩ := hj1
  exact absurd hy'lt (not_lt.2 (hj2 y' hy'F))
