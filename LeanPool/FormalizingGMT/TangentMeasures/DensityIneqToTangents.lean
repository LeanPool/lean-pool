/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.TangentMeasures.Doubling
public import LeanPool.FormalizingGMT.TangentMeasures.DensityIneqToTangentsLemmas2

/-!
# Mattila's Lemma 14.7

This file assembles the ball-bound and good-set machinery into the three statements of
Mattila's Lemma 14.7.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-! ## Mattila, Lemma 14.7 (1), (2) and (3)
The three statements below are the almost-everywhere statements of Lemma 14.7; `A` is the set
`positiveFiniteDensitySet s μ` of points where `0 < Θ^s_*(μ, a) ≤ Θ^{*s}(μ, a) < ∞`, and
"`μ` almost all points `a ∈ A`" is expressed by exhibiting a `μ`-null exceptional set `E`. -/
/-- **Mattila, Lemma 14.7 (1).**
At `μ` almost all points `a` of `A = {a | 0 < Θ^s_*(μ, a) ≤ Θ^{*s}(μ, a) < ∞}`: for every
tangent measure `ν ∈ Tan (μ, a)` there is a positive (finite) number `c` such that
`t c r ^ s ≤ ν (B (x, r)) ≤ c r ^ s` for `x ∈ spt ν` and `0 < r < ∞`, where
`t = t (a) = Θ^s_*(μ, a) / Θ^{*s}(μ, a)`.
The proof needs no sign assumption on the exponent `s`. -/
theorem mattila_14_7_1 {s : ℝ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensitySet s μ \ E, ∀ ν, IsTangentMeasure μ ν a →
        ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
          ∀ x ∈ Measure.support ν, ∀ r : ℝ, 0 < r →
            RatioOfDensities s μ a * c * ENNReal.ofReal (r ^ s) ≤
              ν (closedBall x r) ∧
              ν (closedBall x r) ≤ c * ENNReal.ofReal (r ^ s) := by
  -- the exceptional set: the non-density points of the countably many sets `goodSet`
  have hex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ \ N, ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          μ (closedBall a ρ \ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ)
            ≤ γ * μ (closedBall a ρ) :=
    fun i ↦ exists_null_of_not_density_point μ hμ (isClosed_goodSet _ _ _ _ μ).measurableSet
  choose N hN0 hN using hex
  refine ⟨⋃ i, N i, measure_iUnion_null hN0, ?_⟩
  rintro a ⟨ha, haE⟩ ν htan
  obtain ⟨hνr, hν0, -⟩ := id htan
  obtain ⟨hl, hlu, hu⟩ := ha
  -- the sharp constant `t`
  set t := RatioOfDensities s μ a with ht
  have htpos : 0 < t := ENNReal.div_pos hl.ne' hu.ne
  have htle : t ≤ 1 := by
    rw [ht]
    exact ENNReal.div_le_of_le_mul (by simpa using hlu)
  have httop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
  set T := t.toReal with hT
  have hTpos : 0 < T := ENNReal.toReal_pos htpos.ne' httop
  have hTt : ENNReal.ofReal T = t := ENNReal.ofReal_toReal httop
  -- a sequence of constants increasing to `t`
  set θ : ℕ → ℝ := fun k ↦ T - T / (k + 2) with hθdef
  have hθpos : ∀ k, 0 < θ k := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : T / ((k : ℝ) + 2) < T := by
      rw [div_lt_iff₀ hk]
      nlinarith
    simpa [hθdef] using this
  have hθlb : ∀ k, T / 2 ≤ θ k := by
    intro k
    have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have : T / ((k : ℝ) + 2) ≤ T / 2 :=
      div_le_div_of_nonneg_left hTpos.le (by norm_num) hk
    simp only [hθdef]
    linarith
  have hθlt : ∀ k, ENNReal.ofReal (θ k) < t := by
    intro k
    rw [← hTt]
    refine (ENNReal.ofReal_lt_ofReal_iff hTpos).mpr ?_
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : 0 < T / ((k : ℝ) + 2) := by positivity
    simp only [hθdef]
    linarith
  have hθtend : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t) := by
    have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ ↦ T / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h2
    have h3 : Tendsto θ atTop (𝓝 T) := by
      simpa [hθdef] using tendsto_const_nhds.sub h1
    rw [← hTt]
    exact (ENNReal.continuous_ofReal.tendsto T).comp h3
  -- the estimate with constant `θ k`, for every `k`
  have hmain : ∀ k : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
    intro k
    obtain ⟨p, q, m, hp, hq, hθq, -, hmem⟩ :=
      exists_goodSet_mem ⟨hl, hlu, hu⟩ (hθpos k) (hθlt k)
    have haN : a ∉ N (p, q, m) := fun h ↦ haE (mem_iUnion.2 ⟨(p, q, m), h⟩)
    have hdens := hN (p, q, m) a ⟨hmem, haN⟩
    have hbounds : ∀ y ∈ goodSet s (p : ℝ) (q : ℝ) m μ, ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (m + 1) →
        ENNReal.ofReal (θ k * (q : ℝ) * ρ ^ s) ≤ μ (closedBall y ρ) ∧
          μ (closedBall y ρ) ≤ ENNReal.ofReal ((q : ℝ) * ρ ^ s) := by
      intro y hy ρ hρ hρm
      obtain ⟨h1, h2⟩ := hy ρ hρ hρm
      refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) h1, h2⟩
      have hpow : (0 : ℝ) ≤ ρ ^ s := Real.rpow_nonneg hρ.le s
      nlinarith
    have hr₀ : (0 : ℝ) < 1 / (m + 1) := by positivity
    exact tangent_ball_bounds_of_density_point hq (hθpos k) hr₀ μ hμ hbounds hmem hdens ν htan
  exact exists_uniform_constant_of_tendsto hνr hν0 (by positivity) hθlb hθtend hmain
/-- **Mattila, Lemma 14.7 (2).**
If, in addition, at `μ` almost all `z ∈ A` the upper bound
`limsup_{δ ↓ 0} sup {d (B) ^ (-s) μ (B) : B a closed ball with z ∈ B, d (B) < δ}
  ≤ Θ^{*s}(μ, z)`
holds, then at `μ` almost all `a ∈ A` every tangent measure `ν ∈ Tan (μ, a)` satisfies
`ν (B (x, r)) ≤ c r ^ s` for **all** `x ∈ ℝⁿ` and `r > 0`, with the same constant `c` as in
Lemma 14.7 (1). -/
theorem mattila_14_7_2 {s : ℝ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    (hball : ∃ E₀ : Set (EuclideanSpace ℝ (Fin n)), μ E₀ = 0 ∧
      ∀ z ∈ positiveFiniteDensitySet s μ \ E₀,
        upperBallSDensity s μ z ≤ dimensionalUpperDensity μ.toOuterMeasure s z) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensitySet s μ \ E, ∀ ν, IsTangentMeasure μ ν a →
        ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
          (∀ x ∈ Measure.support ν, ∀ r : ℝ, 0 < r →
            RatioOfDensities s μ a * c * ENNReal.ofReal (r ^ s) ≤
              ν (closedBall x r) ∧
              ν (closedBall x r) ≤ c * ENNReal.ofReal (r ^ s)) ∧
          ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
            ν (closedBall x r) ≤ c * ENNReal.ofReal (r ^ s) := by
  obtain ⟨E₀, hE₀, hballdens⟩ := hball
  have hex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ ∩ goodBallSet s (i.2.1 : ℝ) i.2.2 μ) \ N,
        ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          μ (closedBall a ρ \
              (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ ∩ goodBallSet s (i.2.1 : ℝ) i.2.2 μ))
            ≤ γ * μ (closedBall a ρ) :=
    fun i ↦ exists_null_of_not_density_point μ hμ
      (((isClosed_goodSet _ _ _ _ μ).inter (isClosed_goodBallSet _ _ _ μ)).measurableSet)
  choose N hN0 hN using hex
  have hUnull : μ (⋃ i, N i) = 0 := measure_iUnion_null hN0
  refine ⟨E₀ ∪ ⋃ i, N i, ?_, ?_⟩
  · refine le_antisymm (le_trans (measure_union_le _ _) ?_) zero_le
    rw [hE₀, hUnull]
    simp
  rintro a ⟨ha, haE⟩ ν htan
  have haE₀ : a ∉ E₀ := fun h ↦ haE (Set.mem_union_left _ h)
  have haU : a ∉ ⋃ i, N i := fun h ↦ haE (Set.mem_union_right _ h)
  have hbd : upperBallSDensity s μ a ≤ dimensionalUpperDensity μ.toOuterMeasure s a :=
    hballdens a ⟨ha, haE₀⟩
  obtain ⟨hνr, hν0, -⟩ := id htan
  obtain ⟨hl, hlu, hu⟩ := ha
  set t := RatioOfDensities s μ a with ht
  have htpos : 0 < t := ENNReal.div_pos hl.ne' hu.ne
  have htle : t ≤ 1 := by
    rw [ht]
    exact ENNReal.div_le_of_le_mul (by simpa using hlu)
  have httop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
  set T := t.toReal with hT
  have hTpos : 0 < T := ENNReal.toReal_pos htpos.ne' httop
  have hTt : ENNReal.ofReal T = t := ENNReal.ofReal_toReal httop
  set θ : ℕ → ℝ := fun k ↦ T - T / (k + 2) with hθdef
  have hθpos : ∀ k, 0 < θ k := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : T / ((k : ℝ) + 2) < T := by
      rw [div_lt_iff₀ hk]
      nlinarith
    simpa [hθdef] using this
  have hθlb : ∀ k, T / 2 ≤ θ k := by
    intro k
    have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have : T / ((k : ℝ) + 2) ≤ T / 2 :=
      div_le_div_of_nonneg_left hTpos.le (by norm_num) hk
    simp only [hθdef]
    linarith
  have hθlt : ∀ k, ENNReal.ofReal (θ k) < t := by
    intro k
    rw [← hTt]
    refine (ENNReal.ofReal_lt_ofReal_iff hTpos).mpr ?_
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : 0 < T / ((k : ℝ) + 2) := by positivity
    simp only [hθdef]
    linarith
  have hθtend : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t) := by
    have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ ↦ T / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h2
    have h3 : Tendsto θ atTop (𝓝 T) := by
      simpa [hθdef] using tendsto_const_nhds.sub h1
    rw [← hTt]
    exact (ENNReal.continuous_ofReal.tendsto T).comp h3
  have hmain : ∀ k : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
    intro k
    obtain ⟨p, q, m, hp, hq, hθq, hqsup, hmem⟩ :=
      exists_goodSet_mem ⟨hl, hlu, hu⟩ (hθpos k) (hθlt k)
    obtain ⟨m', hmem'⟩ := exists_goodBallSet_mem hq hbd hqsup
    set M := max m m' with hM
    have hmemM : a ∈ goodSet s (p : ℝ) (q : ℝ) M μ :=
      goodSet_mono_nat (le_max_left _ _) hmem
    have hmemM' : a ∈ goodBallSet s (q : ℝ) M μ :=
      goodBallSet_mono_nat (le_max_right _ _) hmem'
    have haN : a ∉ N (p, q, M) := fun h ↦ haU (mem_iUnion.2 ⟨(p, q, M), h⟩)
    have hdens := hN (p, q, M) a ⟨⟨hmemM, hmemM'⟩, haN⟩
    have hbounds : ∀ y ∈ goodSet s (p : ℝ) (q : ℝ) M μ ∩ goodBallSet s (q : ℝ) M μ,
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (M + 1) →
        ENNReal.ofReal (θ k * (q : ℝ) * ρ ^ s) ≤ μ (closedBall y ρ) ∧
          μ (closedBall y ρ) ≤ ENNReal.ofReal ((q : ℝ) * ρ ^ s) := by
      intro y hy ρ hρ hρm
      obtain ⟨h1, h2⟩ := hy.1 ρ hρ hρm
      refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) h1, h2⟩
      have hpow : (0 : ℝ) ≤ ρ ^ s := Real.rpow_nonneg hρ.le s
      nlinarith
    have hballbd : ∀ z ∈ goodSet s (p : ℝ) (q : ℝ) M μ ∩ goodBallSet s (q : ℝ) M μ,
        ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < 1 / (M + 1) →
        z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal ((q : ℝ) * w ^ s) :=
      fun z hz y w hw hwm hzmem ↦ hz.2 y w hw hwm hzmem
    have hr₀ : (0 : ℝ) < 1 / (M + 1) := by positivity
    exact tangent_ball_bounds_of_density_point_of_ball_bounds hq (hθpos k) hr₀ μ hμ hbounds
      hballbd ⟨hmemM, hmemM'⟩ hdens ν htan
  obtain ⟨c, hc0, hctop, hclo, hcup⟩ :=
    exists_uniform_constant_of_tendsto_ball hνr hν0 (by positivity : (0 : ℝ) < T / 2) hθlb
      hθtend hmain
  exact ⟨c, hc0, hctop, fun x hx ρ hρ ↦ ⟨hclo x hx ρ hρ, hcup x ρ hρ⟩, hcup⟩
/-- **Mattila, Lemma 14.7 (3).**
If `s < n`, then at `μ` almost all `a ∈ A` there are a unit vector `e` and a tangent measure
`ν ∈ Tan (μ, a)` whose support is contained in the half-space `{x | 0 ≤ x ⬝ e}`.
The proof runs as follows.  Almost every `a ∈ A` lies in one of the closed sets
`F = goodSet s p q m μ`, on which the measures of all small balls are comparable to `ρ ^ s`, and
is a `μ`-density point of `F`.  Since `s < n`, a Fubini argument shows that a definite proportion
of every ball centred on `F` is a hole of `F` (`exists_hole_of_ball_bounds`), and a density
argument then shows that almost every point of `F` is an *asymptotic touching point*: there are
points `y ∈ F` touching holes `B (z, d)` with `d → 0` and `dist y a` negligible compared with `d`
(`exists_touching_points_ae`).  Blowing `μ` up at `a` at scales `r` with `dist y a ≪ r ≪ d` turns
these holes into balls of radius tending to infinity whose boundaries pass arbitrarily close to
the origin; in the limit they exhaust an open half-space, so the resulting tangent measure is
supported in the complementary closed half-space
(`exists_halfSpace_tangentMeasure_of_touching`).
The proof turned out not to need any positivity assumption on the exponent `s`, so the
hypothesis `0 < s` was dropped from the statement, as in parts (1) and (2). -/
theorem mattila_14_7_3 {s : ℝ} (hsn : s < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensitySet s μ \ E,
        ∃ (e : EuclideanSpace ℝ (Fin n)) (ν : Measure (EuclideanSpace ℝ (Fin n))),
          ‖e‖ = 1 ∧ IsTangentMeasure μ ν a ∧
            Measure.support ν ⊆ {x : EuclideanSpace ℝ (Fin n) | 0 ≤ inner ℝ x e} := by
  classical
  -- the upper and lower bounds carried by the sets `goodSet s p q m μ`
  have hup : ∀ (p q : ℝ) (m : ℕ), ∀ y ∈ goodSet s p q m μ, ∀ ρ : ℝ, 0 < ρ →
      ρ < 1 / ((m : ℝ) + 1) → μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s) :=
    fun p q m y hy ρ h1 h2 ↦ (hy ρ h1 h2).2
  have hlo : ∀ (p q : ℝ) (m : ℕ), ∀ y ∈ goodSet s p q m μ, ∀ ρ : ℝ, 0 < ρ →
      ρ < 1 / ((m : ℝ) + 1) → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun p q m y hy ρ h1 h2 ↦ (hy ρ h1 h2).1
  -- the first family of exceptional sets: the non-density points of the good sets
  have hdensex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ \ N, ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          μ (closedBall a ρ \ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ)
            ≤ γ * μ (closedBall a ρ) :=
    fun i ↦ exists_null_of_not_density_point μ hμ (isClosed_goodSet _ _ _ _ μ).measurableSet
  choose N₁ hN₁0 hN₁ using hdensex
  -- the second family: the points which are far from all touching points
  have htouchex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      (0 < (i.1 : ℝ) → 0 < (i.2.1 : ℝ) →
        ∀ a ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ \ N, ∀ ε d₀ : ℝ, 0 < ε → 0 < d₀ →
          ∃ y z : EuclideanSpace ℝ (Fin n),
            y ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ ∧
              dist z y = infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ) ∧
              0 < infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ) ∧
              infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ) ≤ d₀ ∧
              dist y a < ε * infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ)) := by
    intro i
    by_cases hpq : 0 < (i.1 : ℝ) ∧ 0 < (i.2.1 : ℝ)
    · obtain ⟨N, hN0, hN⟩ :=
        exists_touching_points_ae hsn hpq.1 hpq.2
          (show (0 : ℝ) < 1 / ((i.2.2 : ℝ) + 1) by positivity) μ hμ
          (isClosed_goodSet _ _ _ _ μ) (hup _ _ _) (hlo _ _ _)
      exact ⟨N, hN0, fun _ _ ↦ hN⟩
    · exact ⟨∅, by simp, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hpq⟩
  choose N₂ hN₂0 hN₂ using htouchex
  refine ⟨⋃ i : ℚ × ℚ × ℕ, (N₁ i ∪ N₂ i), ?_, ?_⟩
  · refine measure_iUnion_null fun i ↦ le_antisymm ?_ zero_le
    calc μ (N₁ i ∪ N₂ i) ≤ μ (N₁ i) + μ (N₂ i) := measure_union_le _ _
      _ = 0 := by rw [hN₁0, hN₂0]; simp
  · rintro a ⟨ha, haE⟩
    obtain ⟨hl, hlu, hu⟩ := ha
    -- the density ratio at `a` is positive, so `a` lies in one of the good sets
    set t := RatioOfDensities s μ a with ht
    have htpos : 0 < t := ENNReal.div_pos hl.ne' hu.ne
    have htle : t ≤ 1 := by
      rw [ht]
      exact ENNReal.div_le_of_le_mul (by simpa using hlu)
    have httop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
    have hTpos : 0 < t.toReal := ENNReal.toReal_pos htpos.ne' httop
    have hTt : ENNReal.ofReal t.toReal = t := ENNReal.ofReal_toReal httop
    have hθlt : ENNReal.ofReal (t.toReal / 2) < t := by
      have h := (ENNReal.ofReal_lt_ofReal_iff hTpos).2 (half_lt_self hTpos)
      rwa [hTt] at h
    obtain ⟨p, q, m, hp, hq, -, -, hmem⟩ :=
      exists_goodSet_mem ⟨hl, hlu, hu⟩ (show (0 : ℝ) < t.toReal / 2 by positivity) hθlt
    have haN₁ : a ∉ N₁ (p, q, m) := fun h ↦ haE (mem_iUnion.2 ⟨(p, q, m), Or.inl h⟩)
    have haN₂ : a ∉ N₂ (p, q, m) := fun h ↦ haE (mem_iUnion.2 ⟨(p, q, m), Or.inr h⟩)
    exact exists_halfSpace_tangentMeasure_of_touching hp hq
      (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity) μ hμ hmem (hup _ _ _) (hlo _ _ _)
      (hN₁ (p, q, m) a ⟨hmem, haN₁⟩)
      (hN₂ (p, q, m) hp hq a ⟨hmem, haN₂⟩)
/-! ## Mattila, Lemma 14.7 (4) -/
/-- **Mattila, Lemma 14.7 (4).**
If there exist positive numbers `d`, `t` and `r₀` such that
`t d r ^ s ≤ μ (B (a, r)) ≤ d r ^ s` for all `a ∈ spt μ` and `0 < r < r₀`,
then at every point `a ∈ spt μ` the set `Tan (μ, a)` of tangent measures is nonempty, and every
tangent measure `ν ∈ Tan (μ, a)` satisfies the conclusion of Lemma 14.7 (1): there is a positive
finite constant `c` with `t c r ^ s ≤ ν (B (x, r)) ≤ c r ^ s` for all `x ∈ spt ν` and
`0 < r < ∞`. -/
theorem mattila_14_7_4 {s d t r₀ : ℝ} (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : Measure.Regular μ)
    (hbounds : ∀ y ∈ Measure.support μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) ∧
        μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ Measure.support μ) :
    (∃ ν, IsTangentMeasure μ ν a) ∧
      ∀ ν, IsTangentMeasure μ ν a →
        ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
          ∀ x ∈ Measure.support ν, ∀ ρ : ℝ, 0 < ρ →
            ENNReal.ofReal t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
              ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  have hupper : ∀ y ∈ Measure.support μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2
  have hlower : ∀ y ∈ Measure.support μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1
  have hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞ :=
    limsup_ball_ratio_lt_top_of_uniform hd ht hr₀ ha hupper hlower
  constructor
  · obtain ⟨φ, ν, -, htan, -⟩ :=
      exists_subseq_blowUp_weaklyConverges_tangentMeasure μ hμ a ha hdoub
        (fun i ↦ 1 / ((i : ℝ) + 1)) (fun i ↦ by positivity)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨ν, htan⟩
  · rintro ν ⟨hν, hν0, rs, cs, hrpos, hcpos, hcfin, hr0, hconv⟩
    obtain ⟨lam, -, φ, hφ, hlam⟩ := (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq
      (x := fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) (fun i ↦ mem_univ _)
    have hrpos' : ∀ j, 0 < rs (φ j) := fun j ↦ hrpos _
    have hr0' : Tendsto (fun j ↦ rs (φ j)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
    have hconv' : Measure.WeaklyConverges
        (fun j ↦ cs (φ j) • Measure.map (blowUpMap a (rs (φ j))) μ) ν :=
        hconv.comp hφ.tendsto_atTop
    have hseq' : ∀ j, Measure.Regular (cs (φ j) • Measure.map (blowUpMap a (rs (φ j))) μ) :=
      fun j ↦ regular_smul_map_blowUp hμ a (hrpos _).ne' (hcfin _)
    have hlamfin : lam ≠ ∞ :=
      tangent_scaling_lt_top hd ht hr₀ ha hlower hrpos' hr0' hlam hseq' hν hconv'
    have hlampos : 0 < lam :=
      tangent_scaling_pos hd hr₀ ha hupper hrpos' hr0' hlam hν0 hseq' hν hconv'
    refine ⟨ENNReal.ofReal d * lam, ?_, ?_, ?_⟩
    · exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hd).ne' hlampos.ne'
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamfin
    · intro x hx ρ hρ
      have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
          ∃ y ∈ Measure.support μ, dist y (a + rs (φ j) • x) < rs (φ j) * ε :=
        fun ε hε ↦ tangent_exists_nearby_support_point hrpos' hseq' hν hconv' hx hε
      have hup := tangent_closedBall_le hd.le hr₀ hupper hrpos' hr0' hlam hlamfin hseq' hν hconv'
        hnear hρ
      have hlo := le_tangent_closedBall hd.le ht.le hr₀ hlower hrpos' hr0' hlam hlamfin
        hseq' hν hconv' hnear hρ
      constructor
      · refine le_trans (le_of_eq ?_) hlo
        rw [ENNReal.ofReal_mul (mul_nonneg ht.le hd.le), ENNReal.ofReal_mul ht.le]
        ring
      · refine le_trans hup (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hd.le]
        ring
