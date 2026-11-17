/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.LocalLimit
public import LeanPool.RareSubtreePatterns.Setup.Toolkit

/-!
# The random-walk toolkit derived from `(H_α)` (Stage 5)

Source lines 837–883 and the toolbox uses at lines 1029–1041, 1138–1177, 1640–1647, 1987–1994
(inventory B06, B07, B09, B10, B14). The final export is

  `PoissonDeclumping.Stable.stableToolkit : StableDomain μ α a → StableToolkit μ α a`,

discharging the conditional interface `PoissonDeclumping.StableToolkit` of
`PoissonDeclumping.Setup.Toolkit` from the hypothesis `(H_α)` alone. Its fields are proved by:

* `regularlyVarying`: `PoissonDeclumping.Stable.regularlyVaryingSeq` (convergence of types);
* `sup_le`: `PoissonDeclumping.Stable.exists_walkProb_le` (local limit theorem plus
  boundedness of `d_α`, and `Ψ_m ≤ 1 ≤ a_N/a_m` for the finitely many small `m`);
* `tight`: `PoissonDeclumping.Stable.tight` (weak convergence against the continuous cutoff
  `min(1, (|y| - R)_+)`, and tightness of each of the finitely many small-time laws);
* `lattice`: `PoissonDeclumping.Stable.latticeLocal`, with `d = latticeSpan μ` and
  `L = d · d_α(0) > 0` (lattice local limit theorem, Lipschitz continuity of `d_α`,
  `d_α(0) > 0`).

The paper's functional convergence in the Skorokhod `J_1` topology (B07) is not proved: the
toolkit only needs marginal tightness (see `PoissonDeclumping.StableToolkit.tight`), and the
Skorokhod-representation step of B14 is replaced by the deterministic equicontinuity field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- **Uniform local bound** (inventory B10, "the local bound following from `eq:LL`", source
lines 1140, 1161): `Ψ_m(x) ≤ C / a_m` for all `m ≥ 1` and all `x ∈ ℤ`. -/
theorem exists_walkProb_le (h : StableDomain μ α a) :
    ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ x : ℤ, walkProb μ m x ≤ C / a m := by
  obtain ⟨M, hM0, hM⟩ := exists_stableDensity_le (α := α)
  obtain ⟨N, hN⟩ := localLimit h one_pos
  set d : ℝ := (latticeSpan μ : ℝ)
  set C : ℝ := max (d * M + 1) (a (max N 1)) with hC
  refine ⟨C, fun m hm x => ?_⟩
  have ham := h.pos m hm
  rw [le_div_iff₀ ham]
  by_cases hdx : (latticeSpan μ : ℤ) ∣ x + m
  · rcases le_or_gt N m with hNm | hNm
    · have h1 := hN m hNm x hdx
      have h2 : d * stableDensity α (x / a m) ≤ d * M :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM _)) (by positivity)
      have h3 : a m * walkProb μ m x ≤ d * M + 1 := by
        have := (abs_le.1 h1).2; linarith
      calc walkProb μ m x * a m = a m * walkProb μ m x := mul_comm _ _
        _ ≤ d * M + 1 := h3
        _ ≤ C := le_max_left _ _
    · have hP : walkProb μ m x ≤ 1 := by
        rw [walkProb_coe_nat]; exact measureReal_le_one
      have hP0 : 0 ≤ walkProb μ m x := by rw [walkProb_coe_nat]; exact measureReal_nonneg
      have : a m ≤ a (max N 1) := h.monotone (le_trans hNm.le (le_max_left _ _))
      calc walkProb μ m x * a m ≤ 1 * a m := by gcongr
        _ ≤ a (max N 1) := by linarith
        _ ≤ C := le_max_right _ _
  · rw [walkProb_eq_zero_of_not_dvd h hdx, zero_mul]
    exact le_trans (by positivity) (le_max_left _ _)

/-- The bounded continuous cutoff `y ↦ min 1 (max 0 (|y| - R))`. -/
noncomputable def cutoffFn (R : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => min 1 (max 0 (|y| - R)))
    (by fun_prop) 1 (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
      exact min_le_left _ _)

lemma cutoffFn_apply (R y : ℝ) : cutoffFn R y = min 1 (max 0 (|y| - R)) := rfl

/-- **Tightness of `S_m / a_m`** (inventory B07 in marginal form):
`sup_{m ≥ 1} P(|S_m| > K a_m) → 0` as `K → ∞`. -/
theorem tight (h : StableDomain μ α a) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (walkLaw μ m).real {x : ℤ | K * a m < |(x : ℝ)|} ≤ ε := by
  obtain ⟨ν, hν, -, hconv⟩ := h.converges
  -- the limit law: `∫ cutoff_R dν → 0`
  have hνt : Tendsto (fun R : ℝ => ∫ y, cutoffFn R y ∂ν) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ y, (fun _ => (0 : ℝ)) y ∂ν := by simp
    rw [h0]
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun R => (cutoffFn R).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun R => Eventually.of_forall fun y => ?_
      rw [cutoffFn_apply, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
      exact min_le_left _ _
    · exact integrable_const 1
    · refine Eventually.of_forall fun y => ?_
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop |y|] with R hR
      rw [cutoffFn_apply, max_eq_left (by linarith), min_eq_right zero_le_one]
  obtain ⟨R, hR⟩ := (hνt.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
  have hR' := hR (max R 0) (le_max_left _ _)
  set R' : ℝ := max R 0
  -- large `m`
  obtain ⟨N, hN⟩ := ((hconv (cutoffFn R')).eventually
    (gt_mem_nhds (show ∫ y, cutoffFn R' y ∂ν < ε by linarith))).exists_forall_of_atTop
  -- small `m`: each law is tight
  have hsmall : ∀ m ∈ Finset.range N, ∀ᶠ j : ℕ in atTop, 1 ≤ m →
      (walkLaw μ m).real {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|} ≤ ε := by
    intro m _
    by_cases hm : 1 ≤ m
    · have ham := h.pos m hm
      have ht : Tendsto (fun j : ℕ => (walkLaw μ m).real {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|})
          atTop (𝓝 0) := by
        have heq : ∀ j : ℕ, (walkLaw μ m).real {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|} =
            ∫ x, {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|}.indicator 1 x ∂(walkLaw μ m) :=
          fun j => (integral_indicator_one ((Set.to_countable _).measurableSet)).symm
        simp_rw [heq]
        have h0 : (0 : ℝ) = ∫ x, (fun _ => (0 : ℝ)) x ∂(walkLaw μ m) := by simp
        rw [h0]
        apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        · exact fun j => (measurable_of_countable _).aestronglyMeasurable
        · exact integrable_const 1
        · intro j; refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|}
          · simp [indicator_of_mem hx]
          · simp [indicator_of_notMem hx]
        · refine Eventually.of_forall fun x => ?_
          apply tendsto_const_nhds.congr'
          obtain ⟨J, hJ⟩ := exists_nat_ge (|(x : ℝ)| / a m)
          filter_upwards [eventually_ge_atTop J] with j hj
          have : |(x : ℝ)| ≤ j * a m := by
            rw [div_le_iff₀ ham] at hJ
            exact hJ.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ham.le)
          have hx : x ∉ {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|} := by
            simp only [mem_ofPred_eq, not_lt]; exact this
          simp [indicator_of_notMem hx]
      filter_upwards [ht.eventually (ge_mem_nhds hε)] with j hj _ using hj
    · exact Eventually.of_forall fun j hm' => absurd hm' hm
  obtain ⟨J, hJ⟩ := ((Finset.eventually_all (Finset.range N)).2 hsmall).exists_forall_of_atTop
  refine ⟨max (R' + 1) J, fun m hm => ?_⟩
  have ham := h.pos m hm
  rcases le_or_gt N m with hNm | hNm
  · -- large `m`: compare with the cutoff
    have h1 : (walkLaw μ m).real {x : ℤ | max (R' + 1) J * a m < |(x : ℝ)|} ≤
        ∫ y, cutoffFn R' y ∂((walkLaw μ m).map (fun z : ℤ => (z : ℝ) / a m)) := by
      set S : Set ℤ := {x : ℤ | max (R' + 1) J * a m < |(x : ℝ)|} with hS
      have hint1 : Integrable (S.indicator (1 : ℤ → ℝ)) (walkLaw μ m) :=
        Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            by_cases hx : x ∈ S
            · simp [indicator_of_mem hx]
            · simp [indicator_of_notMem hx])
      have hint2 : Integrable (fun x : ℤ => cutoffFn R' ((x : ℝ) / a m)) (walkLaw μ m) :=
        Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            rw [cutoffFn_apply, Real.norm_eq_abs,
              abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
            exact min_le_left _ _)
      rw [integral_map (measurable_of_countable _).aemeasurable
        (cutoffFn R').continuous.aestronglyMeasurable,
        ← integral_indicator_one (Set.to_countable S).measurableSet]
      apply integral_mono hint1 hint2
      intro x
      by_cases hx : x ∈ {x : ℤ | max (R' + 1) J * a m < |(x : ℝ)|}
      · rw [indicator_of_mem hx, Pi.one_apply]
        change 1 ≤ cutoffFn R' ((x : ℝ) / a m)
        rw [cutoffFn_apply]
        simp only [mem_ofPred_eq] at hx
        have : R' + 1 < |(x : ℝ) / a m| := by
          rw [abs_div, abs_of_pos ham, lt_div_iff₀ ham]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) ham.le) hx
        rw [min_eq_left (by rw [le_max_iff]; right; linarith)]
      · rw [indicator_of_notMem hx]
        change 0 ≤ cutoffFn R' ((x : ℝ) / a m)
        rw [cutoffFn_apply]
        exact le_min zero_le_one (le_max_left _ _)
    exact h1.trans (hN m hNm).le
  · have h2 := hJ J le_rfl m (Finset.mem_range.2 hNm) hm
    refine le_trans (measureReal_mono ?_) h2
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) ham.le) hx


/-- **The lattice local limit theorem in the toolkit form** (`LatticeLocal`), with
`d = latticeSpan μ` and `L = d · d_α(0) > 0`. -/
theorem latticeLocal (h : StableDomain μ α a) :
    LatticeLocal μ a (latticeSpan μ) (latticeSpan μ * stableDensity α 0) := by
  have hα := h.alpha_mem
  have hd0 : (0 : ℝ) < latticeSpan μ := by exact_mod_cast latticeSpan_pos h.critical h.nondegenerate
  set dR : ℝ := (latticeSpan μ : ℝ)
  set K : ℝ := (1 / (2 * Real.pi)) * ∫ θ : ℝ, |θ| * ‖stableCF α θ‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hLip : ∀ x y, |stableDensity α x - stableDensity α y| ≤ K * |x - y| :=
    fun x y => abs_stableDensity_sub_le hα x y
  refine ⟨latticeSpan_pos h.critical h.nondegenerate,
    mul_pos hd0 (stableDensity_zero_pos hα), ?_, ?_, ?_⟩
  · intro m x hx
    by_contra hd
    exact hx (walkProb_eq_zero_of_not_dvd h hd)
  · intro ε hε
    set η : ℝ := ε / (2 * (dR * K + 1)) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨N₀, hN₀⟩ := localLimit h (half_pos hε)
    refine ⟨η, hη0, max N₀ 1, fun n hn x hdx hx => ?_⟩
    have han := h.pos n (le_trans (le_max_right _ _) hn)
    have h1 := hN₀ n (le_trans (le_max_left _ _) hn) x hdx
    have h2 : |(x : ℝ) / a n - 0| ≤ η := by
      rw [sub_zero, abs_div, abs_of_pos han, div_le_iff₀ han]; exact hx
    have h3 : dR * |stableDensity α (x / a n) - stableDensity α 0| ≤ ε / 2 := by
      calc dR * |stableDensity α (x / a n) - stableDensity α 0| ≤ dR * (K * η) := by
            gcongr; exact (hLip _ _).trans (by gcongr)
        _ = ε / 2 * (dR * K / (dR * K + 1)) := by rw [hη]; field_simp
        _ ≤ ε / 2 * 1 := by
            gcongr; rw [div_le_one (by positivity)]; linarith
        _ = ε / 2 := mul_one _
    calc |a n * walkProb μ n x - dR * stableDensity α 0|
        = |(a n * walkProb μ n x - dR * stableDensity α (x / a n)) +
            dR * (stableDensity α (x / a n) - stableDensity α 0)| := by ring_nf
      _ ≤ |a n * walkProb μ n x - dR * stableDensity α (x / a n)| +
            |dR * (stableDensity α (x / a n) - stableDensity α 0)| := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          rw [abs_mul, abs_of_pos hd0]; exact add_le_add h1 h3
      _ = ε := by ring
  · intro ε hε
    set η : ℝ := ε / (3 * (dR * K + 1)) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨N₀, hN₀⟩ := localLimit h (show 0 < ε / 3 by positivity)
    refine ⟨η, hη0, max N₀ 1, fun n hn x y hdx hdy hxy => ?_⟩
    have han := h.pos n (le_trans (le_max_right _ _) hn)
    have h1 := hN₀ n (le_trans (le_max_left _ _) hn) x hdx
    have h1' := hN₀ n (le_trans (le_max_left _ _) hn) y hdy
    have h2 : |(x : ℝ) / a n - y / a n| ≤ η := by
      rw [← sub_div, abs_div, abs_of_pos han, div_le_iff₀ han]
      push_cast at hxy; exact hxy
    have h3 : dR * |stableDensity α (x / a n) - stableDensity α (y / a n)| ≤ ε / 3 := by
      calc dR * |stableDensity α (x / a n) - stableDensity α (y / a n)| ≤ dR * (K * η) := by
            gcongr; exact (hLip _ _).trans (by gcongr)
        _ = ε / 3 * (dR * K / (dR * K + 1)) := by rw [hη]; field_simp
        _ ≤ ε / 3 * 1 := by
            gcongr; rw [div_le_one (by positivity)]; linarith
        _ = ε / 3 := mul_one _
    calc |a n * walkProb μ n x - a n * walkProb μ n y|
        = |(a n * walkProb μ n x - dR * stableDensity α (x / a n)) -
            (a n * walkProb μ n y - dR * stableDensity α (y / a n)) +
            dR * (stableDensity α (x / a n) - stableDensity α (y / a n))| := by ring_nf
      _ ≤ |a n * walkProb μ n x - dR * stableDensity α (x / a n)| +
            |a n * walkProb μ n y - dR * stableDensity α (y / a n)| +
            |dR * (stableDensity α (x / a n) - stableDensity α (y / a n))| :=
          (abs_add_le _ _).trans (by linarith [abs_sub (a n * walkProb μ n x -
            dR * stableDensity α (x / a n)) (a n * walkProb μ n y - dR * stableDensity α (y / a
              n))])
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
          rw [abs_mul, abs_of_pos hd0]; exact add_le_add (add_le_add h1 h1') h3
      _ = ε := by ring

/-- **The stable random-walk toolkit, derived from `(H_α)`.** Every field of
`PoissonDeclumping.StableToolkit` follows from `StableDomain μ α a` alone. -/
theorem stableToolkit (h : StableDomain μ α a) : StableToolkit μ α a where
  critical := h.critical
  nondegenerate := h.nondegenerate
  alpha_mem := h.alpha_mem
  monotone := h.monotone
  pos := h.pos
  regularlyVarying := regularlyVaryingSeq h
  sup_le := exists_walkProb_le h
  tight := fun _ hε => tight h hε
  lattice := ⟨_, _, latticeLocal h⟩

end PoissonDeclumping.Stable
