/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.Slope.Recovery

/-!
# Density of smooth tests in the local-slope energy

Read `SmoothGradient.relaxation_le_localSlope` for the main contract, then
`LocalSlope.measurable_apply`, `LocalSlope.exists_patch` (the McShane patch),
`SmoothGradient.relaxation_le_localSlope_of_lipschitzWith` and
`SmoothGradient.relaxation_le_localSlope_of_admissible`.

## The argument

**Measurability.**  The local slope of a continuous function is the countable infimum, over the
radii `1 / (m + 1)`, of the secant suprema `LocalSlope.secant`, each of which is lower
semicontinuous: a witness `y` realizing a value above a threshold satisfies two strict
inequalities, both of which survive a small move of the base point, and the secant quotient is
continuous there because the witness is at positive distance.

**The McShane patch.**  For a globally `L`-Lipschitz `f` the slope is stratified into bands of
width `α`; each band is cut by the balls of a dense sequence into pieces of diameter below the
radius witnessing the slope bound, and `disjointed` turns the countable family into a Borel
partition on which `f` is Lipschitz with a constant within `α` of its slope.  Inner regularity
replaces each piece by a compact core, finitely many of which already carry all but `δ` of the
mass.  The cores are pairwise disjoint compacts, so they have a common separation radius; `f` is
extended from each core by McShane with the core's own constant and the extensions are glued by
linear cutoffs at that scale.  At most one block is active at any point, which is what keeps the
global Lipschitz constant at `9 L + 8 α`, independently of `δ`.

**Globally Lipschitz tests.**  Taking `α = δ = 1 / (n + 1)` the patches converge to `g` in
`L²(ν)` — they differ from `g`
by at most `2 L + 2 α` and only outside a set of mass `δ` — and smooth recovery bounds the
relaxation at each
patch by its asymptotic-Lipschitz energy, which a *measurable majorant* bounds by
`(1 + 4 α) · LocalSlope.energy ν g + 4 α + 4 α² + M² δ`.  No measurability of the asymptotic
Lipschitz constant is needed.  Lower semicontinuity of the relaxation finishes.

**General tests.**  A general admissible test is cut off by the smooth bump `scaled (n + 1)`; the
local Lipschitz product rule and the bounded-support Lipschitz bound
make the cutoff globally Lipschitz, dominated convergence gives `L²` convergence, and the
local-slope product bound with
Young's inequality bounds the energy of the cutoff.  The reverse inequality feeds this to
`LocalSlope.le_relaxation_of_lowerSemicontinuous`.

Closest literature: S. Eriksson-Bique, *Density of Lipschitz functions in energy*, Calc. Var. PDE
62 (2023), Art. 60, Thm 1.1, of which this Euclidean argument is an elementary special case.
-/

@[expose] public section

section

open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Energy

universe u

/-! ### The local slope of a continuous function is Borel -/

namespace LocalSlope

section Measurability

variable {X : Type*} [MetricSpace X]

/-- Each secant supremum of a continuous function is lower semicontinuous. -/
theorem lowerSemicontinuous_secant {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
    LowerSemicontinuous (secant f r) := by
  intro x t ht
  have ht' : t < ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x) := ht
  obtain ⟨y, hy⟩ := lt_iSup_iff.1 ht'
  obtain ⟨hyr, hyt⟩ := lt_iSup_iff.1 hy
  have hpos : 0 < dist y x := by
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
    · exfalso
      rw [← h0] at hyt
      simp at hyt
    · exact h0
  set q : X → ℝ := fun x' ↦ dist (f y) (f x') / dist y x' with hq
  have hcont : ContinuousAt (fun x' ↦ ENNReal.ofReal (q x')) x := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.div ?_ ?_ hpos.ne'
    · exact (continuous_const.dist hf).continuousAt
    · exact (continuous_const.dist continuous_id).continuousAt
  have hball : ∀ᶠ x' in 𝓝 x, dist y x' < r := by
    have hmem : Metric.ball y r ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_comm] using hyr)
    filter_upwards [hmem] with x' hx'
    simpa [Metric.mem_ball, dist_comm] using hx'
  have hgt : ∀ᶠ x' in 𝓝 x, t < ENNReal.ofReal (q x') := hcont (lt_mem_nhds hyt)
  filter_upwards [hball, hgt] with x' h1 h2
  refine lt_of_lt_of_le h2 ?_
  rw [secant]
  exact le_iSup₂_of_le y h1 le_rfl

/-- The local slope is the countable infimum of the secant suprema at the radii `1 / (m + 1)`. -/
theorem apply_eq_iInf_nat (f : X → ℝ) (x : X) :
    apply f x = ⨅ m : ℕ, secant f (1 / ((m : ℝ) + 1)) x := by
  refine le_antisymm (le_iInf fun m ↦ apply_le_secant f (by positivity) x) ?_
  rw [apply_eq_iInf_secant]
  refine le_iInf fun r ↦ le_iInf fun hr ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
  exact le_trans (iInf_le _ m) (secant_mono f hm.le x)

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The local slope of a continuous function is Borel measurable. -/
theorem measurable_apply {f : X → ℝ} (hf : Continuous f) : Measurable (apply f) := by
  have h : apply f = fun x ↦ ⨅ m : ℕ, secant f (1 / ((m : ℝ) + 1)) x :=
    funext fun x ↦ apply_eq_iInf_nat f x
  rw [h]
  exact Measurable.iInf fun m ↦ (lowerSemicontinuous_secant hf _).measurable

end Measurability

end LocalSlope

/-! ### Separation of finitely many disjoint compact sets -/

section Separation

variable {X : Type*} [MetricSpace X]

/-- Finitely many pairwise disjoint compact sets have one common thickening radius keeping the
thickenings pairwise disjoint. -/
theorem exists_thickening_pairwise_disjoint (N : ℕ) (Kc : ℕ → Set X)
    (hcomp : ∀ n, IsCompact (Kc n)) (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := by
  induction N with
  | zero => exact ⟨1, one_pos, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨ρ₁, hρ₁, hsep₁⟩ := ih
    set U : Set X := ⋃ i : Fin N, Kc (i : ℕ) with hU
    have hUcompact : IsCompact U := isCompact_iUnion fun i ↦ hcomp _
    have hdisjU : Disjoint (Kc N) U := by
      rw [hU, Set.disjoint_iUnion_right]
      intro i
      exact hdisj N i (by omega)
    obtain ⟨ρ₂, hρ₂, hsep₂⟩ := hdisjU.exists_thickenings (hcomp N) hUcompact.isClosed
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun i hi j hj hij ↦ ?_⟩
    have hsubU : ∀ k, k < N → Metric.thickening (min ρ₁ ρ₂) (Kc k) ⊆ Metric.thickening ρ₂ U := by
      intro k hk
      refine subset_trans (Metric.thickening_mono (min_le_right _ _) _) ?_
      exact Metric.thickening_subset_of_subset _ (Set.subset_iUnion (fun i : Fin N ↦ Kc i) ⟨k, hk⟩)
    have hsubN : Metric.thickening (min ρ₁ ρ₂) (Kc N) ⊆ Metric.thickening ρ₂ (Kc N) :=
      Metric.thickening_mono (min_le_right _ _) _
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Disjoint.mono (Metric.thickening_mono (min_le_left _ _) _)
          (Metric.thickening_mono (min_le_left _ _) _) (hsep₁ i hi' j hj' hij)
      · subst hj'
        exact Disjoint.mono (hsubU i hi') hsubN hsep₂.symm
    · subst hi'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Disjoint.mono hsubN (hsubU j hj') hsep₂
      · exact absurd hj'.symm hij

end Separation

/-! ### The gluing step of the McShane patch -/

namespace LocalSlope

section Gluing

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A sum with at most one active correction at each point has at most two
active corrections across a pair of points. -/
private theorem abs_sum_sub_le_of_card_support_le_one {ι X : Type*}
    [PseudoMetricSpace X] (S : Finset ι) (u : ι → X → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hcard : ∀ x, (S.filter fun i ↦ u i x ≠ 0).card ≤ 1)
    (hterm : ∀ i ∈ S, ∀ y z, |u i y - u i z| ≤ M * dist y z) (y z : X) :
    |∑ i ∈ S, (u i y - u i z)| ≤ 2 * (M * dist y z) := by
  classical
  have hsumP : ∑ n ∈ S, (u n y - u n z) =
      ∑ n ∈ S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0), (u n y - u n z) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hnP
    rw [Finset.mem_filter] at hnP
    push Not at hnP
    obtain ⟨h1, h2⟩ := hnP hn
    rw [h1, h2, sub_zero]
  have hPcard : (S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0)).card ≤ 2 := by
    have hsub : S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0) ⊆
        (S.filter fun n ↦ u n y ≠ 0) ∪ (S.filter fun n ↦ u n z ≠ 0) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rcases hn.2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hn.1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hn.1, h⟩)
    calc (S.filter (fun n ↦ u n y ≠ 0 ∨ u n z ≠ 0)).card
        ≤ ((S.filter fun n ↦ u n y ≠ 0) ∪ (S.filter fun n ↦ u n z ≠ 0)).card :=
          Finset.card_le_card hsub
      _ ≤ (S.filter fun n ↦ u n y ≠ 0).card + (S.filter fun n ↦ u n z ≠ 0).card :=
          Finset.card_union_le _ _
      _ ≤ 1 + 1 := add_le_add (hcard y) (hcard z)
      _ = 2 := rfl
  rw [hsumP]
  calc
    |∑ i ∈ S.filter (fun i ↦ u i y ≠ 0 ∨ u i z ≠ 0), (u i y - u i z)|
        ≤ ∑ i ∈ S.filter (fun i ↦ u i y ≠ 0 ∨ u i z ≠ 0), |u i y - u i z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (S.filter (fun i ↦ u i y ≠ 0 ∨ u i z ≠ 0)).card • (M * dist y z) :=
      Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ hterm i (Finset.mem_filter.mp hi).1 y z
    _ = ((S.filter (fun i ↦ u i y ≠ 0 ∨ u i z ≠ 0)).card : ℝ) * (M * dist y z) := by
      rw [nsmul_eq_mul]
    _ ≤ 2 * (M * dist y z) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM dist_nonneg)
      exact_mod_cast hPcard

omit [InnerProductSpace ℝ V] in
/-- Gluing step.  Finitely many pairwise disjoint compact cores, each carrying a Lipschitz
constant `c n ≤ L + α` for `f`, produce one globally Lipschitz patch with constant `9 L + 8 α`:
it agrees with `f` on the cores, differs from `f` by at most `2 L + 2 α` everywhere, and has
asymptotic Lipschitz constant at most `c n` at every point of the `n`-th core.

Extend each core separately, multiply its correction by a distance cutoff, then sum.
Disjoint neighborhoods leave at most one correction at each point; the private
finite-sum estimate controls the global Lipschitz bound. On a core, a shrinking-ball
estimate recovers the sharper local constant. -/
theorem exists_patch_of_isCompact {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0}
    (N : ℕ) (Kc : ℕ → Set V) (c : ℕ → ℝ≥0) (hcomp : ∀ n, IsCompact (Kc n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j))
    (hlipK : ∀ n, LipschitzOnWith (c n) f (Kc n)) (hcle : ∀ n, c n ≤ L + α) :
    ∃ F : V → ℝ, LipschitzWith (9 * L + 8 * α) F ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      (∀ n < N, ∀ x ∈ Kc n, F x = f x) ∧
      (∀ n < N, ∀ x ∈ Kc n, AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞)) := by
  classical
  -- Choose disjoint neighborhoods and extend the restriction of f on each core.

  -- Separate the compact pieces and choose localized corrections.
  obtain ⟨ρ₀, hρ₀, hsep₀⟩ := exists_thickening_pairwise_disjoint N Kc hcomp hdisj
  set ρ : ℝ := min ρ₀ 1 with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hsep : ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := fun i hi j hj hij ↦
    Disjoint.mono (Metric.thickening_mono (min_le_left _ _) _)
      (Metric.thickening_mono (min_le_left _ _) _) (hsep₀ i hi j hj hij)
  have hext : ∀ n, ∃ g : V → ℝ, LipschitzWith (c n) g ∧ Set.EqOn f g (Kc n) :=
    fun n ↦ (hlipK n).extend_real
  choose hfun hfunlip hfuneq using hext
  set S : Finset ℕ := (Finset.range N).filter (fun n ↦ (Kc n).Nonempty) with hSdef
  have hSmem : ∀ n ∈ S, n < N ∧ (Kc n).Nonempty := by
    intro n hn
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hn
    exact hn
  set φ : ℕ → V → ℝ := fun n x ↦ max (1 - Metric.infDist x (Kc n) / ρ) 0 with hφdef
  set w : ℕ → V → ℝ := fun n x ↦ hfun n x - f x with hwdef
  set u : ℕ → V → ℝ := fun n x ↦ φ n x * w n x with hudef
  set F : V → ℝ := fun x ↦ f x + ∑ n ∈ S, u n x with hFdef
  -- the cutoffs
  have hφ0 : ∀ n x, 0 ≤ φ n x := fun n x ↦ le_max_right _ _
  have hφ1 : ∀ n x, φ n x ≤ 1 := by
    intro n x
    refine max_le ?_ zero_le_one
    have : 0 ≤ Metric.infDist x (Kc n) / ρ := div_nonneg Metric.infDist_nonneg hρ.le
    linarith
  have hφmem : ∀ n x, x ∈ Kc n → φ n x = 1 := by
    intro n x hx
    simp [hφdef, Metric.infDist_zero_of_mem hx]
  have hφne : ∀ n x, φ n x ≠ 0 → Metric.infDist x (Kc n) < ρ := by
    intro n x hne
    by_contra hcon
    push Not at hcon
    refine hne ?_
    have hle : 1 - Metric.infDist x (Kc n) / ρ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hρ, one_mul]
      exact hcon
    simp [hφdef, max_eq_right hle]
  have hφlip : ∀ n y z, |φ n y - φ n z| ≤ dist y z / ρ := by
    intro n y z
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have h : (1 - Metric.infDist y (Kc n) / ρ) - (1 - Metric.infDist z (Kc n) / ρ) =
        (Metric.infDist z (Kc n) - Metric.infDist y (Kc n)) / ρ := by ring
    have hd : |Metric.infDist z (Kc n) - Metric.infDist y (Kc n)| ≤ dist y z := by
      have h2 := (Metric.lipschitz_infDist_pt (Kc n)).dist_le_mul z y
      rw [Real.dist_eq] at h2
      simpa [dist_comm z y] using h2
    rw [h, abs_div, abs_of_pos hρ]
    exact (div_le_div_iff_of_pos_right hρ).mpr hd
  -- the corrections
  have hwlip : ∀ n y z, |w n y - w n z| ≤ ((c n : ℝ) + L) * dist y z := by
    intro n y z
    have h1 : |hfun n y - hfun n z| ≤ (c n : ℝ) * dist y z := by
      simpa [Real.dist_eq] using (hfunlip n).dist_le_mul y z
    have h2 : |f y - f z| ≤ (L : ℝ) * dist y z := by
      simpa [Real.dist_eq] using hf.dist_le_mul y z
    have he : w n y - w n z = (hfun n y - hfun n z) - (f y - f z) := by
      simp only [hwdef]; ring
    rw [he]
    calc |(hfun n y - hfun n z) - (f y - f z)|
        ≤ |hfun n y - hfun n z| + |f y - f z| := abs_sub _ _
      _ ≤ (c n : ℝ) * dist y z + (L : ℝ) * dist y z := add_le_add h1 h2
      _ = ((c n : ℝ) + L) * dist y z := by ring
  have hwabs : ∀ n, (Kc n).Nonempty → ∀ x,
      |w n x| ≤ ((c n : ℝ) + L) * Metric.infDist x (Kc n) := by
    intro n hne x
    obtain ⟨p, hp, hdp⟩ := (hcomp n).exists_infDist_eq_dist hne x
    have h1 : |hfun n x - hfun n p| ≤ (c n : ℝ) * dist x p := by
      simpa [Real.dist_eq] using (hfunlip n).dist_le_mul x p
    have h2 : |f p - f x| ≤ (L : ℝ) * dist x p := by
      have := hf.dist_le_mul p x
      rw [Real.dist_eq, dist_comm p x] at this
      exact this
    have h3 : hfun n p = f p := (hfuneq n hp).symm
    have he : w n x = (hfun n x - hfun n p) + (f p - f x) := by
      simp only [hwdef, h3]; ring
    rw [he, hdp]
    calc |(hfun n x - hfun n p) + (f p - f x)|
        ≤ |hfun n x - hfun n p| + |f p - f x| := abs_add_le _ _
      _ ≤ (c n : ℝ) * dist x p + (L : ℝ) * dist x p := add_le_add h1 h2
      _ = ((c n : ℝ) + L) * dist x p := by ring
  -- the blocks
  have hublock : ∀ n, (Kc n).Nonempty → ∀ y z,
      |u n y - u n z| ≤ 2 * ((c n : ℝ) + L) * dist y z := by
    intro n hne y z
    have hcL : (0 : ℝ) ≤ (c n : ℝ) + L := by positivity

    -- Control the correction across different cutoff supports.
    have key : ∀ y' z' : V, φ n z' ≠ 0 →
        |u n y' - u n z'| ≤ 2 * ((c n : ℝ) + L) * dist y' z' := by
      intro y' z' hz'
      have hdz : Metric.infDist z' (Kc n) < ρ := hφne n z' hz'
      have hwz : |w n z'| ≤ ((c n : ℝ) + L) * ρ :=
        (hwabs n hne z').trans (by nlinarith [Metric.infDist_nonneg (x := z') (s := Kc n)])
      have he : u n y' - u n z' = φ n y' * (w n y' - w n z') + w n z' * (φ n y' - φ n z') := by
        simp only [hudef]; ring
      rw [he]
      have h1 : |φ n y' * (w n y' - w n z')| ≤ ((c n : ℝ) + L) * dist y' z' := by
        rw [abs_mul, abs_of_nonneg (hφ0 n y')]
        calc φ n y' * |w n y' - w n z'| ≤ 1 * (((c n : ℝ) + L) * dist y' z') := by
              apply mul_le_mul (hφ1 n y') (hwlip n y' z') (abs_nonneg _) zero_le_one
          _ = ((c n : ℝ) + L) * dist y' z' := by ring
      have h2 : |w n z' * (φ n y' - φ n z')| ≤ ((c n : ℝ) + L) * dist y' z' := by
        rw [abs_mul]
        calc |w n z'| * |φ n y' - φ n z'| ≤ (((c n : ℝ) + L) * ρ) * (dist y' z' / ρ) := by
              apply mul_le_mul hwz (hφlip n y' z') (abs_nonneg _) (by positivity)
          _ = ((c n : ℝ) + L) * dist y' z' := by field_simp
      calc |φ n y' * (w n y' - w n z') + w n z' * (φ n y' - φ n z')|
          ≤ |φ n y' * (w n y' - w n z')| + |w n z' * (φ n y' - φ n z')| := abs_add_le _ _
        _ ≤ ((c n : ℝ) + L) * dist y' z' + ((c n : ℝ) + L) * dist y' z' := add_le_add h1 h2
        _ = 2 * ((c n : ℝ) + L) * dist y' z' := by ring
    by_cases hz : φ n z = 0
    · by_cases hy : φ n y = 0
      · simp only [hudef, hy, zero_mul, hz, sub_self, abs_zero, ge_iff_le]
        positivity
      · have := key z y hy
        rw [abs_sub_comm, dist_comm]
        exact this
    · exact key y z hz
  have huabs : ∀ n, (Kc n).Nonempty → ∀ x, |u n x| ≤ ((c n : ℝ) + L) * ρ := by
    intro n hne x
    by_cases hx : φ n x = 0
    · simp only [hudef, hx, zero_mul, abs_zero]
      positivity
    · rw [hudef]
      simp only
      rw [abs_mul, abs_of_nonneg (hφ0 n x)]
      calc φ n x * |w n x| ≤ 1 * (((c n : ℝ) + L) * Metric.infDist x (Kc n)) := by
            apply mul_le_mul (hφ1 n x) (hwabs n hne x) (abs_nonneg _) zero_le_one
        _ ≤ ((c n : ℝ) + L) * ρ := by
            have h1 : Metric.infDist x (Kc n) ≤ ρ := (hφne n x hx).le
            have : (0 : ℝ) ≤ (c n : ℝ) + L := by positivity
            nlinarith
  have hcbound : ∀ n, (c n : ℝ) + L ≤ 2 * (L : ℝ) + α := by
    intro n
    have := hcle n
    have : (c n : ℝ) ≤ (L : ℝ) + α := by exact_mod_cast this
    linarith
  -- at most one active block at each point
  have hunique : ∀ x, ∀ n ∈ S, ∀ n' ∈ S, φ n x ≠ 0 → φ n' x ≠ 0 → n = n' := by
    intro x n hn n' hn' hφn hφn'
    by_contra hne
    obtain ⟨hnN, hnne⟩ := hSmem n hn
    obtain ⟨hn'N, hn'ne⟩ := hSmem n' hn'
    have h1 : x ∈ Metric.thickening ρ (Kc n) :=
      (Metric.mem_thickening_iff_infDist_lt hnne).2 (hφne n x hφn)
    have h2 : x ∈ Metric.thickening ρ (Kc n') :=
      (Metric.mem_thickening_iff_infDist_lt hn'ne).2 (hφne n' x hφn')
    exact Set.disjoint_left.1 (hsep n hnN n' hn'N hne) h1 h2
  have hzero : ∀ x, ∀ n ∈ S, u n x ≠ 0 → φ n x ≠ 0 := by
    intro x n _ hu0 hφ0'
    exact hu0 (by simp [hudef, hφ0'])
  have hcardone : ∀ x, ((S.filter fun n ↦ u n x ≠ 0).card ≤ 1) := by
    intro x
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hunique x a ha.1 b hb.1 (hzero x a ha.1 ha.2) (hzero x b hb.1 hb.2)
  -- the patch is uniformly close to `f`
  have hclose : ∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ) := by
    intro x
    have hFx : F x - f x = ∑ n ∈ S, u n x := by simp [hFdef]
    rw [hFx, ← Finset.sum_filter_ne_zero S]
    obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.1 (hcardone x)
    rcases Finset.subset_singleton_iff.1 ha with h | h
    · rw [h]
      simp only [Finset.sum_empty, abs_zero, ge_iff_le]
      positivity
    · rw [h, Finset.sum_singleton]
      have haS : a ∈ S := by
        have : a ∈ S.filter fun n ↦ u n x ≠ 0 := by rw [h]; exact Finset.mem_singleton_self a
        exact (Finset.mem_filter.1 this).1
      have hne := (hSmem a haS).2
      calc |u a x| ≤ ((c a : ℝ) + L) * ρ := huabs a hne x
        _ ≤ (2 * (L : ℝ) + α) * 1 := by
            apply mul_le_mul (hcbound a) hρ1 hρ.le
            positivity
        _ ≤ 2 * (L : ℝ) + 2 * (α : ℝ) := by
            have : (0 : ℝ) ≤ α := α.coe_nonneg
            linarith
  -- the patch is globally Lipschitz
  have hFlip : LipschitzWith (9 * L + 8 * α) F := by
    -- Prove the patched function is Lipschitz and control its local slopes.
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    have hcoe : ((9 * L + 8 * α : ℝ≥0) : ℝ) = 9 * (L : ℝ) + 8 * (α : ℝ) := by push_cast; ring
    rw [Real.dist_eq, hcoe]
    have hFyz : F y - F z = (f y - f z) + ∑ n ∈ S, (u n y - u n z) := by
      simp [hFdef, Finset.sum_sub_distrib]
      ring
    have hsumbound : |∑ n ∈ S, (u n y - u n z)| ≤
        2 * (2 * (2 * (L : ℝ) + α) * dist y z) := by
      apply abs_sum_sub_le_of_card_support_le_one S u (2 * (2 * (L : ℝ) + α))
        (by positivity) hcardone
      intro n hn y z
      refine (hublock n (hSmem n hn).2 y z).trans ?_
      have hc := hcbound n
      nlinarith [dist_nonneg (x := y) (y := z)]
    have hf' : |f y - f z| ≤ (L : ℝ) * dist y z := by
      simpa [Real.dist_eq] using hf.dist_le_mul y z
    rw [hFyz]
    calc |(f y - f z) + ∑ n ∈ S, (u n y - u n z)|
        ≤ |f y - f z| + |∑ n ∈ S, (u n y - u n z)| :=
          abs_add_le _ _
      _ ≤ (L : ℝ) * dist y z + 2 * (2 * (2 * (L : ℝ) + α) * dist y z) :=
          add_le_add hf' hsumbound
      _ ≤ (9 * (L : ℝ) + 8 * (α : ℝ)) * dist y z := by
          have : (0 : ℝ) ≤ dist y z := dist_nonneg
          nlinarith [α.coe_nonneg, L.coe_nonneg]
  -- the patch agrees with `f` on the cores
  have hFeq : ∀ n < N, ∀ x ∈ Kc n, F x = f x := by
    intro n hn x hx
    have hnS : n ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn, ⟨x, hx⟩⟩
    have hφn : φ n x = 1 := hφmem n x hx
    have hsum : ∑ m ∈ S, u m x = 0 := by
      refine Finset.sum_eq_zero fun m hm ↦ ?_
      by_cases hmn : m = n
      · subst hmn
        have : w m x = 0 := by simp [hwdef, (hfuneq m hx).symm]
        simp [hudef, this]
      · have : φ m x = 0 := by
          by_contra hcon
          exact hmn (hunique x m hm n hnS hcon (by rw [hφn]; norm_num))
        simp [hudef, this]
    simp [hFdef, hsum]
  -- the asymptotic Lipschitz constant on the cores
  have hFslope : ∀ n < N, ∀ x ∈ Kc n, AsymptoticLipschitz.apply F x ≤ (c n : ℝ≥0∞) := by
    intro n hn x hx
    have hnS : n ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn, ⟨x, hx⟩⟩
    have hne : (Kc n).Nonempty := ⟨x, hx⟩
    have hcL : (0 : ℝ) ≤ (c n : ℝ) + L := by positivity
    -- on a ball of radius `r ≤ ρ` around `x` only the `n`-th block is active
    have hlocal : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ y : V, dist y x < r →
        F y = hfun n y - (Metric.infDist y (Kc n) / ρ) * w n y := by
      intro r hr0 hrρ y hy
      have hdy : Metric.infDist y (Kc n) < ρ := by
        calc Metric.infDist y (Kc n) ≤ dist y x := Metric.infDist_le_dist_of_mem hx
          _ < r := hy
          _ ≤ ρ := hrρ
      have hφy : φ n y = 1 - Metric.infDist y (Kc n) / ρ := by
        refine max_eq_left ?_
        rw [le_sub_comm, sub_zero, div_le_one hρ]
        exact hdy.le
      have hsum : ∑ m ∈ S, u m y = u n y := by
        refine Finset.sum_eq_single_of_mem n hnS fun m hm hmn ↦ ?_
        have : φ m y = 0 := by
          by_contra hcon
          refine hmn (hunique y m hm n hnS hcon ?_)
          rw [hφy]
          intro hzero'
          rw [sub_eq_zero] at hzero'
          rw [eq_comm, div_eq_one_iff_eq hρ.ne'] at hzero'
          exact absurd hzero' hdy.ne
        simp [hudef, this]
      have hfy : f y = hfun n y - w n y := by simp [hwdef]
      rw [hFdef]
      simp only
      rw [hsum, hudef]
      simp only
      rw [hφy, hfy]
      ring
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hεr : (0 : ℝ) < (ε : ℝ) := hε
    have hd : (0 : ℝ) < 2 * ((c n : ℝ) + L) + 1 := by positivity
    set t : ℝ := ((ε : ℝ) * ρ) / (2 * ((c n : ℝ) + L) + 1) with htdef

    -- Choose the final scale to meet the uniform approximation error.
    have ht0 : 0 < t := div_pos (mul_pos hεr hρ) hd
    have hteq : (2 * ((c n : ℝ) + L) + 1) * t = (ε : ℝ) * ρ := by
      rw [htdef]; field_simp
    set r : ℝ := min ρ t with hrdef
    have hr0 : 0 < r := lt_min hρ ht0
    have hrρ : r ≤ ρ := min_le_left _ _
    have hsmall : 2 * r * ((c n : ℝ) + L) / ρ ≤ (ε : ℝ) := by
      have hb : r ≤ t := min_le_right _ _
      rw [div_le_iff₀ hρ]
      nlinarith [mul_le_mul_of_nonneg_right hb hcL, ht0.le, hcL]
    have hball : ∀ y z : V, dist y x < r → dist z x < r →
        dist (F y) (F z) ≤ ((c n : ℝ) + 2 * r * ((c n : ℝ) + L) / ρ) * dist y z := by
      intro y z hy hz
      rw [hlocal r hr0 hrρ y hy, hlocal r hr0 hrρ z hz]
      set θ : V → ℝ := fun v ↦ Metric.infDist v (Kc n) / ρ with hθ
      have hθ0 : ∀ v : V, 0 ≤ θ v := fun v ↦ div_nonneg Metric.infDist_nonneg hρ.le
      have hθy : θ y ≤ r / ρ := by
        change Metric.infDist y (Kc n) / ρ ≤ r / ρ
        exact (div_le_div_iff_of_pos_right hρ).mpr
          ((Metric.infDist_le_dist_of_mem hx).trans hy.le)
      have hθz : θ z ≤ r / ρ := by
        change Metric.infDist z (Kc n) / ρ ≤ r / ρ
        exact (div_le_div_iff_of_pos_right hρ).mpr
          ((Metric.infDist_le_dist_of_mem hx).trans hz.le)
      have hθlip : |θ y - θ z| ≤ dist y z / ρ := by
        change |Metric.infDist y (Kc n) / ρ - Metric.infDist z (Kc n) / ρ| ≤ dist y z / ρ
        rw [div_sub_div_same, abs_div, abs_of_pos hρ]
        have hdd : |Metric.infDist y (Kc n) - Metric.infDist z (Kc n)| ≤ dist y z := by
          have h2 := (Metric.lipschitz_infDist_pt (Kc n)).dist_le_mul y z
          rw [Real.dist_eq] at h2
          simpa using h2
        exact (div_le_div_iff_of_pos_right hρ).mpr hdd
      have hwz : |w n z| ≤ ((c n : ℝ) + L) * r := by
        refine (hwabs n hne z).trans ?_
        apply mul_le_mul_of_nonneg_left _ hcL
        exact (Metric.infDist_le_dist_of_mem hx).trans hz.le
      have he : (hfun n y - θ y * w n y) - (hfun n z - θ z * w n z) =
          (hfun n y - hfun n z) - (θ y * (w n y - w n z) + w n z * (θ y - θ z)) := by ring
      rw [Real.dist_eq, he]
      have h1 : |hfun n y - hfun n z| ≤ (c n : ℝ) * dist y z := by
        simpa [Real.dist_eq] using (hfunlip n).dist_le_mul y z
      have h2 : |θ y * (w n y - w n z)| ≤ (r / ρ) * (((c n : ℝ) + L) * dist y z) := by
        rw [abs_mul, abs_of_nonneg (hθ0 y)]
        exact mul_le_mul hθy (hwlip n y z) (abs_nonneg _) (div_nonneg hr0.le hρ.le)
      have h3 : |w n z * (θ y - θ z)| ≤ (((c n : ℝ) + L) * r) * (dist y z / ρ) := by
        rw [abs_mul]
        exact mul_le_mul hwz hθlip (abs_nonneg _) (mul_nonneg hcL hr0.le)
      calc |(hfun n y - hfun n z) - (θ y * (w n y - w n z) + w n z * (θ y - θ z))|
          ≤ |hfun n y - hfun n z| + |θ y * (w n y - w n z) + w n z * (θ y - θ z)| :=
            abs_sub _ _
        _ ≤ |hfun n y - hfun n z| + (|θ y * (w n y - w n z)| + |w n z * (θ y - θ z)|) := by
            gcongr
            exact abs_add_le _ _
        _ ≤ (c n : ℝ) * dist y z + ((r / ρ) * (((c n : ℝ) + L) * dist y z) +
              (((c n : ℝ) + L) * r) * (dist y z / ρ)) := by
            gcongr
        _ = ((c n : ℝ) + 2 * r * ((c n : ℝ) + L) / ρ) * dist y z := by field_simp; ring
    have hbd := AsymptoticLipschitz.secant_le_ofReal
      (f := F) (r := r) (x := x)
      (by positivity : (0 : ℝ) ≤ (c n : ℝ) + 2 * r * ((c n : ℝ) + L) / ρ)
      (fun y z hy hz ↦ hball y z hy hz)
    refine (AsymptoticLipschitz.apply_le_secant F hr0 x).trans (hbd.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal (p := c n), ← ENNReal.ofReal_coe_nnreal (p := ε),
      ← ENNReal.ofReal_add (c n).coe_nonneg ε.coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  exact ⟨F, hFlip, hclose, hFeq, hFslope⟩

end Gluing

end LocalSlope

/-! ### The McShane patch -/

namespace LocalSlope

section Patch

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] in
/-- The Borel partition underlying the McShane patch: slope bands of width `α` cut by the balls
of a dense sequence, disjointed.  On each piece `f` is Lipschitz with a constant within `α` of
its local slope, and at most `L + α` overall. -/
theorem exists_partition {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0} (hα : 0 < α) :
    ∃ (D : ℕ → Set V) (c : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (D i)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ i, D i) = Set.univ ∧ (∀ i, c i ≤ L + α) ∧
      (∀ i, LipschitzOnWith (c i) f (D i)) ∧
      (∀ i, ∀ x ∈ D i, ((c i : ℝ≥0∞)) ≤ apply f x + (α : ℝ≥0∞)) := by
  classical
  have hcont : Continuous f := hf.continuous
  have hsL : ∀ x, apply f x ≤ (L : ℝ≥0∞) := fun x ↦
    (apply_le_asymptoticLipschitz f x).trans (AsymptoticLipschitz.apply_le_of_lipschitzWith hf x)
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq V
  set P : ℕ → ℕ → Set V := fun k m ↦
    {x | (((k : ℝ≥0) * α : ℝ≥0) : ℝ≥0∞) ≤ apply f x} ∩
      {x | apply f x < ((((k : ℝ≥0) + 1) * α : ℝ≥0) : ℝ≥0∞)} ∩
      {x | secant f (1 / ((m : ℝ) + 1)) x ≤ ((((k : ℝ≥0) + 1) * α : ℝ≥0) : ℝ≥0∞)} with hPdef
  set A : ℕ → ℕ → ℕ → Set V := fun k m n ↦ P k m ∩ Metric.ball (v n) (1 / (4 * ((m : ℝ) + 1)))
    with hAdef
  set e : ℕ ≃ ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm with hedef
  set Aseq : ℕ → Set V := fun i ↦ A (e i).1 (e i).2.1 (e i).2.2 with hAseq
  have hmeasP : ∀ k m, MeasurableSet (P k m) := by
    intro k m
    refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
    · exact measurableSet_le measurable_const (measurable_apply hcont)
    · exact measurableSet_lt (measurable_apply hcont) measurable_const
    · exact (lowerSemicontinuous_secant hcont _).measurable measurableSet_Iic
  have hmeasA : ∀ i, MeasurableSet (Aseq i) := fun i ↦
    (hmeasP _ _).inter Metric.isOpen_ball.measurableSet
  set D : ℕ → Set V := disjointed Aseq with hDdef
  set c : ℕ → ℝ≥0 := fun i ↦ min ((((e i).1 : ℝ≥0) + 1) * α) (L + α) with hcdef
  have hDsub : ∀ i, D i ⊆ Aseq i := fun i ↦ disjointed_subset Aseq i
  have hcover : (⋃ i, Aseq i) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hfin : apply f x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hsL x)
    set t : ℝ := (apply f x).toReal with htdef
    have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
    have hteq : apply f x = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfin).symm
    set k : ℕ := ⌊t / (α : ℝ)⌋₊ with hkdef
    have hαpos : (0 : ℝ) < (α : ℝ) := hα
    have hk1 : (k : ℝ) * (α : ℝ) ≤ t := by
      have := Nat.floor_le (a := t / (α : ℝ)) (by positivity)
      rw [le_div_iff₀ hαpos] at this
      exact this
    have hk2 : t < ((k : ℝ) + 1) * (α : ℝ) := by
      have := Nat.lt_floor_add_one (t / (α : ℝ))
      rw [div_lt_iff₀ hαpos] at this
      exact this
    have hband1 : ((((k : ℝ≥0)) * α : ℝ≥0) : ℝ≥0∞) ≤ apply f x := by
      rw [hteq, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      exact hk1
    have hband2 : apply f x < ((((k : ℝ≥0) + 1) * α : ℝ≥0) : ℝ≥0∞) := by
      rw [hteq, ← ENNReal.ofReal_coe_nnreal]
      refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).2 ?_
      push_cast
      exact hk2
    obtain ⟨r, hr0, hsec⟩ := exists_secant_le hband2
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr0
    have hPm : x ∈ P k m := ⟨⟨hband1, hband2⟩, (secant_mono f hm.le x).trans hsec⟩
    obtain ⟨n, hn⟩ := hv.exists_dist_lt x (ε := 1 / (4 * ((m : ℝ) + 1))) (by positivity)
    refine Set.mem_iUnion.2 ⟨e.symm (k, m, n), ?_⟩
    rw [hAseq]
    simp only [Equiv.apply_symm_apply]
    exact ⟨hPm, by simpa [Metric.mem_ball] using hn⟩
  have hlipA : ∀ i, LipschitzOnWith (c i) f (Aseq i) := by
    intro i
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    obtain ⟨hxP, hxb⟩ := hx
    obtain ⟨hyP, hyb⟩ := hy
    set k : ℕ := (e i).1
    set m : ℕ := (e i).2.1
    have hci : c i = (((k : ℝ≥0)) + 1) * α := by
      refine min_eq_left ?_
      have hk : ((((k : ℝ≥0)) * α : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) := hxP.1.1.trans (hsL x)
      have hk' : ((k : ℝ≥0)) * α ≤ L := by exact_mod_cast hk
      have : ((((k : ℝ≥0)) + 1) * α : ℝ≥0) = (k : ℝ≥0) * α + α := by ring
      rw [this]
      exact add_le_add hk' le_rfl
    have hdist : dist y x < 1 / ((m : ℝ) + 1) := by
      have h1 : dist x (v (e i).2.2) < 1 / (4 * ((m : ℝ) + 1)) := by
        simpa [Metric.mem_ball] using hxb
      have h2 : dist y (v (e i).2.2) < 1 / (4 * ((m : ℝ) + 1)) := by
        simpa [Metric.mem_ball] using hyb
      have h3 : dist y x ≤ dist y (v (e i).2.2) + dist (v (e i).2.2) x :=
        dist_triangle _ _ _
      rw [dist_comm (v (e i).2.2) x] at h3
      have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h4 : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
      have hlt : (2 : ℝ) * (1 / (4 * ((m : ℝ) + 1))) < 1 / ((m : ℝ) + 1) := by
        rw [mul_one_div, div_lt_div_iff₀ h4 hm0]
        nlinarith
      linarith
    have hsecx : secant f (1 / ((m : ℝ) + 1)) x ≤
        ENNReal.ofReal (((((k : ℝ≥0)) + 1) * α : ℝ≥0) : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact hxP.2
    have := dist_le_of_secant_le (NNReal.coe_nonneg _) hsecx hdist
    rw [dist_comm (f x) (f y), dist_comm x y, hci]
    exact this
  refine ⟨D, c, fun i ↦ MeasurableSet.disjointed hmeasA i, disjoint_disjointed Aseq, ?_,
    fun i ↦ min_le_right _ _, fun i ↦ (hlipA i).mono (hDsub i), ?_⟩
  · rw [hDdef, iUnion_disjointed, hcover]
  · intro i x hx
    have hxA : x ∈ Aseq i := hDsub i hx
    have hk : ((((e i).1 : ℝ≥0)) * α : ℝ≥0) ≤ apply f x := by
      exact_mod_cast hxA.1.1.1
    calc ((c i : ℝ≥0) : ℝ≥0∞) ≤ ((((((e i).1 : ℝ≥0)) + 1) * α : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.2 (min_le_left _ _)
      _ = (((((e i).1 : ℝ≥0)) * α : ℝ≥0) : ℝ≥0∞) + (α : ℝ≥0∞) := by
          rw [← ENNReal.coe_add]
          congr 1
          ring
      _ ≤ apply f x + (α : ℝ≥0∞) := add_le_add hk le_rfl

omit [CompleteSpace V] in
/-- The McShane patch: a globally Lipschitz `F` with constant `9 L + 8 α` independent of
`δ`, equal to `f` on a Borel set of co-mass at most `δ`, uniformly within `2 L + 2 α` of `f`, and
whose asymptotic Lipschitz constant on that set is within `2 α` of the local slope of `f`. -/
theorem exists_patch (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {α : ℝ≥0} (hα : 0 < α) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
      (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
      (∀ x, |F x - f x| ≤ 2 * (L : ℝ) + 2 * (α : ℝ)) ∧
      ∀ x ∈ K, AsymptoticLipschitz.apply F x ≤ apply f x + 2 * (α : ℝ≥0∞) := by
  classical
  obtain ⟨D, c, hDmeas, hDdisj, hDcover, hcle, hDlip, hDslope⟩ := exists_partition hf hα
  set δ' : ℝ≥0∞ := min δ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'top : δ' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hhalf0 : 0 < δ' / 2 := ENNReal.div_pos hδ'0.ne' (by norm_num)
  set ε : ℕ → ℝ≥0∞ := fun i ↦ δ' / 2 * ((2 : ℝ≥0∞)⁻¹) ^ (i + 1) with hεdef
  have hε0 : ∀ i, ε i ≠ 0 := by
    intro i
    exact mul_ne_zero hhalf0.ne' (pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num)))
  have hεsum : ∑' i, ε i = δ' / 2 := by
    rw [hεdef, ENNReal.tsum_mul_left]
    have hgeo : ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) = 1 := by
      have hfun : (fun n : ℕ ↦ ((2 : ℝ≥0∞)⁻¹) ^ (n + 1))
          = fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ n := funext fun n ↦ by ring
      rw [hfun, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [hgeo, mul_one]
  have hexK : ∀ i, ∃ Kc ⊆ D i, IsCompact Kc ∧ (ν : Measure V) (D i \ Kc) < ε i := fun i ↦
    (hDmeas i).exists_isCompact_sdiff_lt (measure_ne_top _ _) (hε0 i)
  choose Kc hKcsub hKccomp hKcmeas using hexK
  have hKcdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j) := fun i j hij ↦
    Disjoint.mono (hKcsub i) (hKcsub j) (hDdisj hij)
  have hKclip : ∀ i, LipschitzOnWith (c i) f (Kc i) := fun i ↦ (hDlip i).mono (hKcsub i)
  -- a finite family already carries all but `δ` of the mass
  have hDsum : ∑' i, (ν : Measure V) (D i) = 1 := by
    rw [← measure_iUnion hDdisj hDmeas, hDcover, measure_univ]
  have htail : Tendsto (fun N ↦ ∑' k, (ν : Measure V) (D (k + N))) atTop (𝓝 0) :=
    ENNReal.tendsto_sum_nat_add _ (by rw [hDsum]; exact ENNReal.one_ne_top)
  obtain ⟨N, hN⟩ := ((htail.eventually (gt_mem_nhds hhalf0)).exists)
  obtain ⟨F, hFlip, hFclose, hFeq, hFslope⟩ :=
    exists_patch_of_isCompact hf N Kc c hKccomp hKcdisj hKclip hcle
  refine ⟨F, ⋃ i : Fin N, Kc (i : ℕ), hFlip, ?_, ?_, ?_, hFclose, ?_⟩
  · exact (isCompact_iUnion fun i ↦ hKccomp _).isClosed.measurableSet
  · have hsub : (⋃ i : Fin N, Kc (i : ℕ))ᶜ ⊆ (⋃ i, D i \ Kc i) ∪ (⋃ k, D (k + N)) := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hDcover ▸ Set.mem_univ x : x ∈ ⋃ i, D i)
      by_cases hiN : i < N
      · refine Or.inl (Set.mem_iUnion.2 ⟨i, hi, fun hmem ↦ hx ?_⟩)
        exact Set.mem_iUnion.2 ⟨⟨i, hiN⟩, hmem⟩
      · refine Or.inr (Set.mem_iUnion.2 ⟨i - N, ?_⟩)
        rwa [Nat.sub_add_cancel (by omega)]
    calc (ν : Measure V) (⋃ i : Fin N, Kc (i : ℕ))ᶜ
        ≤ (ν : Measure V) ((⋃ i, D i \ Kc i) ∪ (⋃ k, D (k + N))) := measure_mono hsub
      _ ≤ (ν : Measure V) (⋃ i, D i \ Kc i) + (ν : Measure V) (⋃ k, D (k + N)) :=
          measure_union_le _ _
      _ ≤ (∑' i, (ν : Measure V) (D i \ Kc i)) + ∑' k, (ν : Measure V) (D (k + N)) :=
          add_le_add (measure_iUnion_le _) (measure_iUnion_le _)
      _ ≤ (∑' i, ε i) + δ' / 2 := add_le_add (ENNReal.tsum_le_tsum fun i ↦ (hKcmeas i).le) hN.le
      _ = δ' := by rw [hεsum, ENNReal.add_halves]
      _ ≤ δ := min_le_left _ _
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hFeq i i.2 x hi
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    refine (hFslope i i.2 x hi).trans ?_
    refine (hDslope i x (hKcsub i hi)).trans ?_
    have h2α : (α : ℝ≥0∞) ≤ 2 * (α : ℝ≥0∞) := by
      calc (α : ℝ≥0∞) = 1 * (α : ℝ≥0∞) := (one_mul _).symm
        _ ≤ 2 * (α : ℝ≥0∞) := by gcongr; norm_num
    exact add_le_add le_rfl h2α

end Patch

end LocalSlope

/-! ### Density for globally Lipschitz tests -/

section Density

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- A lower-semicontinuous functional does not exceed the limit inferior along a convergent
sequence. -/
theorem le_liminf_of_lowerSemicontinuous {X : Type*} [TopologicalSpace X] (Q : X → ℝ≥0∞)
    (hQ : LowerSemicontinuous Q) {x : X} {a : ℕ → X} (h : Tendsto a atTop (𝓝 x)) :
    Q x ≤ liminf (fun n ↦ Q (a n)) atTop := by
  refine le_of_forall_lt fun cc hcc ↦ ?_
  obtain ⟨d, hcd, hd⟩ := exists_between hcc
  have heventually := h.eventually (hQ x d hd)
  exact hcd.trans_le (le_liminf_of_le (by isBoundedDefault)
    (heventually.mono fun _ hn ↦ hn.le))

/-- In `ℝ≥0∞` every value is dominated by `1` plus its square. -/
theorem le_one_add_sq (s : ℝ≥0∞) : s ≤ 1 + s ^ 2 := by
  rcases le_total s 1 with h | h
  · exact h.trans le_self_add
  · calc s = s * 1 := (mul_one s).symm
      _ ≤ s * s := mul_le_mul_right h s
      _ = s ^ 2 := (sq s).symm
      _ ≤ 1 + s ^ 2 := le_add_self

/-- The band expansion used by the density estimate. -/
theorem sq_add_two_mul_le (s a : ℝ≥0∞) :
    (s + 2 * a) ^ 2 ≤ (1 + 4 * a) * s ^ 2 + (4 * a + 4 * a ^ 2) := by
  have h1 : (s + 2 * a) ^ 2 = s ^ 2 + 4 * a * s + 4 * a ^ 2 := by ring
  rw [h1]
  calc s ^ 2 + 4 * a * s + 4 * a ^ 2 ≤ s ^ 2 + 4 * a * (1 + s ^ 2) + 4 * a ^ 2 := by
        gcongr
        exact le_one_add_sq s
    _ = (1 + 4 * a) * s ^ 2 + (4 * a + 4 * a ^ 2) := by ring

namespace SmoothGradient

/-- Density for a globally Lipschitz test: the smooth-gradient relaxation of `g` is at most
its raw local-slope energy.  The recovery is by McShane patches with `α = δ = 1 / (n + 1)`. -/
theorem relaxation_le_localSlope_of_lipschitzWith (ν : ProbabilityMeasure V) {g : V → ℝ}
    {L : ℝ≥0} (hg : LipschitzWith L g) (hmem : MemLp g 2 (ν : Measure V)) :
    relaxation ν (hmem.toLp g) ≤ LocalSlope.energy ν g := by
  classical
  set E : ℝ≥0∞ := LocalSlope.energy ν g with hE
  rcases eq_or_ne E ⊤ with hEtop | hEtop
  · rw [hEtop]; exact le_top
  set a : ℕ → ℝ≥0 := fun n ↦ ((n : ℝ≥0) + 1)⁻¹ with hadef
  have ha0 : ∀ n, 0 < a n := fun n ↦ by
    rw [hadef]
    exact inv_pos.2 (by positivity)
  have ha1 : ∀ n, a n ≤ 1 := by
    intro n
    rw [hadef]
    simp only
    rw [inv_le_one₀ (by positivity)]
    simp
  have hatend : Tendsto (fun n : ℕ ↦ ((a n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from rfl]
    refine ENNReal.tendsto_coe.2 ?_
    rw [← NNReal.tendsto_coe]
    have heq : (fun n : ℕ ↦ ((a n : ℝ≥0) : ℝ)) = fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ := by
      funext n
      rw [hadef]
      push_cast
      ring
    rw [heq]
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  set M : ℝ≥0 := 9 * L + 8 with hM
  have hpatch :
    ∀ n : ℕ,
      ∃ (F : V → ℝ) (K : Set V),
        LipschitzWith (9 * L + 8 * a n) F ∧
          MeasurableSet K ∧
            (ν : Measure V) Kᶜ ≤ ((a n : ℝ≥0) : ℝ≥0∞) ∧
              (∀ x ∈ K, F x = g x) ∧
                (∀ x, |F x - g x| ≤ 2 * (L : ℝ) + 2 * ((a n : ℝ≥0) : ℝ)) ∧
                  ∀ x ∈ K,
                    AsymptoticLipschitz.apply F x ≤
                      LocalSlope.apply g x + 2 * ((a n : ℝ≥0) : ℝ≥0∞) :=
    fun n ↦ LocalSlope.exists_patch ν hg (ha0 n) (by exact_mod_cast ha0 n)
  choose F Kset hFlip hKmeas hKmass hFeq hFclose hFslope using
    hpatch
  -- the patches are `L²(ν)` functions
  have hFmem : ∀ n, MemLp (F n) 2 (ν : Measure V) := by
    intro n
    have hdiff : MemLp (fun x ↦ F n x - g x) 2 (ν : Measure V) := by
      refine MemLp.of_bound ?_ (2 * (L : ℝ) + 2 * ((a n : ℝ≥0) : ℝ)) (ae_of_all _ fun x ↦ ?_)
      · exact (((hFlip n).continuous).sub hg.continuous).aestronglyMeasurable
      · simpa [Real.norm_eq_abs] using hFclose n x
    have hrw : F n = fun x ↦ (F n x - g x) + g x := by funext x; ring
    rw [hrw]
    exact
      hdiff.add
        hmem
  -- the energy bound at each patch
  have hMbound : ∀ n, 9 * L + 8 * a n ≤ M := by
    intro n
    rw [hM]
    have : 8 * a n ≤ 8 := by
      calc
        8 * a n ≤ 8 * 1 := mul_le_mul_right (ha1 n) 8
        _ = 8 := mul_one 8
    exact add_le_add le_rfl this
  have hmeas_s : Measurable (LocalSlope.apply g) := LocalSlope.measurable_apply hg.continuous
  have henergy :
    ∀ n,
      AsymptoticLipschitz.energy ν (F n) ≤
        (1 + 4 * ((a n : ℝ≥0) : ℝ≥0∞)) * E +
            (4 * ((a n : ℝ≥0) : ℝ≥0∞) + 4 * ((a n : ℝ≥0) : ℝ≥0∞) ^ 2) +
          (M : ℝ≥0∞) ^ 2 * ((a n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    set an : ℝ≥0∞ := ((a n : ℝ≥0) : ℝ≥0∞) with handef
    have hpt :
      ∀ x,
        AsymptoticLipschitz.apply (F n) x ^ 2 ≤
          ((1 + 4 * an) * LocalSlope.apply g x ^ 2 + (4 * an + 4 * an ^ 2)) +
            (Kset n)ᶜ.indicator (fun _ ↦ (M : ℝ≥0∞) ^ 2) x := by
      intro x
      by_cases hx : x ∈ Kset n
      · have h1 : AsymptoticLipschitz.apply (F n) x ≤ LocalSlope.apply g x + 2 * an :=
          hFslope n x hx
        have h2 : AsymptoticLipschitz.apply (F n) x ^ 2 ≤ (LocalSlope.apply g x + 2 * an) ^ 2 :=
          pow_le_pow_left' h1 2
        refine h2.trans ?_
        exact le_trans (sq_add_two_mul_le _ _) le_self_add
      · have h1 : AsymptoticLipschitz.apply (F n) x ≤ (M : ℝ≥0∞) := by
          refine (AsymptoticLipschitz.apply_le_of_lipschitzWith (hFlip n) x).trans ?_
          exact_mod_cast hMbound n
        have h2 : AsymptoticLipschitz.apply (F n) x ^ 2 ≤ (M : ℝ≥0∞) ^ 2 :=
          pow_le_pow_left' h1 2
        have h3 : (Kset n)ᶜ.indicator (fun _ ↦ (M : ℝ≥0∞) ^ 2) x = (M : ℝ≥0∞) ^ 2 :=
          Set.indicator_of_mem hx _
        rw [h3]
        exact h2.trans le_add_self
    calc
      AsymptoticLipschitz.energy ν (F n) ≤
          ∫⁻ x,
            (((1 + 4 * an) * LocalSlope.apply g x ^ 2 + (4 * an + 4 * an ^ 2)) +
              (Kset n)ᶜ.indicator (fun _ ↦ (M : ℝ≥0∞) ^ 2) x) ∂(ν : Measure V) :=
        lintegral_mono hpt
      _ =
          (∫⁻ x,
              ((1 + 4 * an) * LocalSlope.apply g x ^ 2 +
                (4 * an + 4 * an ^ 2)) ∂(ν : Measure V)) +
            (M : ℝ≥0∞) ^ 2 * (ν : Measure V) (Kset n)ᶜ := by
        rw [lintegral_add_right _ ((measurable_const.indicator (hKmeas n).compl)),
          lintegral_indicator_const (hKmeas n).compl]
      _ =
          ((1 + 4 * an) * E + (4 * an + 4 * an ^ 2)) +
            (M : ℝ≥0∞) ^ 2 * (ν : Measure V) (Kset n)ᶜ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (hmeas_s.pow_const 2),
          lintegral_const, measure_univ, mul_one]
        rfl
      _ ≤ (1 + 4 * an) * E + (4 * an + 4 * an ^ 2) + (M : ℝ≥0∞) ^ 2 * an := by
        exact
          add_le_add le_rfl
            (mul_le_mul_right (hKmass n) _)
  -- convergence of the patches in `L²(ν)`
  have hconv : Tendsto (fun n ↦ (hFmem n).toLp (F n)) atTop (𝓝 (hmem.toLp g)) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ F n) hFmem g hmem).mpr ?_
    have hle :
      ∀ n,
        eLpNorm (F n - g) 2 (ν : Measure V) ≤
          ‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2) := by
      intro n
      have hmono :
        eLpNorm (F n - g) 2 (ν : Measure V) ≤
          eLpNorm ((Kset n)ᶜ.indicator fun _ ↦ (2 * (L : ℝ) + 2 : ℝ)) 2 (ν : Measure V) := by
        refine eLpNorm_mono ((hFmem n).aestronglyMeasurable.sub hmem.aestronglyMeasurable)
          fun x ↦ ?_
        by_cases hx : x ∈ Kset n
        · simp [hFeq n x hx]
        · rw [Set.indicator_of_mem hx (fun _ ↦ (2 * (L : ℝ) + 2 : ℝ))]
          have h1 := hFclose n x
          have h2 : 2 * ((a n : ℝ≥0) : ℝ) ≤ 2 := by
            have : ((a n : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast ha1 n
            linarith
          have : |F n x - g x| ≤ 2 * (L : ℝ) + 2 := by linarith
          simpa [Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) + 2)] using this
      refine hmono.trans ?_
      rw [eLpNorm_indicator_const (hKmeas n).compl.nullMeasurableSet (by norm_num) (by norm_num)]
      have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
      rw [h2]
      exact mul_le_mul_right (ENNReal.rpow_le_rpow (hKmass n) (by norm_num)) _
    have hlim :
      Tendsto (fun n ↦ ‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun n ↦ ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
        have := (ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0 |>.comp hatend
        simpa [Function.comp_def,
          ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this
      have h2 :
        Tendsto (fun n ↦ ‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * ((a n : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) atTop
          (𝓝 (‖(2 * (L : ℝ) + 2 : ℝ)‖ₑ * 0)) :=
        ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
      simpa using h2
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
        hle
  -- lower semicontinuity finishes
  have hlsc :=
    le_liminf_of_lowerSemicontinuous (fun f ↦ relaxation ν f)
      (preEnergy ν).lowerSemicontinuous_sequentialRelaxation hconv
  refine hlsc.trans ?_
  set C : ℝ≥0∞ := 4 * E + 8 + (M : ℝ≥0∞) ^ 2 with hC
  have hCtop : C ≠ ⊤ := by
    rw [hC]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, by norm_num⟩, ?_⟩
    · exact ENNReal.mul_ne_top (by norm_num) hEtop
    · exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hstep : ∀ n, relaxation ν ((hFmem n).toLp (F n)) ≤ E + ((a n : ℝ≥0) : ℝ≥0∞) * C := by
    intro n
    set an : ℝ≥0∞ := ((a n : ℝ≥0) : ℝ≥0∞) with handef
    have han1 : an ≤ 1 := by rw [handef]; exact_mod_cast ha1 n
    refine
      le_trans (relaxation_le_asymptoticLipschitz_of_lipschitzWith ν (hFlip n) (hFmem n)) ?_
    refine (henergy n).trans ?_
    have hsq : an ^ 2 ≤ an := by
      calc
        an ^ 2 = an * an := sq an
        _ ≤ an * 1 := mul_le_mul_right han1 an
        _ = an := mul_one an
    calc
      (1 + 4 * an) * E + (4 * an + 4 * an ^ 2) + (M : ℝ≥0∞) ^ 2 * an =
          E + 4 * an * E + (4 * an + 4 * an ^ 2) + (M : ℝ≥0∞) ^ 2 * an := by
        ring
      _ ≤ E + 4 * an * E + (4 * an + 4 * an) + (M : ℝ≥0∞) ^ 2 * an := by gcongr
      _ = E + an * (4 * E + 8 + (M : ℝ≥0∞) ^ 2) := by ring
  refine le_trans (liminf_le_liminf (Eventually.of_forall hstep)) ?_
  have htend : Tendsto (fun n ↦ E + ((a n : ℝ≥0) : ℝ≥0∞) * C) atTop (𝓝 E) := by
    have h1 : Tendsto (fun n ↦ ((a n : ℝ≥0) : ℝ≥0∞) * C) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const hatend (Or.inr hCtop)
      simpa using this
    simpa using tendsto_const_nhds.add h1
  exact le_of_eq htend.liminf_eq

end SmoothGradient

end Density

/-! ### Density for every admissible test and the reverse inequality -/

section General

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- Young's inequality with a parameter, in the real line. -/
theorem real_sq_add_le {t a b : ℝ} (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + t⁻¹) * b ^ 2 := by
  have hX : 0 ≤ t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b := by
    have h2 : t * (t * a ^ 2 + t⁻¹ * b ^ 2 - 2 * a * b) = (t * a - b) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (t * a - b), ht]
  nlinarith [hX]

/-- Young's inequality with a parameter, in `ℝ≥0∞`, including the infinite values. -/
theorem sq_add_le_mul_sq_add {θ : ℝ≥0} (hθ : 0 < θ) (x y : ℝ≥0∞) :
    (x + y) ^ 2 ≤ (1 + (θ : ℝ≥0∞)) * x ^ 2 + (1 + (θ : ℝ≥0∞)⁻¹) * y ^ 2 := by
  have hθinv : ((θ : ℝ≥0∞))⁻¹ = ((θ⁻¹ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_inv hθ.ne').symm
  rw [hθinv]
  rcases eq_or_ne x ⊤ with hx | hx
  · have h1 : (1 + (θ : ℝ≥0∞)) * x ^ 2 = ⊤ := by
      rw [hx, ENNReal.top_pow (by norm_num)]
      exact ENNReal.mul_top (by simp)
    rw [h1, top_add]
    exact le_top
  rcases eq_or_ne y ⊤ with hy | hy
  · have h1 : (1 + ((θ⁻¹ : ℝ≥0) : ℝ≥0∞)) * y ^ 2 = ⊤ := by
      rw [hy, ENNReal.top_pow (by norm_num)]
      exact ENNReal.mul_top (by simp)
    rw [h1, add_top]
    exact le_top
  obtain ⟨a, rfl⟩ : ∃ a : ℝ≥0, x = (a : ℝ≥0∞) := ⟨x.toNNReal, (ENNReal.coe_toNNReal hx).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ≥0, y = (b : ℝ≥0∞) := ⟨y.toNNReal, (ENNReal.coe_toNNReal hy).symm⟩
  have hnn : (a + b) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + θ⁻¹) * b ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact real_sq_add_le (by exact_mod_cast hθ)
  calc ((a : ℝ≥0∞) + (b : ℝ≥0∞)) ^ 2 = ((((a + b) ^ 2 : ℝ≥0)) : ℝ≥0∞) := by
        rw [ENNReal.coe_pow, ENNReal.coe_add]
    _ ≤ ((((1 + θ) * a ^ 2 + (1 + θ⁻¹) * b ^ 2 : ℝ≥0)) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hnn
    _ = (1 + (θ : ℝ≥0∞)) * (a : ℝ≥0∞) ^ 2 + (1 + ((θ⁻¹ : ℝ≥0) : ℝ≥0∞)) * (b : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_add,
          ENNReal.coe_one, ENNReal.coe_pow, ENNReal.coe_pow]

namespace SmoothGradient

/-- Density for every admissible local-slope test: cutting off by the smooth bump
`scaled (n + 1)` produces globally Lipschitz tests converging in `L²(ν)` whose energies converge,
after Young's inequality, to the local-slope energy of the test. -/
theorem relaxation_le_localSlope_of_admissible (ν : ProbabilityMeasure V) {g : V → ℝ}
    (hg : LocalSlope.Admissible ν g) :
    relaxation ν (hg.memLp_two.toLp g) ≤ LocalSlope.energy ν g := by
  classical
  set E : ℝ≥0∞ := LocalSlope.energy ν g with hE
  have hEtop : E ≠ ⊤ := hg.finite_energy
  have hgcont : Continuous g := hg.locallyLipschitz.continuous
  have hmeas_s : Measurable (LocalSlope.apply g) := LocalSlope.measurable_apply hgcont
  -- the `L²` mass of the test
  set G : ℝ≥0∞ := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂(ν : Measure V) with hG
  have hGtop : G ≠ ⊤ := by
    have hint : Integrable (fun x ↦ ‖g x‖ ^ 2) (ν : Measure V) :=
      (memLp_two_iff_integrable_sq_norm hg.memLp_two.aestronglyMeasurable).mp hg.memLp_two
    have heq : G = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂(ν : Measure V)) := by
      rw [hG, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x ↦ sq_nonneg _)]
      exact lintegral_congr fun x ↦ by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [heq]
    exact ENNReal.ofReal_ne_top
  obtain ⟨Mb, hMb0, hMb⟩ := exists_bound_fderiv_bump (E := V)
  set N : ℕ → ℝ≥0 := fun n ↦ ((((n : ℝ) + 1)⁻¹ * Mb).toNNReal) with hNdef
  have hNtend : Tendsto (fun n : ℕ ↦ ((N n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from rfl]
    refine ENNReal.tendsto_coe.2 ?_
    rw [← NNReal.tendsto_coe]
    have heq : (fun n : ℕ ↦ ((N n : ℝ≥0) : ℝ)) = fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹ * Mb) := by
      funext n
      rw [hNdef]
      exact Real.coe_toNNReal _ (by positivity)
    rw [heq]
    have : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ * Mb) atTop (𝓝 (0 * Mb)) := by
      refine Tendsto.mul_const Mb ?_
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  -- the cutoffs
  set q : ℕ → V → ℝ := fun n x ↦ g x * scaled ((n : ℝ) + 1) x with hqdef
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  have hscaled1 : ∀ (n : ℕ) (x : V), |scaled ((n : ℝ) + 1) x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (scaled_nonneg _ x)]
    exact scaled_le_one _ x
  have hscaledlip : ∀ n : ℕ, LipschitzWith (N n) (scaled (E := V) ((n : ℝ) + 1)) := fun n ↦
    lipschitzWith_scaled (hRpos n) hMb0 hMb
  have hqloc : ∀ n, LocallyLipschitz (q n) := fun n ↦
    locallyLipschitz_mul hg.locallyLipschitz (hscaledlip n) (hscaled1 n)
  have hqzero : ∀ (n : ℕ) (x : V), 2 * ((n : ℝ) + 1) ≤ ‖x‖ → q n x = 0 := by
    intro n x hx
    rw [hqdef]
    simp only
    rw [scaled_eq_zero (hRpos n) hx, mul_zero]
  have hKqex : ∀ n : ℕ, ∃ K : ℝ≥0, LipschitzWith K (q n) := fun n ↦
    exists_lipschitzWith_of_eq_zero_outside_ball (hqloc n) (hqzero n)
  choose Kq hKq using hKqex
  have hqabs : ∀ (n : ℕ) (x : V), |q n x| ≤ |g x| := by
    intro n x
    rw [hqdef]
    simp only
    rw [abs_mul]
    calc |g x| * |scaled ((n : ℝ) + 1) x| ≤ |g x| * 1 :=
          mul_le_mul_of_nonneg_left (hscaled1 n x) (abs_nonneg _)
      _ = |g x| := mul_one _
  have hqmem : ∀ n, MemLp (q n) 2 (ν : Measure V) := by
    intro n
    refine hg.memLp_two.mono ((hqloc n).continuous.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    simpa [Real.norm_eq_abs] using hqabs n x
  have hqconv : Tendsto (fun n ↦ (hqmem n).toLp (q n)) atTop (𝓝 (hg.memLp_two.toLp g)) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ q n) hqmem g hg.memLp_two).mpr ?_
    refine tendsto_eLpNorm_zero_of_dominated (ν : Measure V) (p := 2) (by norm_num) (by norm_num)
      (F := fun n ↦ q n - g) (bound := fun x ↦ ‖g x‖) (fun n ↦ ?_) hg.memLp_two.norm
      (fun n ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · exact ((hqloc n).continuous.sub hgcont).aestronglyMeasurable
    · simp only [Pi.sub_apply]
      have h2 : q n x - g x = g x * (scaled ((n : ℝ) + 1) x - 1) := by
        rw [hqdef]; simp only; ring
      rw [h2, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      have h3 : |scaled ((n : ℝ) + 1) x - 1| ≤ 1 := by
        rw [abs_le]
        constructor
        · have := scaled_le_one ((n : ℝ) + 1) x
          have := scaled_nonneg ((n : ℝ) + 1) x
          linarith
        · have := scaled_nonneg ((n : ℝ) + 1) x
          have := scaled_le_one ((n : ℝ) + 1) x
          linarith
      calc |g x| * |scaled ((n : ℝ) + 1) x - 1| ≤ |g x| * 1 :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |g x| := mul_one _
    · have hev : ∀ᶠ n : ℕ in atTop, (q n - g) x = 0 := by
        obtain ⟨n₀, hn₀⟩ := exists_nat_ge ‖x‖
        filter_upwards [eventually_ge_atTop n₀] with n hn
        have hle : ‖x‖ ≤ (n : ℝ) + 1 := by
          have : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        simp [hqdef, scaled_eq_one (hRpos n) hle]
      exact Tendsto.congr' (by filter_upwards [hev] with n hn; rw [hn]) tendsto_const_nhds
  -- the parametrized energy bound
  have key : ∀ θ : ℝ≥0, 0 < θ →
      relaxation ν (hg.memLp_two.toLp g) ≤ (1 + (θ : ℝ≥0∞)) * E := by
    intro θ hθ
    have hθtop : (1 + (θ : ℝ≥0∞)⁻¹) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, by
        rw [← ENNReal.coe_inv hθ.ne']
        exact ENNReal.coe_ne_top⟩
    have hbound : ∀ n, relaxation ν ((hqmem n).toLp (q n)) ≤
        (1 + (θ : ℝ≥0∞)) * E + (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G) := by
      intro n
      refine le_trans (relaxation_le_localSlope_of_lipschitzWith ν (hKq n) (hqmem n)) ?_
      have hpt : ∀ x, LocalSlope.apply (q n) x ^ 2 ≤
          (1 + (θ : ℝ≥0∞)) * LocalSlope.apply g x ^ 2 +
            (1 + (θ : ℝ≥0∞)⁻¹) * (‖g x‖ₑ ^ 2 * ((N n : ℝ≥0) : ℝ≥0∞) ^ 2) := by
        intro x
        have h1 : LocalSlope.apply (q n) x ≤
            LocalSlope.apply g x + ENNReal.ofReal |g x| * ((N n : ℝ≥0) : ℝ≥0∞) :=
          LocalSlope.apply_mul_le g _ (hscaledlip n) (hscaled1 n) x
        refine (pow_le_pow_left' h1 2).trans ?_
        refine (sq_add_le_mul_sq_add hθ _ _).trans ?_
        refine add_le_add le_rfl (le_of_eq ?_)
        have hgx : ENNReal.ofReal |g x| = ‖g x‖ₑ := by
          rw [← Real.norm_eq_abs, ofReal_norm]
        rw [hgx, mul_pow]
      calc LocalSlope.energy ν (q n) ≤ ∫⁻ x, ((1 + (θ : ℝ≥0∞)) * LocalSlope.apply g x ^ 2 +
              (1 + (θ : ℝ≥0∞)⁻¹) * (‖g x‖ₑ ^ 2 * ((N n : ℝ≥0) : ℝ≥0∞) ^ 2)) ∂(ν : Measure V) :=
            lintegral_mono hpt
        _ = (1 + (θ : ℝ≥0∞)) * E + (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G) := by
            rw [lintegral_add_left ((hmeas_s.pow_const 2).const_mul _),
              lintegral_const_mul _ (hmeas_s.pow_const 2),
              lintegral_const_mul _ (((hgcont.measurable.enorm).pow_const 2).mul_const _)]
            rw [lintegral_mul_const _ (hgcont.measurable.enorm.pow_const 2)]
            rw [hG, hE]
            simp only [LocalSlope.energy]
            ring
    have herr : Tendsto (fun n ↦ (1 + (θ : ℝ≥0∞)) * E +
        (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G)) atTop
        (𝓝 ((1 + (θ : ℝ≥0∞)) * E)) := by
      have h1 : Tendsto (fun n ↦ ((N n : ℝ≥0) : ℝ≥0∞) ^ 2) atTop (𝓝 0) := by
        have := (ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞) |>.comp hNtend
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun n ↦ ((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const h1 (Or.inr hGtop)
        simpa using this
      have h3 : Tendsto (fun n ↦ (1 + (θ : ℝ≥0∞)⁻¹) * (((N n : ℝ≥0) : ℝ≥0∞) ^ 2 * G)) atTop
          (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul h2 (Or.inr hθtop)
        simpa using this
      simpa using tendsto_const_nhds.add h3
    have hlsc := le_liminf_of_lowerSemicontinuous (fun f ↦ relaxation ν f)
      (preEnergy ν).lowerSemicontinuous_sequentialRelaxation hqconv
    refine hlsc.trans ?_
    refine le_trans (liminf_le_liminf (Eventually.of_forall hbound)) ?_
    exact le_of_eq herr.liminf_eq
  -- let the parameter tend to zero
  set θ : ℕ → ℝ≥0 := fun k ↦ ((k : ℝ≥0) + 1)⁻¹ with hθdef
  have hθ0 : ∀ k, 0 < θ k := fun k ↦ by
    rw [hθdef]
    exact inv_pos.2 (by positivity)
  have hθtend : Tendsto (fun k : ℕ ↦ ((θ k : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from rfl]
    refine ENNReal.tendsto_coe.2 ?_
    rw [← NNReal.tendsto_coe]
    have heq : (fun k : ℕ ↦ ((θ k : ℝ≥0) : ℝ)) = fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹ := by
      funext k
      rw [hθdef]
      push_cast
      ring
    rw [heq]
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun k ↦ (1 + ((θ k : ℝ≥0) : ℝ≥0∞)) * E) atTop (𝓝 E) := by
    have h1 : Tendsto (fun k ↦ (1 + ((θ k : ℝ≥0) : ℝ≥0∞))) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hθtend
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hEtop)
    simpa using this
  exact ge_of_tendsto hlim (Eventually.of_forall fun k ↦ key (θ k) (hθ0 k))

/-- The reverse inequality between the two relaxations, for every law: smooth tests are
dense in the local-slope energy, so the smooth-gradient relaxation does not exceed the
local-slope relaxation. -/
theorem relaxation_le_localSlope (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f ≤ LocalSlope.relaxation ν f :=
  LocalSlope.le_relaxation_of_lowerSemicontinuous ν (relaxation ν)
    (preEnergy ν).lowerSemicontinuous_sequentialRelaxation
    (fun _g hgadm ↦ relaxation_le_localSlope_of_admissible ν hgadm) f

end SmoothGradient

end General

end FunctionalInequalities.Energy
