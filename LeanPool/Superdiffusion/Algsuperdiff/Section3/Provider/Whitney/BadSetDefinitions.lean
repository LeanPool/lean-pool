/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.MinimalScaleSeparation

/-!
# BadSetDefinitions

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `d.whitney.bad-set.definitions`: the Whitney partition and its bad set

This module defines local implementations of the definitions in ABK26's
`sss.whitney.partition`:

* the scale separation sequence `h_n = ⌈b(1-b)⁻¹ n⌉ + h_hat_sep + k₀` (`e.hn.def`)
  and the one-layer gap `h_{n+1} - h_n ≤ 1` (`e.hn.gap`, (label-line
  convention;));
* the recursive Whitney partition `𝒲(□_m)` and its layers `𝒲(□_m, n)`
  (`e.W.n.def`);
* the bad family `ℐ` and `ℐ_n` (`e.bad.cubes.in.partition`);
* the neighborhood `𝒩(𝒥)` (`e.neighborhood.def`);
* connected components of `ℐ`.

## The recursion, unrolled

The manuscript's construction is: divide `□_m` into its `3^d` children; a child
that touches `∂□_m` is carried to the next layer and re-divided; a child that
does *not* touch `∂□_m` is a layer-`n` cube and is subdivided `h_n` further
generations.  The cubes so produced are the elements of `𝒲(□_m)`.

A cube reaches layer `n` exactly when every one of its ancestors of depth
`1, …, n-1` touches `∂□_m`, and by `touchesBoundary_of_mem_descendantsAtDepth`
that is the same as its depth-`(n-1)` ancestor touching `∂□_m`.  So the layer is
the closed-form family

```
𝒲(□_m, n) = ⋃ { descendantsAtDepth C (h n) :
                  C a non-touching child of a touching depth-(n-1) descendant } ,
```

which is the definition taken here (`whitneyLayer`).  `𝒲(□_m)` is the union of
all layers, without any fuel truncation.  `whitneyLayer_eq_filter_scale` proves
that this agrees with the manuscript's own `e.W.n.def`, which *defines*
`𝒲(□_m, n)` as the cubes of `𝒲(□_m)` of size `3^{m-n-h_n}`.

## Carriers

Cubes are `Homogenization.TriadicCube d`; `□_m` is `originCube d m`; triadic
subdivision is `childCubes` / `descendantsAtDepth`.  "`□` touches `∂□_m`" is
the extreme-index predicate `TouchesBoundary`: a depth-`t` descendant of `□_m`
is the box `(index ± ½)·3^{m-t}`, and `□_m` is `(0 ± ½)·3^m`, so the closed
cube meets `∂□_m` in the coordinate `i` exactly when `index i = ±(3^t - 1)/2 =
±E_t`.  The bad event `𝓑(□)` is the proved `BadEvents.bad`.

## Reading notes (recorded)

* `𝒩(𝒥)` is defined through `∃ □' ∈ 𝒥, dist(□,□') = 0` rather than through
  `dist(□, ⋃𝒥) = 0`.  The two agree whenever `𝒥` is finite, and every
  manuscript use of `𝒩` is at a bad cluster; the pointwise form is the one the
  proofs consume.  `dist(□,□') = 0` for the *closed* cubes is `CubeTouch`,
  characterized coordinatewise by `cubeTouch_iff`.

## References

* ABK26, `sss.whitney.partition`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The scale separation sequence `e.hn.def` -/

/-- **ABK26 `e.hn.def`**: the scale separation sequence `h_n = ⌈b (1-b)⁻¹ n⌉ +
h_hat_sep + k₀`, as a function of the *value* `hs` of the minimal scale separation
`h_hat_sep` and of the parameter `k₀`. -/
def whitneyScaleSeq (b : ℝ) (hs k₀ n : ℕ) : ℕ :=
  ⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊ + hs + k₀

/-- `h_n ≥ h_hat_sep + k₀`: the bottom of the sequence, used to check the
`h ≥ h_hat_sep` hypothesis of the deterministic percolation bounds. -/
theorem add_le_whitneyScaleSeq (b : ℝ) (hs k₀ n : ℕ) :
    hs + k₀ ≤ whitneyScaleSeq b hs k₀ n := by
  unfold whitneyScaleSeq
  omega

theorem hsep_le_whitneyScaleSeq (b : ℝ) (hs k₀ n : ℕ) :
    hs ≤ whitneyScaleSeq b hs k₀ n :=
  le_trans (Nat.le_add_right hs k₀) (add_le_whitneyScaleSeq b hs k₀ n)

/-- The slope of `e.hn.def` is at most `1` when `b ≤ 1/8` (the true bound is
`1/7`; `≤ 1` is what the gap proof consumes). -/
theorem whitneyScaleSeq_slope_le_one {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 8) :
    b * (1 - b)⁻¹ ≤ 1 := by
  have hb1 : (0 : ℝ) < 1 - b := by linarith
  rw [mul_inv_le_iff₀ hb1]
  linarith

/-- **ABK26 `e.hn.gap`**: for `b ≤ 1/8` consecutive scale separations differ by at
most one, so the Whitney scales grow by at most one layer at a time. -/
theorem whitneyScaleSeq_succ_le {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hs k₀ n : ℕ) :
    whitneyScaleSeq b hs k₀ (n + 1) ≤ whitneyScaleSeq b hs k₀ n + 1 := by
  have hslope := whitneyScaleSeq_slope_le_one hb0 hb
  have hb1 : (0 : ℝ) < 1 - b := by linarith
  have hnn : (0 : ℝ) ≤ b * (1 - b)⁻¹ * (n : ℝ) :=
    mul_nonneg (mul_nonneg hb0.le (inv_pos.2 hb1).le) (Nat.cast_nonneg n)
  have hceil : ⌈b * (1 - b)⁻¹ * ((n + 1 : ℕ) : ℝ)⌉₊ ≤
      ⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊ + 1 := by
    refine Nat.ceil_le.2 ?_
    have hle : b * (1 - b)⁻¹ * (n : ℝ) ≤ (⌈b * (1 - b)⁻¹ * (n : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    push_cast
    nlinarith
  unfold whitneyScaleSeq
  omega

theorem whitneyScaleSeq_mono {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hs k₀ : ℕ) :
    Monotone (whitneyScaleSeq b hs k₀) := by
  intro n n' hnn'
  have hb : (0 : ℝ) < 1 - b := by linarith
  have hmul : b * (1 - b)⁻¹ * (n : ℝ) ≤ b * (1 - b)⁻¹ * (n' : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hnn')
      (mul_nonneg hb0 (inv_pos.2 hb).le)
  have := Nat.ceil_le_ceil hmul
  unfold whitneyScaleSeq
  omega

/-- The real lower bound `h_n ≥ b(1-b)⁻¹ n + h_hat_sep + k₀` used in the cluster
diameter estimate. -/
theorem le_whitneyScaleSeq_cast (b : ℝ) (hs k₀ n : ℕ) :
    b * (1 - b)⁻¹ * (n : ℝ) + (hs : ℝ) + (k₀ : ℝ) ≤
      (whitneyScaleSeq b hs k₀ n : ℝ) := by
  have h := Nat.le_ceil (b * (1 - b)⁻¹ * (n : ℝ))
  unfold whitneyScaleSeq
  push_cast
  linarith

/-- The Whitney depth sequence anchored at the sample's separation height. -/
def whitneyScale (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ : ℕ)
    (omega : CutoffSample d) : ℕ → ℕ :=
  whitneyScaleSeq b (Percolation.hsep M m E b omega) k₀

theorem hsep_le_whitneyScale (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ : ℕ)
    (omega : CutoffSample d) (n : ℕ) :
    Percolation.hsep M m E b omega ≤ whitneyScale M m E b k₀ omega n :=
  hsep_le_whitneyScaleSeq _ _ _ _

/-! ## Boundary-index arithmetic -/

/-- `E_j = (3^j - 1)/2`, the extreme index coordinate of a depth-`j` triadic
descendant of `□_m`. -/
def extremeIdx : ℕ → ℤ
  | 0 => 0
  | j + 1 => 3 * extremeIdx j + 1

theorem two_mul_extremeIdx_add_one (j : ℕ) : 2 * extremeIdx j + 1 = (3 : ℤ) ^ j := by
  induction j with
  | zero => simp [extremeIdx]
  | succ j ih => rw [extremeIdx, pow_succ]; omega

theorem extremeIdx_nonneg (j : ℕ) : 0 ≤ extremeIdx j := by
  induction j with
  | zero => simp [extremeIdx]
  | succ j ih => rw [extremeIdx]; omega

/-- The extreme index coordinate of a scale-`s` triadic descendant of `□_m`. -/
def rootExtreme (m s : ℤ) : ℤ := (3 ^ (m - s).toNat - 1) / 2

theorem rootExtreme_sub_natCast (m : ℤ) (j : ℕ) :
    rootExtreme m (m - (j : ℤ)) = extremeIdx j := by
  have hj : (m - (m - (j : ℤ))).toNat = j := by omega
  rw [rootExtreme, hj]
  have h := two_mul_extremeIdx_add_one j
  omega

/-- **`□` touches `∂□_m`**: some index coordinate of `□` is extreme.  For a
depth-`t` descendant of `□_m`, whose closed realization is the box
`(index ± ½)·3^{m-t}` inside `□_m = (0 ± ½)·3^m`, this is exactly the condition
that the closed cube meets the boundary `∂□_m`. -/
def TouchesBoundary (m : ℤ) (R : TriadicCube d) : Prop :=
  ∃ i : Fin d, R.index i = rootExtreme m R.scale ∨ R.index i = -rootExtreme m R.scale

instance instDecidablePredTouchesBoundary (m : ℤ) :
    DecidablePred (TouchesBoundary (d := d) m) := fun R => by
  unfold TouchesBoundary; infer_instance

/-! ## Triadic subdivision -/

-- The subdivision basics (`descendantsAtDepth_zero`/`_one`,
-- `mem_descendantsAtDepth_succ_iff`, `mem_childCubes_iff`,
-- `child_scale_of_mem_childCubes`, `scale_eq_sub_of_mem_descendantsAtDepth`,
-- consumers opening `Homogenization` see no ambiguous names.

/-- The index of a depth-`s` descendant stays within `E_s` of the rescaled index
of its ancestor. -/
theorem abs_index_sub_le_of_mem_descendantsAtDepth {C : TriadicCube d} :
    ∀ {s : ℕ} {Q : TriadicCube d}, Q ∈ descendantsAtDepth C s →
      ∀ j, |Q.index j - 3 ^ s * C.index j| ≤ extremeIdx s := by
  intro s
  induction s with
  | zero =>
      intro Q hQ j
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hQ
      subst hQ
      simp [extremeIdx]
  | succ s ih =>
      intro Q hQ j
      obtain ⟨S, hS, hQS⟩ := mem_descendantsAtDepth_succ_iff.mp hQ
      obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hQS
      have hprev := abs_le.mp (ih hS j)
      have hd1 : ((digits j : ℕ) : ℤ) < 3 := by exact_mod_cast (digits j).is_lt
      have hd2 : (0 : ℤ) ≤ ((digits j : ℕ) : ℤ) := Int.natCast_nonneg _
      have hE : extremeIdx (s + 1) = 3 * extremeIdx s + 1 := rfl
      have hp : (3 : ℤ) ^ (s + 1) = 3 * 3 ^ s := by ring
      change |3 * S.index j + ((digits j : ℕ) : ℤ) - 1 - 3 ^ (s + 1) * C.index j| ≤
        extremeIdx (s + 1)
      rw [hE, hp, abs_le]
      constructor <;> nlinarith [hprev.1, hprev.2]

theorem abs_index_le_extremeIdx {m : ℤ} {t : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtDepth (originCube d m) t) (j : Fin d) :
    |Q.index j| ≤ extremeIdx t := by
  have h := abs_index_sub_le_of_mem_descendantsAtDepth hQ j
  simpa [originCube] using h

/-- Boundary touching propagates from a child to its parent. -/
theorem touchesBoundary_parent_of_child {m : ℤ} {t : ℕ} {S R : TriadicCube d}
    (hS : S.scale = m - (t : ℤ)) (hR : R ∈ childCubes S)
    (hRt : TouchesBoundary m R) : TouchesBoundary m S := by
  obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hR
  obtain ⟨i, hi⟩ := hRt
  dsimp only at hi
  have hd1 : ((digits i : ℕ) : ℤ) < 3 := by exact_mod_cast (digits i).is_lt
  have hd2 : (0 : ℤ) ≤ ((digits i : ℕ) : ℤ) := Int.natCast_nonneg _
  have hSroot : rootExtreme m S.scale = extremeIdx t := by
    rw [hS, rootExtreme_sub_natCast]
  have hRroot : rootExtreme m (S.scale - 1) = extremeIdx (t + 1) := by
    rw [hS, show m - (t : ℤ) - 1 = m - ((t + 1 : ℕ) : ℤ) from by push_cast; ring,
      rootExtreme_sub_natCast]
  rw [hRroot] at hi
  have hE : extremeIdx (t + 1) = 3 * extremeIdx t + 1 := rfl
  exact ⟨i, by rw [hSroot]; omega⟩

/-- **Boundary touching propagates to ancestors.**  Contrapositive: no descendant
of a cube in the interior of `□_m` ever touches `∂□_m`. -/
theorem touchesBoundary_of_mem_descendantsAtDepth {m : ℤ} :
    ∀ {s t : ℕ} {A Q : TriadicCube d}, A.scale = m - (t : ℤ) →
      Q ∈ descendantsAtDepth A s → TouchesBoundary m Q → TouchesBoundary m A := by
  intro s
  induction s with
  | zero =>
      intro t A Q _ hQ hQt
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hQ
      exact hQ ▸ hQt
  | succ s ih =>
      intro t A Q hA hQ hQt
      obtain ⟨S, hS, hQS⟩ := mem_descendantsAtDepth_succ_iff.mp hQ
      have hSscale : S.scale = m - ((t + s : ℕ) : ℤ) := by
        have h := scale_eq_sub_of_mem_descendantsAtDepth hS
        rw [hA] at h
        push_cast at h ⊢
        omega
      exact ih hA hS (touchesBoundary_parent_of_child hSscale hQS hQt)

/-! ## The Whitney partition -/

/-- **ABK26 `𝒲(□_m, n)`**: the layer-`n` cubes of the Whitney partition of `□_m` at
the scale profile `hn`.  A layer-`n` cube is a depth-`h_n` triadic descendant
of a child `C` of a boundary-touching depth-`(n-1)` descendant `A` of `□_m`,
where `C` itself does not touch `∂□_m`.  Layer `0` is empty: the recursion
starts at layer `1`. -/
def whitneyLayer (m : ℤ) (hn : ℕ → ℕ) (n : ℕ) : Finset (TriadicCube d) :=
  if 1 ≤ n then
    ((descendantsAtDepth (originCube d m) (n - 1)).filter (TouchesBoundary m)).biUnion
      fun A =>
        ((childCubes A).filter fun C => ¬ TouchesBoundary m C).biUnion
          fun C => descendantsAtDepth C (hn n)
  else ∅

/-- **ABK26 `𝒲(□_m)`**: the Whitney partition, the union of all its layers.  No
truncation: the family is the literal infinite one. -/
def whitneyPartition (m : ℤ) (hn : ℕ → ℕ) : Set (TriadicCube d) :=
  {Q | ∃ n : ℕ, Q ∈ whitneyLayer m hn n}

theorem mem_whitneyLayer_iff {m : ℤ} {hn : ℕ → ℕ} {n : ℕ} {Q : TriadicCube d} :
    Q ∈ whitneyLayer m hn n ↔
      1 ≤ n ∧ ∃ A ∈ descendantsAtDepth (originCube d m) (n - 1),
        TouchesBoundary m A ∧ ∃ C ∈ childCubes A, ¬ TouchesBoundary m C ∧
          Q ∈ descendantsAtDepth C (hn n) := by
  classical
  by_cases hn1 : 1 ≤ n
  · simp only [whitneyLayer, ite_eq_left hn1, Finset.mem_biUnion, Finset.mem_filter]
    aesop
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [whitneyLayer]

@[simp] theorem whitneyLayer_zero (m : ℤ) (hn : ℕ → ℕ) :
    whitneyLayer (d := d) m hn 0 = ∅ := by
  simp [whitneyLayer]

/-- **`e.W.n.def`, the size clause**: every layer-`n` cube has size `3^{m-n-h_n}`. -/
theorem scale_eq_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    Q.scale = m - (n : ℤ) - (hn n : ℤ) := by
  obtain ⟨hn1, A, hA, _, C, hC, _, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  have hAscale : A.scale = m - ((n - 1 : ℕ) : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hA
    simpa only [originCube] using h
  have hCscale := child_scale_of_mem_childCubes hC
  have hQscale := scale_eq_sub_of_mem_descendantsAtDepth hQC
  rw [hCscale, hAscale] at hQscale
  have hncast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hncast] at hQscale
  omega

/-- A layer-`n` cube is a depth-`(n + h_n)` triadic descendant of `□_m`. -/
theorem mem_descendantsAtDepth_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    Q ∈ descendantsAtDepth (originCube d m) (n + hn n) := by
  obtain ⟨hn1, A, hA, _, C, hC, _, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  have hAC : C ∈ descendantsAtDepth A 1 := by
    simpa only [descendantsAtDepth_one] using hC
  have hCroot := mem_descendantsAtDepth_add hA hAC
  have hQroot := mem_descendantsAtDepth_add hCroot hQC
  simpa only [show n - 1 + 1 + hn n = n + hn n from by omega] using hQroot

/-- **The termination clause**: no element of `𝒲(□_m)` touches `∂□_m`. -/
theorem not_touchesBoundary_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    ¬ TouchesBoundary m Q := by
  obtain ⟨hn1, A, hA, _, C, hC, hCnt, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  have hAscale : A.scale = m - ((n - 1 : ℕ) : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hA
    simpa only [originCube] using h
  intro hQt
  exact hCnt (touchesBoundary_of_mem_descendantsAtDepth
    (t := (n - 1) + 1)
    (by rw [child_scale_of_mem_childCubes hC, hAscale]; push_cast; ring) hQC hQt)

/-- Distinct layers are disjoint. -/
theorem whitneyLayer_disjoint {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn)
    {n n' : ℕ} (hne : n ≠ n') :
    Disjoint (whitneyLayer (d := d) m hn n) (whitneyLayer (d := d) m hn n') := by
  classical
  refine Finset.disjoint_left.mpr fun Q hQ hQ' => ?_
  have h1 := scale_eq_of_mem_whitneyLayer hQ
  have h2 := scale_eq_of_mem_whitneyLayer hQ'
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · have hh := hmono hlt.le
    omega
  · exact hne heq
  · have hh := hmono hgt.le
    omega

/-! ## The bad cubes of the partition -/

/-- **ABK26 `e.bad.cubes.in.partition`**: the bad family `ℐ = {□ ∈ 𝒲(□_m): 𝓑(□)
occurs}`. -/
def badFamily (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (omega : CutoffSample d) :
    Set (TriadicCube d) :=
  {Q | Q ∈ whitneyPartition m hn ∧ omega ∈ BadEvents.bad M Q}

/-- **ABK26 `ℐ_n = ℐ ∩ 𝒲(□_m, n)`**: the bad cubes of layer `n`. -/
def badFamilyLayer (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (omega : CutoffSample d) : Finset (TriadicCube d) :=
  @Finset.filter _ (fun Q => omega ∈ BadEvents.bad M Q) (Classical.decPred _)
    (whitneyLayer m hn n)

theorem mem_badFamilyLayer_iff {M : ABKModel d} {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {omega : CutoffSample d} {Q : TriadicCube d} :
    Q ∈ badFamilyLayer M m hn n omega ↔
      Q ∈ whitneyLayer m hn n ∧ omega ∈ BadEvents.bad M Q := by
  let : DecidablePred fun Q : TriadicCube d => omega ∈ BadEvents.bad M Q :=
    Classical.decPred _
  unfold badFamilyLayer
  rw [Finset.mem_filter]

theorem badFamilyLayer_subset (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (n : ℕ)
    (omega : CutoffSample d) :
    badFamilyLayer M m hn n omega ⊆ whitneyLayer m hn n :=
  fun _ hQ => (mem_badFamilyLayer_iff.mp hQ).1

/-! ## Adjacency, neighborhoods and components -/

/-- **`dist(□, □') = 0`** in the manuscript's `ℓ^∞` sense: the closed cubes
intersect.  On `Vec d = Fin d → ℝ` the ambient metric is the sup metric and
`Metric.closedBall (cubeCenter Q) (cubeRadius Q)` is the closed realization of
the triadic cube `Q`. -/
def CubeTouch (Q R : TriadicCube d) : Prop :=
  (Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) ∩
      Metric.closedBall (cubeCenter R) (HCPolySupport.cubeRadius R)).Nonempty

/-- The coordinatewise characterization of touching. -/
theorem cubeTouch_iff {Q R : TriadicCube d} :
    CubeTouch Q R ↔ ∀ i, |cubeCenter Q i - cubeCenter R i| ≤
      HCPolySupport.cubeRadius Q + HCPolySupport.cubeRadius R := by
  constructor
  · rintro ⟨z, hzQ, hzR⟩ i
    rw [closedBall_cubeCenter_eq_pi_Icc] at hzQ hzR
    have hQ := Set.mem_Icc.mp (hzQ i (Set.mem_univ i))
    have hR := Set.mem_Icc.mp (hzR i (Set.mem_univ i))
    rw [abs_le]
    constructor <;> linarith [hQ.1, hQ.2, hR.1, hR.2]
  · intro h
    refine ⟨fun i => max (cubeCenter Q i - HCPolySupport.cubeRadius Q)
      (cubeCenter R i - HCPolySupport.cubeRadius R), ?_, ?_⟩
    · rw [closedBall_cubeCenter_eq_pi_Icc]
      intro i _
      rw [Set.mem_Icc]
      have hi := abs_le.mp (h i)
      have hQn := HCPolySupport.cubeRadius_nonneg Q
      have hRn := HCPolySupport.cubeRadius_nonneg R
      exact ⟨le_max_left _ _, max_le (by linarith) (by linarith [hi.1])⟩
    · rw [closedBall_cubeCenter_eq_pi_Icc]
      intro i _
      rw [Set.mem_Icc]
      have hi := abs_le.mp (h i)
      have hQn := HCPolySupport.cubeRadius_nonneg Q
      have hRn := HCPolySupport.cubeRadius_nonneg R
      exact ⟨le_max_right _ _, max_le (by linarith [hi.2]) (by linarith)⟩

theorem cubeTouch_refl (Q : TriadicCube d) : CubeTouch Q Q :=
  ⟨cubeCenter Q, by
    rw [closedBall_cubeCenter_eq_pi_Icc]
    intro i _
    rw [Set.mem_Icc]
    exact ⟨by linarith [HCPolySupport.cubeRadius_nonneg Q],
      by linarith [HCPolySupport.cubeRadius_nonneg Q]⟩, by
    rw [closedBall_cubeCenter_eq_pi_Icc]
    intro i _
    rw [Set.mem_Icc]
    exact ⟨by linarith [HCPolySupport.cubeRadius_nonneg Q],
      by linarith [HCPolySupport.cubeRadius_nonneg Q]⟩⟩

theorem CubeTouch.symm {Q R : TriadicCube d} (h : CubeTouch Q R) : CubeTouch R Q := by
  rw [cubeTouch_iff] at h ⊢
  intro i
  rw [abs_sub_comm]
  linarith [h i]

/-- **ABK26 `e.neighborhood.def`**: the neighborhood `𝒩(𝒥) = {□ ∈ 𝒲(□_m): dist(□,
𝒥) = 0}` of a subfamily `𝒥 ⊆ 𝒲(□_m)`, read cubewise (see the module docstring). -/
def whitneyNeighborhood (m : ℤ) (hn : ℕ → ℕ) (J : Set (TriadicCube d)) :
    Set (TriadicCube d) :=
  {Q | Q ∈ whitneyPartition m hn ∧ ∃ R ∈ J, CubeTouch Q R}

theorem subset_whitneyNeighborhood {m : ℤ} {hn : ℕ → ℕ} {J : Set (TriadicCube d)}
    (hJ : J ⊆ whitneyPartition m hn) : J ⊆ whitneyNeighborhood m hn J :=
  fun Q hQ => ⟨hJ hQ, Q, hQ, cubeTouch_refl Q⟩

theorem whitneyNeighborhood_subset (m : ℤ) (hn : ℕ → ℕ) (J : Set (TriadicCube d)) :
    whitneyNeighborhood m hn J ⊆ whitneyPartition m hn := fun _ hQ => hQ.1

/-- **The chain relation**: `Q` and `R` are joined by a chain of pairwise adjacent
cubes of `J`. -/
def BadChain (J : Set (TriadicCube d)) : TriadicCube d → TriadicCube d → Prop :=
  Relation.ReflTransGen fun A B => A ∈ J ∧ B ∈ J ∧ CubeTouch A B

/-- The connected component of `Q` inside `J`. -/
def badComponent (J : Set (TriadicCube d)) (Q : TriadicCube d) :
    Set (TriadicCube d) :=
  {R | R ∈ J ∧ BadChain J Q R}

theorem badChain_symm {J : Set (TriadicCube d)} {Q R : TriadicCube d}
    (h : BadChain J Q R) : BadChain J R Q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hAB ih =>
      exact Relation.ReflTransGen.head ⟨hAB.2.1, hAB.1, hAB.2.2.symm⟩ ih

theorem self_mem_badComponent {J : Set (TriadicCube d)} {Q : TriadicCube d}
    (hQ : Q ∈ J) : Q ∈ badComponent J Q :=
  ⟨hQ, Relation.ReflTransGen.refl⟩

/-- **"`𝒞` intersects layer `n`"**. -/
def IntersectsLayer (m : ℤ) (hn : ℕ → ℕ) (C : Set (TriadicCube d)) (n : ℕ) : Prop :=
  (C ∩ (whitneyLayer (d := d) m hn n : Set (TriadicCube d))).Nonempty

theorem intersectsLayer_iff {m : ℤ} {hn : ℕ → ℕ} {C : Set (TriadicCube d)}
    {n : ℕ} :
    IntersectsLayer m hn C n ↔ ∃ Q ∈ C, Q ∈ whitneyLayer m hn n :=
  ⟨fun ⟨Q, hQ⟩ => ⟨Q, hQ.1, hQ.2⟩, fun ⟨Q, hQ, hQ'⟩ => ⟨Q, hQ, hQ'⟩⟩

end

end Algsuperdiff.Section3.Provider.Whitney
