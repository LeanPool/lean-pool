/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.SobolevLadderFullStep
public import LeanPool.EllipticPDE.Embedding.ClassicalDeriv


/-!
# Hölder regularity of finite order from a bounded supply of weak derivatives

Guo's Sobolev embedding (Guo, *Partial Differential Equations*, Theorem IV.2.3) has two cases.
The first raises the exponent, and `EllipticPdes.Embedding.memLp_of_gradClosed_fullStep` runs it.
The second reads a bounded supply of weak derivatives as classical ones: for `u ∈ W^{m,p}(Ω)`
with `m > n/p`, the conclusion is `u ∈ C^{m-1-⌊n/p⌋, γ}(Ω)`. This file proves the second case at
`p = 2`, locally, for a family closed under weak differentiation as far as `m`.

## Order the supply pays for

The supply is spent in three places. Morrey asks for the weak gradient, so one order goes there;
the ladder takes `⌊d/2⌋` more raising that gradient from `L²` to `L^{2d}`; and reading the `n`-th
classical derivative asks the same of every index `n` levels up. So an index of depth `dep i`
reaches `C^n` while `dep i + n + 1 + ⌊d/2⌋ ≤ m`, and at `dep i = 0` that is
`n = m - 1 - ⌊d/2⌋`, which is Guo's order exactly.

## Hölder exponent

The ladder lands on `L^{2d}` and `EllipticPdes.Embedding.morrey_ball` reads off `1 - d/(2d)`, so
the exponent is `1/2` in every dimension. For `d` odd this is Guo's `⌊d/2⌋ + 1 - d/2` on the
nose. For `d` even `d/2` is an integer, Guo's statement leaves `γ` free in `(0, 1)`, and `1/2` is
one admissible choice: the ladder's landing reciprocal is `0` there, so every finite exponent is
reached and `2d` is the one this file fixes.

## Main declarations

* `EllipticPdes.Embedding.morreyExponent_two_mul`: the landing exponent is `1/2`.
* `EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed`: representatives of class
  `C^{n, 1/2}`, for every order the supply pays for, together with the identification of the
  family's entries as their classical partial derivatives.

## References

Guo, *Partial Differential Equations*, Theorem IV.2.3.
Evans, *Partial Differential Equations* (2nd ed.), §5.6.3.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- At the exponent `2d` the Morrey exponent is `1/2`, whatever the dimension. -/
theorem morreyExponent_two_mul (hd : 0 < d) : morreyExponent d (2 * (d : ℝ)) = (1 / 2 : ℝ≥0) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnn : 0 ≤ 1 - (d : ℝ) / (2 * (d : ℝ)) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  refine NNReal.coe_injective ?_
  rw [morreyExponent, Real.coe_toNNReal _ hnn]
  push_cast
  field_simp
  norm_num

/-- **Classical derivatives of finite order from a bounded supply of weak ones.** Let `F` assign a
function to each index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on
`Metric.ball c R`, and let `dep` record how far an index sits above the root. If every index of
depth at most `m` lies in `L²` there and every index of depth below `m` has its weak gradient in
the family, then on any smaller concentric ball each index has a representative of class `C^n`
whenever `dep i + n + 1 + ⌊d/2⌋ ≤ m`, and that representative is Hölder-`1/2` as soon as
`dep i + 1 + ⌊d/2⌋ ≤ m`.

The proof is the one `EllipticPdes.Embedding.contDiffOn_of_gradClosed` takes, run against a
supply that runs out. The ladder raises the weak gradient of a qualifying index to `L^{2d}`,
Morrey converts that into a Hölder representative, and a continuous function with a continuous
weak gradient is classically differentiable, so an induction on the order reads the family as
`C^n` with no further shrinking of the ball. Each induction step spends one order, which is what
the depth condition records.

The last component states what the family means: on the inner ball the classical derivative of
`v i` is the tuple of the `v (nxt i k)`, so an entry of depth `n` is the order-`n` classical
partial derivative of the root and the Hölder bound above is a bound on that derivative. -/
theorem contDiffOn_holder_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    {nxt : ι → Fin d → ι} {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) :
    ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, dep i + 1 + d / 2 ≤ m → v i =ᵐ[volume.restrict (Metric.ball c r)] F i) ∧
      (∀ i, dep i + 1 + d / 2 ≤ m →
        ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) (v i) (Metric.ball c r)) ∧
      (∀ (n : ℕ) (i : ι), dep i + n + 1 + d / 2 ≤ m →
        ContDiffOn ℝ (n : ℕ) (v i) (Metric.ball c r)) ∧
      (∀ i, dep i + 2 + d / 2 ≤ m → ∀ y ∈ Metric.ball c r,
        HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) := by
  classical
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp : (d : ℝ) < 2 * (d : ℝ) := by linarith
  -- Every member the supply reaches is integrable on the inner ball.
  have hFint : ∀ i, dep i ≤ m → IntegrableOn (F i) (Metric.ball c r) volume := fun i hi =>
    ((hmem i hi).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable (by norm_num)
  -- The ladder, at every index whose depth leaves `⌊d/2⌋` rungs above it.
  have hladder : ∀ i, dep i + d / 2 ≤ m →
      MemLp (F i) (ENNReal.ofReal (2 * (d : ℝ))) (volume.restrict (Metric.ball c r)) := by
    intro i hi
    have h := memLp_two_mul_of_gradClosed_fullStep hd c hdep hr hrR hgrad hmem i hi
    have hcast : ENNReal.ofReal (2 * (d : ℝ)) = ((2 * (d : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rwa [hcast]
  have hgradr : ∀ i, dep i < m →
      HasWeakGradOn (Metric.ball c r) (F i) (fun k => F (nxt i k)) := fun i hi =>
    (hgrad i hi).mono (Metric.ball_subset_ball hrR.le)
  obtain ⟨C, hC⟩ := morrey_ball hd hp c hr
  -- Morrey, at every index whose gradient the ladder reaches. Indices below that keep `F` itself,
  -- since nothing downstream reads them.
  have hqual : ∀ i, ∃ w : EuclideanSpace ℝ (Fin d) → ℝ, dep i + 1 + d / 2 ≤ m →
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) w (Metric.ball c r) := by
    intro i
    by_cases hi : dep i + 1 + d / 2 ≤ m
    · obtain ⟨w, hwae, hwhol⟩ := hC (F i) (fun k => F (nxt i k)) (hFint i (by omega))
        (fun k => hladder (nxt i k) (by have := hdep i k; omega)) (hgradr i (by omega))
      exact ⟨w, fun _ => ⟨hwae, ⟨_, by rwa [morreyExponent_two_mul hd] at hwhol⟩⟩⟩
    · exact ⟨F i, fun h => absurd h hi⟩
  choose v hv using hqual
  have hvae : ∀ i, dep i + 1 + d / 2 ≤ m →
      v i =ᵐ[volume.restrict (Metric.ball c r)] F i := fun i hi => (hv i hi).1
  have hvhol : ∀ i, dep i + 1 + d / 2 ≤ m →
      ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) (v i) (Metric.ball c r) := fun i hi => (hv i hi).2
  have hvc : ∀ i, dep i + 1 + d / 2 ≤ m → ContinuousOn (v i) (Metric.ball c r) := by
    intro i hi
    obtain ⟨M, hM⟩ := hvhol i hi
    exact hM.continuousOn (by norm_num)
  have hvint : ∀ i, dep i + 1 + d / 2 ≤ m →
      IntegrableOn (v i) (Metric.ball c r) volume := fun i hi =>
    (hFint i (by omega)).congr (hvae i hi).symm
  have hvgrad : ∀ i, dep i + 2 + d / 2 ≤ m →
      HasWeakGradOn (Metric.ball c r) (v i) (fun k => v (nxt i k)) := fun i hi =>
    (hgradr i (by omega)).congr_ae (hvae i (by omega)).symm
      fun k => (hvae (nxt i k) (by have := hdep i k; omega)).symm
  -- The classical derivative of a representative is the representative of the derivative.
  have hfd : ∀ i, dep i + 2 + d / 2 ≤ m → ∀ y ∈ Metric.ball c r,
      HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y := by
    intro i hi y hy
    exact hasFDerivAt_of_continuousOn_hasWeakGradOn measurableSet_ball Metric.isOpen_ball
      (hvint i (by omega)) (fun k => hvint (nxt i k) (by have := hdep i k; omega))
      (hvc i (by omega)) (fun k => hvc (nxt i k) (by have := hdep i k; omega)) (hvgrad i hi) hy
  -- Every order the supply pays for, by induction, with no further shrinking.
  have hcn : ∀ (n : ℕ) (i : ι), dep i + n + 1 + d / 2 ≤ m →
      ContDiffOn ℝ (n : ℕ) (v i) (Metric.ball c r) := by
    intro n
    induction n with
    | zero => intro i hi; simpa using hvc i (by omega)
    | succ n ih =>
      intro i hi
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
      refine ⟨fun y hy =>
        ((hfd i (by omega) y hy).differentiableAt).differentiableWithinAt, by simp, ?_⟩
      have hsum : ContDiffOn ℝ (n : ℕ) (fun y => gradCLM (fun k => v (nxt i k)) y)
          (Metric.ball c r) := by
        change ContDiffOn ℝ (n : ℕ)
          (fun y => ∑ k, v (nxt i k) y •
            (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) (Metric.ball c r)
        exact ContDiffOn.sum fun k _ =>
          (ih (nxt i k) (by have := hdep i k; omega)).smul contDiffOn_const
      exact hsum.congr fun y hy => (hfd i (by omega) y hy).fderiv
  exact ⟨v, hvae, hvhol, hcn, hfd⟩


/-! ### Hölder exponent Guo leaves open -/

/-- **Hölder clause at a general exponent.** The ladder run for `s` rungs lands at any `P`
the reciprocal relation `1/2 - s/d ≤ 1/P` admits, and Morrey at `P > d` reads off the exponent
`1 - d/P`. The fixed exponent `1/2` of `contDiffOn_holder_of_gradClosed` is this at `s = ⌊d/2⌋`
and `P = 2d`. -/
theorem exists_holderOnWith_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R)))
    {s : ℕ} {P : ℝ≥0} (hsd : 2 * s ≤ d) (hP2 : (2 : ℝ≥0) ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹)
    (i : ι) (hi : dep i + 1 + s ≤ m) :
    ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M (morreyExponent d (P : ℝ)) w (Metric.ball c r) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hcast : ((P : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (P : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
  -- The gradient coordinates reach `L^P` on the inner ball.
  have hgradP : ∀ k, MemLp (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (Metric.ball c r)) := by
    intro k
    have h := memLp_of_gradClosed_fullStep hd c hdep s hsd hP2 hPs hr hrR hgrad hmem
      (nxt i k) (by have := hdep i k; omega)
    rwa [hcast] at h
  -- The member itself is integrable there.
  have hFint : IntegrableOn (F i) (Metric.ball c r) volume :=
    ((hmem i (by omega)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable (by norm_num)
  have hgradr : HasWeakGradOn (Metric.ball c r) (F i) (fun k => F (nxt i k)) :=
    (hgrad i (by omega)).mono (Metric.ball_subset_ball hrR.le)
  obtain ⟨C, hC⟩ := morrey_ball hd hPd c hr
  obtain ⟨w, hwae, hwhol⟩ := hC (F i) (fun k => F (nxt i k)) hFint hgradP hgradr
  exact ⟨w, hwae, ⟨_, hwhol⟩⟩

/-- **Guo's free Hölder exponent in even dimension.** When `d/2` is an integer, which at `p = 2`
is Guo's case `n/p ∈ ℕ`, the ladder reaches every finite exponent, so the Hölder exponent may be
any value in `(0,1)`. In odd dimension the reciprocal `1/2 - ⌊d/2⌋/d = 1/(2d)` caps the exponent
at `2d` and the Hölder exponent at `1/2`, which is Guo's other case. -/
theorem exists_holderOnWith_of_gradClosed_even (hd : 0 < d) (hdeven : 2 * (d / 2) = d)
    (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R)))
    {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (i : ι) (hi : dep i + 1 + d / 2 ≤ m) :
    ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M γ w (Metric.ball c r) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd2 : (2 : ℕ) ≤ d := by omega
  have hγ1R : ((γ : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hγ1
  have hden : (0 : ℝ) < 1 - (γ : ℝ) := by linarith
  -- The exponent whose Morrey exponent is `γ`.
  set P : ℝ≥0 := Real.toNNReal ((d : ℝ) / (1 - (γ : ℝ))) with hP_def
  have hPcoe : ((P : ℝ≥0) : ℝ) = (d : ℝ) / (1 - (γ : ℝ)) := by
    rw [hP_def, Real.coe_toNNReal _ (by positivity)]
  have hPd : (d : ℝ) < (P : ℝ) := by
    rw [hPcoe, lt_div_iff₀ hden]
    have hγ0R : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγ0
    nlinarith
  have hP2 : (2 : ℝ≥0) ≤ P := by
    rw [← NNReal.coe_le_coe, NNReal.coe_ofNat]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith [hPd]
  have hPs : 2⁻¹ - ((d / 2 : ℕ) : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹ := by
    have hhalf : ((d / 2 : ℕ) : ℝ) * (d : ℝ)⁻¹ = 2⁻¹ := by
      have hne : ((d / 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hR : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) := by
        conv_lhs => rw [hdeven.symm]
        push_cast
        ring
      rw [hR]
      field_simp
    rw [hhalf, sub_self]
    positivity
  obtain ⟨w, hwae, M, hwhol⟩ := exists_holderOnWith_of_gradClosed hd c hr hrR hdep hgrad hmem
    (s := d / 2) (P := P) (by omega) hP2 hPd hPs i hi
  refine ⟨w, hwae, M, ?_⟩
  have hexp : morreyExponent d (P : ℝ) = γ := by
    have := coe_morreyExponent (d := d) hPd hd
    refine NNReal.coe_injective ?_
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hdenne : (1 - (γ : ℝ)) ≠ 0 := ne_of_gt hden
    rw [this, hPcoe, div_div_eq_mul_div, mul_comm (d : ℝ) (1 - (γ : ℝ)), mul_div_assoc,
      div_self hdne, mul_one]
    ring
  rwa [hexp] at hwhol


/-- **Hölder estimate with its constant**, in the shape Guo states: one constant, depending
on the dimension, the exponent and the ball alone, bounding the Hölder seminorm of every member
of every family by the `L^P` norms of that member's first derivatives.

`exists_holderOnWith_of_gradClosed` is this with the constant discarded. The remaining step to
Guo's `‖u‖_{C^{k-1-⌊n/p⌋,γ}} ≤ C‖u‖_{W^{k,p}}` is the ladder's own constant, which takes the
`L^P` norms here back to the `L²` data. -/
theorem exists_const_holderOnWith_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (ι : Type*)
    {s : ℕ} {P : ℝ≥0} (hsd : 2 * s ≤ d) (hP2 : (2 : ℝ≥0) ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
            HolderOnWith
              (C * ∑ k, (eLpNorm (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
                          (volume.restrict (Metric.ball c r))).toNNReal)
              (morreyExponent d (P : ℝ)) w (Metric.ball c r) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hcast : ((P : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (P : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
  obtain ⟨C, hC⟩ := morrey_ball hd hPd c hr
  refine ⟨C, fun {F nxt dep m} hdep hgrad hmem i hi => ?_⟩
  have hgradP : ∀ k, MemLp (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (Metric.ball c r)) := by
    intro k
    have h := memLp_of_gradClosed_fullStep hd c hdep s hsd hP2 hPs hr hrR hgrad hmem
      (nxt i k) (by have := hdep i k; omega)
    rwa [hcast] at h
  have hFint : IntegrableOn (F i) (Metric.ball c r) volume :=
    ((hmem i (by omega)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable (by norm_num)
  have hgradr : HasWeakGradOn (Metric.ball c r) (F i) (fun k => F (nxt i k)) :=
    (hgrad i (by omega)).mono (Metric.ball_subset_ball hrR.le)
  exact hC (F i) (fun k => F (nxt i k)) hFint hgradP hgradr


/-- **Guo's clause (ii) with its constant against the `L²` data.** Composing the ladder's
constant with Morrey's gives one constant, depending on the dimension, the rung count, the
exponent and the two radii, bounding the Hölder seminorm of every member by a uniform `L²` bound
on the family over the outer ball. This is the shape of Guo's
`‖u‖_{C^{k-1-⌊n/p⌋,γ}} ≤ C‖u‖_{W^{k,p}}` at `p = 2`. -/
theorem exists_const_holderOnWith_of_gradClosed_of_bound (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (ι : Type*)
    {s : ℕ} {P : ℝ≥0} (hsd : 2 * s ≤ d) (hP2 : (2 : ℝ≥0) ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) 2 (volume.restrict (Metric.ball c R)) ≤ M) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
            HolderOnWith (C * M) (morreyExponent d (P : ℝ)) w (Metric.ball c r) := by
  obtain ⟨Cm, hCm⟩ := exists_const_holderOnWith_of_gradClosed hd c hr hrR ι hsd hP2 hPd hPs
  obtain ⟨K, hK⟩ := exists_const_eLpNorm_le_of_gradClosed_fullStep hd c ι s hsd hP2 hPs hr hrR
  have hcast : ((P : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (P : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
  refine ⟨Cm * d * K, ?_⟩
  intro F nxt dep m hdep hgrad hmem M hM i hi
  obtain ⟨w, hwae, hwhol⟩ := hCm hdep hgrad hmem i hi
  refine ⟨w, hwae, hwhol.mono_const ?_⟩
  have hterm : ∀ k : Fin d, (eLpNorm (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (Metric.ball c r))).toNNReal ≤ K * M := by
    intro k
    have h := hK hdep hgrad hmem M hM (nxt i k) (by have := hdep i k; omega)
    rw [hcast] at h
    have hcoe' : eLpNorm (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
        (volume.restrict (Metric.ball c r)) ≤ ((K * M : ℝ≥0) : ℝ≥0∞) := by
      rwa [ENNReal.coe_mul]
    have hne : eLpNorm (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
        (volume.restrict (Metric.ball c r)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hcoe'
    simpa using (ENNReal.toNNReal_le_toNNReal hne ENNReal.coe_ne_top).mpr hcoe'
  calc Cm * ∑ k, (eLpNorm (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
          (volume.restrict (Metric.ball c r))).toNNReal
      ≤ Cm * ∑ _k : Fin d, K * M := by
        gcongr with k _
        exact hterm k
    _ = Cm * d * K * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end EllipticPdes.Embedding
