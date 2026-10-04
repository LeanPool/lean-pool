/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.HolderOfGradClosed
public import LeanPool.EllipticPDE.Embedding.SobolevLadderGeneral


/-!
# Hölder continuity at a general base exponent

`EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed` runs the ladder from `L²` and reads
the Hölder exponent off Morrey's inequality at the exponent the ladder reaches. Morrey is already
stated for every exponent above the dimension, and the rung count and the landing exponent are
already free there, so the base exponent is the only thing left at `2`. This file frees it, which
is the second case of Evans, *Partial Differential Equations*, §5.6.3 Theorem 6, and of Guo,
*Partial Differential Equations*, Theorem IV.2.3, at the exponent each quantifies over.

## Landing exponent

Running `s` rungs from `p₀` lands at the reciprocal `1/p₀ - s/d`, and Morrey at that exponent
gives the Hölder exponent `1 - d/P = s + 1 - d/p₀`. At `s = ⌊d/p₀⌋` that is the
`⌊n/p⌋ + 1 - n/p` of the cited statements. When `d/p₀` is an integer the reciprocal reaches `0`,
the ladder reaches every finite exponent, and the Hölder exponent is free in `(0,1)`, which is
the other case those statements separate out.

## Main declarations

* `EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general`: the Hölder clause at a
  general base exponent.
* `EllipticPdes.Embedding.morreyExponent_eq_ladder`: the exponent it lands on is the one the
  cited statements name.

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (ii).
Guo, *Partial Differential Equations*, Theorem IV.2.3 case (ii).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Hölder clause at a general base exponent.** The ladder run for `s` rungs from `L^{p₀}`
lands at any `P` the reciprocal relation `1/p₀ - s/d ≤ 1/P` admits, and Morrey at `P > d` reads
off the exponent `1 - d/P`. -/
theorem exists_holderOnWith_of_gradClosed_general (hd : 1 < d) (c : EuclideanSpace ℝ (Fin d))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict (Metric.ball c R)))
    {s : ℕ} {P : ℝ≥0} (hsd : (p₀ : ℝ) * s ≤ (d : ℝ)) (hp₀P : p₀ ≤ P)
    (hPd : (d : ℝ) < (P : ℝ))
    (hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹)
    (i : ι) (hi : dep i + 1 + s ≤ m) :
    ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M (morreyExponent d (P : ℝ)) w (Metric.ball c r) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hd0 : 0 < d := by omega
  have hp₀E : (1 : ℝ≥0∞) ≤ (p₀ : ℝ≥0∞) := by exact_mod_cast hp₀
  have hcast : ((P : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (P : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
  -- The gradient coordinates reach `L^P` on the inner ball.
  have hgradP : ∀ k, MemLp (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (Metric.ball c r)) := by
    intro k
    have h := memLp_of_gradClosed_general hd c hp₀ hdep s hsd hp₀P hPs hr hrR hgrad hmem
      (nxt i k) (by have := hdep i k; omega)
    rwa [hcast] at h
  -- The member itself is integrable there.
  have hFint : IntegrableOn (F i) (Metric.ball c r) volume :=
    ((hmem i (by omega)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable hp₀E
  have hgradr : HasWeakGradOn (Metric.ball c r) (F i) (fun k => F (nxt i k)) :=
    (hgrad i (by omega)).mono (Metric.ball_subset_ball hrR.le)
  obtain ⟨C, hC⟩ := morrey_ball hd0 hPd c hr
  obtain ⟨w, hwae, hwhol⟩ := hC (F i) (fun k => F (nxt i k)) hFint hgradP hgradr
  exact ⟨w, hwae, ⟨_, hwhol⟩⟩

/-- **Agreement of the ladder's exponent with the cited one.** At the landing
reciprocal `1/P = 1/p₀ - s/d`, Morrey's exponent is `s + 1 - d/p₀`, which at `s = ⌊d/p₀⌋` is the
`⌊n/p⌋ + 1 - n/p` of Evans §5.6.3 Theorem 6 and Guo Theorem IV.2.3. -/
theorem morreyExponent_eq_ladder (hd : 0 < d) {p₀ P : ℝ≥0} {s : ℕ}
    (hp₀ : 0 < (p₀ : ℝ)) (hPd : (d : ℝ) ≤ (P : ℝ))
    (hP : (P : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹) :
    ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ) = (s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hP0 : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le hdR hPd
  have hnn : (0 : ℝ) ≤ 1 - (d : ℝ) / (P : ℝ) := by
    rw [sub_nonneg, div_le_one hP0]
    exact hPd
  have hval : 1 - (d : ℝ) / (P : ℝ) = (s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ) := by
    rw [div_eq_mul_inv, hP]
    field_simp
    ring
  rw [morreyExponent, Real.coe_toNNReal _ hnn, hval]

end EllipticPdes.Embedding
