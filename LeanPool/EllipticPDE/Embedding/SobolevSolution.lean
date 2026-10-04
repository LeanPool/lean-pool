/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.H01Sobolev
public import LeanPool.EllipticPDE.Existence.Garding


/-!
# Integrability of the weak solution above `L²`

`EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded` bounds the `L^q(Ω)` seminorm of an
element of `H₀¹(Ω)` by its gradient coordinates, for every `q` up to the Sobolev conjugate of `2`.
`EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded` bounds the
`H¹` norm of the weak solution by the `L²` norm of the datum. Composing them takes the solution
out of `L²` and up to the critical exponent, with a bound by the datum alone.

The two hypotheses are those of the existence theorem, no drift and a nonnegative zeroth-order
coefficient, together with `2 < d`, which is what the critical exponent asks for.

## Main declarations

* `EllipticPdes.Embedding.eLpNorm_weakSolution_le`: the weak solution lies in `L^q(Ω)` for every
  `q` up to the critical exponent, with `‖u‖_{L^q} ≤ K ‖f‖_{L²}`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Theorem 3 and §6.2.2 Theorem 3.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Weak solution above `L²`.** On a bounded measurable domain in dimension greater than
two, with no drift and a nonnegative zeroth-order coefficient, the weak solution of `L u = f`
lies in `L^q(Ω)` for every exponent `q` up to the Sobolev conjugate of `2`, and its `L^q`
seminorm is bounded by the `L²` norm of the datum.

The constant is the Sobolev constant times the dimension times the constant of the existence
theorem, so it depends on the domain, the operator and the exponent, and not on the datum. -/
theorem eLpNorm_weakSolution_le (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hd : 2 < n + 1)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    {q : ℝ≥0} (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : L2D Ω) (u : H01 Ω),
      (∀ v : H01 Ω, Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      MemLp ((u : H1amb Ω) 0) q (volume.restrict Ω) ∧
        eLpNorm ((u : H1amb Ω) 0) q (volume.restrict Ω) ≤ ENNReal.ofReal (K * ‖f‖) := by
  obtain ⟨CP, hCP, hsol⟩ :=
    FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded Op hΩb hb hc
  have hlam : 0 < Op.lam := Op.lam_pos
  refine ⟨sobolevConstOfLe Ω q * (n + 1) * ((CP + 1) / Op.lam), by positivity,
    fun f u hu => ?_⟩
  have hSob := eLpNorm_le_of_mem_H01_of_isBounded (d := n + 1) hΩm hΩb hd hq u.2
  refine ⟨memLp_of_mem_H01 hSob, ?_⟩
  -- The energy bound on the solution, from the existence theorem.
  have hen : ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := (hsol f).2 u hu
  have hfnn : (0 : ℝ) ≤ ‖f‖ := norm_nonneg _
  calc eLpNorm ((u : H1amb Ω) 0) q (volume.restrict Ω)
      ≤ sobolevConstOfLe Ω q * ∑ i : Fin (n + 1), ‖(u : H1amb Ω) i.succ‖ₑ := hSob
    _ ≤ (sobolevConstOfLe Ω q : ℝ≥0∞) * ENNReal.ofReal ((n + 1 : ℕ) * ‖u‖) := by
        gcongr
        exact sum_enorm_succ_le u
    _ = ENNReal.ofReal (sobolevConstOfLe Ω q * ((n + 1 : ℕ) * ‖u‖)) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (sobolevConstOfLe Ω q * (n + 1) * ((CP + 1) / Op.lam) * ‖f‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hmul : ((n + 1 : ℕ) : ℝ) * ‖u‖ ≤ ((n + 1 : ℕ) : ℝ) * ((CP + 1) / Op.lam * ‖f‖) := by
          have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hen this
        calc (sobolevConstOfLe Ω q : ℝ) * (((n + 1 : ℕ) : ℝ) * ‖u‖)
            ≤ (sobolevConstOfLe Ω q : ℝ) * (((n + 1 : ℕ) : ℝ) * ((CP + 1) / Op.lam * ‖f‖)) := by
              exact mul_le_mul_of_nonneg_left hmul (by positivity)
          _ = (sobolevConstOfLe Ω q : ℝ) * ((n : ℝ) + 1) * ((CP + 1) / Op.lam) * ‖f‖ := by
              push_cast
              ring

end EllipticPdes.Embedding
