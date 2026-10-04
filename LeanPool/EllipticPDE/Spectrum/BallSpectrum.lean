/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Spectrum.EigenFamily
public import LeanPool.EllipticPDE.Embedding.DirectMethod


/-!
# Dirichlet spectrum of the unit ball

Every eigenvalue statement of the chapter asks that `H₀¹(Ω)` have an element of nonzero `L²`
class, which is false for a domain of measure zero and so cannot be dropped in general. On the
unit ball it is discharged: `EllipticPdes.Embedding.exists_norm_rellichEmbL_eq_one` at `q = 2`
produces an element whose `L²` norm is one, and
`EllipticPdes.Embedding.coeFn_sobolevEmbL` identifies that norm with the norm of the function
coordinate.

`dirichlet_principal_eigenpair_ball` is then the principal eigenvalue theorem with no hypotheses
beyond `2 < d`.

## Main declarations

* `EllipticPdes.Sobolev.exists_embL2_ne_zero_ball`: the unit ball supports a function of nonzero
  `L²` class in `H₀¹`.
* `EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball`: the principal Dirichlet eigenvalue
  of the unit ball, attained and positive.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 2.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Bornology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis EllipticPdes.Embedding

variable {d : ℕ}

/-- The unit ball of `ℝ^d`. -/
local notation "B1" => ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- **Function of nonzero `L²` class on the unit ball.** A renormalised bump has unit
`L²` norm, and the `L²` class of its graph is the function it represents. -/
theorem exists_embL2_ne_zero_ball (hd : 2 < d) : ∃ V : H01 B1, embL2 B1 V ≠ 0 := by
  have hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := isBounded_ball
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ ((2 : ℝ≥0) : ℝ)⁻¹ := by
    have : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    linarith
  have : Fact (1 ≤ (((2 : ℝ≥0)) : ℝ≥0∞)) := ⟨by
    rw [show (((2 : ℝ≥0)) : ℝ≥0∞) = (2 : ℝ≥0∞) by norm_cast]
    norm_num⟩
  obtain ⟨V, hV⟩ :=
    exists_norm_rellichEmbL_eq_one (q := 2) hΩb hd (by norm_num) hq
  refine ⟨V, fun h0 => ?_⟩
  have hz : ((V : H1amb B1) 0) = (0 : L2D B1) := by rw [← embL2_apply]; exact h0
  have hcoe : ⇑(rellichEmbL (q := 2) measurableSet_ball hΩb hd hq V)
      =ᵐ[volume.restrict B1] ⇑((V : H1amb B1) 0) := coeFn_sobolevEmbL _ V
  have hzero : ⇑((V : H1amb B1) 0) =ᵐ[volume.restrict B1]
      (0 : EuclideanSpace ℝ (Fin d) → ℝ) := by
    rw [hz]
    exact Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (volume.restrict B1)
  have hae : ⇑(rellichEmbL (q := 2) measurableSet_ball hΩb hd hq V)
      =ᵐ[volume.restrict B1] (0 : EuclideanSpace ℝ (Fin d) → ℝ) := hcoe.trans hzero
  have hnorm : ‖rellichEmbL (q := 2) measurableSet_ball hΩb hd hq V‖ = 0 := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_zero]
    simp
  rw [hV] at hnorm
  exact one_ne_zero hnorm

/-- **Principal Dirichlet eigenvalue of the unit ball**, with `2 < d` the only hypothesis:
there is a `U` of unit `L²` norm attaining the infimum of the Rayleigh quotient, the infimum is
positive, and `U` solves the weak eigenvalue problem. -/
theorem dirichlet_principal_eigenpair_ball (hd : 2 < d) :
    ∃ U : H01 B1, ‖embL2 B1 U‖ = 1 ∧
      laplaceBilin B1 U U = principalEigenvalue (laplaceBilin B1) ∧
      0 < principalEigenvalue (laplaceBilin B1) ∧
      ∀ V : H01 B1, laplaceBilin B1 U V
        = principalEigenvalue (laplaceBilin B1) * ⟪embL2 B1 U, embL2 B1 V⟫ := by
  have hne := exists_embL2_ne_zero_ball hd
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact dirichlet_principal_eigenpair_of_bounded _ measurableSet_ball isBounded_ball hne

end EllipticPdes.Sobolev
