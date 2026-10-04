/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.DirectMethod
public import LeanPool.EllipticPDE.Analysis.DirectMethodForm


/-!
# Semilinear Dirichlet problem below the critical exponent

Minimising the Dirichlet energy `∫ |∇u|²` over the functions of unit `L^q(Ω)` norm on the unit
ball, for `2 ≤ q < 2⋆`, produces a weak solution of

`-Δu = λ|u|^{q-2}u`,   `λ = ∫ |∇u|² > 0`,

which is the equation of Guo's Section IX.1. `EllipticPdes.Analysis.exists_bilin_minimiser`
supplies the minimiser and `EllipticPdes.Analysis.euler_lagrange_of_bilin_min` supplies the
equation, with the Rellich compact embedding
`EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt` as the only analytic input beyond
coercivity.

`EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt` runs the same two steps at the
graph norm of `H₀¹(Ω)` rather than at the Dirichlet energy, and reaches
`-Δu + u = λ|u|^{q-2}u`. Poincaré makes the two quadratics equivalent, so both minimisation
problems have solutions; their minimisers differ, and so do the equations. Guo states the
Dirichlet-energy one.

## Main declarations

* `EllipticPdes.Embedding.exists_dirichlet_minimiser_of_lt`: the Dirichlet energy attains its
  minimum on the unit `L^q` sphere.
* `EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt`: the minimiser solves
  `-Δu = λ|u|^{q-2}u`.
* `EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt'`: the same identity written out
  over the gradient coordinates.

## References

Y. Guo, *Partial Differential Equations*, Section IX.1; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §8.5.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Bornology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Analysis EllipticPdes.Poincare

variable {d : ℕ} {p' q : ℝ≥0}

section

variable [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The unit ball of `ℝ^d`, where the argument runs. -/
local notation "B1" => ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- **Direct method at the Dirichlet energy.** Below the critical exponent the Dirichlet
energy attains its minimum on the functions of unit `L^q` norm. -/
theorem exists_dirichlet_minimiser_of_lt
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p') :
    ∃ U : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧
      ∀ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1 →
        laplaceBilin B1 U U ≤ laplaceBilin B1 V V := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact exists_bilin_minimiser (laplaceBilin_coercive_of_bounded hΩb) (laplaceBilin_symm _)
    (rellichEmbL measurableSet_ball hΩb hd hq)
    (rellichEmbL_isCompact_of_lt measurableSet_ball hΩb hd hq hq0 hp' hp'0 hqlt)
    (exists_norm_rellichEmbL_eq_one hΩb hd hq0 hq)

/-- **Semilinear Dirichlet problem.** The minimiser of the Dirichlet energy on the unit
`L^q` sphere is a weak solution of `-Δu = λ|u|^{q-2}u`, with `λ = ∫ |∇u|²` the minimum itself,
which is positive. -/
theorem exists_weakSolution_dirichlet_of_lt
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p')
    (hq2 : (2 : ℝ≥0) ≤ q) :
    ∃ U : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧
      0 < laplaceBilin B1 U U ∧
      ∀ V : H01 B1, laplaceBilin B1 U V
        = laplaceBilin B1 U U
            * ∫ x, |(rellichEmbL measurableSet_ball hΩb hd hq U) x| ^ ((q : ℝ) - 2)
                * (rellichEmbL measurableSet_ball hΩb hd hq U) x
                * (rellichEmbL measurableSet_ball hΩb hd hq V) x ∂(volume.restrict B1) := by
  obtain ⟨U, hU, hmin⟩ :=
    exists_dirichlet_minimiser_of_lt hΩb hd hq hq0 hp' hp'0 hqlt
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hco : IsCoercive (laplaceBilin (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    laplaceBilin_coercive_of_bounded hΩb
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hp1 : 1 < ((q : ℝ≥0∞)).toReal := by
    rw [ENNReal.coe_toReal]
    linarith
  -- The minimum is positive: a vector on the constraint set is nonzero.
  have hUne : U ≠ 0 := by
    intro h0
    rw [h0] at hU
    simp at hU
  have hpos : 0 < laplaceBilin (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) U U := by
    obtain ⟨C, hC, hcoer⟩ := id hco
    have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hUne
    nlinarith [hcoer U, mul_pos (mul_pos hC hUpos) hUpos]
  refine ⟨U, hU, hpos, fun V => ?_⟩
  have h := euler_lagrange_of_bilin_min (p := (q : ℝ≥0∞)) (by simpa using hq0) ENNReal.coe_ne_top
    hp1 (rellichEmbL measurableSet_ball hΩb hd hq) _ (laplaceBilin_symm _)
    (bilin_self_nonneg hco) hU hmin V
  simpa using h

/-- **Semilinear Dirichlet problem written over the gradient coordinates.** The identity of
`exists_weakSolution_dirichlet_of_lt` with both sides unfolded: `∫ ∇u · ∇v = λ ∫ |u|^{q-2}uv` for
every `v ∈ H₀¹`, with `λ = ∫ |∇u|²`. -/
theorem exists_weakSolution_dirichlet_of_lt'
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p')
    (hq2 : (2 : ℝ≥0) ≤ q) :
    ∃ (U : H01 B1) (lam : ℝ), ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧ 0 < lam ∧
      lam = ∑ i : Fin d, ‖(U : H1amb B1) i.succ‖ ^ 2 ∧
      ∀ V : H01 B1, ∑ i : Fin d, ⟪(U : H1amb B1) i.succ, (V : H1amb B1) i.succ⟫
        = lam * ∫ x, |(rellichEmbL measurableSet_ball hΩb hd hq U) x| ^ ((q : ℝ) - 2)
            * (rellichEmbL measurableSet_ball hΩb hd hq U) x
            * (rellichEmbL measurableSet_ball hΩb hd hq V) x ∂(volume.restrict B1) := by
  obtain ⟨U, hU, hpos, heq⟩ :=
    exists_weakSolution_dirichlet_of_lt hΩb hd hq hq0 hp' hp'0 hqlt hq2
  refine ⟨U, laplaceBilin B1 U U, hU, hpos, laplaceBilin_self _ U, fun V => ?_⟩
  rw [← laplaceBilin_apply]
  exact heq V

end

end EllipticPdes.Embedding
