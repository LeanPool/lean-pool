/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Spectrum.Variational


/-!
# Later eigenvalues by constrained minimisation

`EllipticPdes.Sobolev.exists_principal_eigenpair` names the first Dirichlet eigenvalue as the
infimum of the Rayleigh quotient over the unit `L²` sphere. Minimising over the part of that
sphere `L²`-orthogonal to a finite family of eigenfunctions names the next one, and repeating the
step names them all. This file supplies the step.

Two things have to be checked. The constraint is weakly closed, so
`EllipticPdes.Sobolev.exists_rayleigh_minimiser_on` applies to it and the minimum is attained;
and the minimiser is a weak eigenfunction of the whole space rather than only of the constrained
subspace. The second is where the multipliers drop out: a test vector splits as an admissible part
plus a combination of the `wᵢ`, and both `B[U, wᵢ]` and `⟪U, wᵢ⟫_{L²}` vanish, the first because
`wᵢ` is an eigenfunction and `U` is orthogonal to it, the second by the constraint itself.

## Main declarations

* `EllipticPdes.Sobolev.orthSubmodule`: the vectors `L²`-orthogonal to a finite family.
* `EllipticPdes.Sobolev.orthSubmodule_weaklyClosed`: the constraint passes to weak limits.
* `EllipticPdes.Sobolev.rayleigh_euler_lagrange_on`: the equation inside a submodule.
* `EllipticPdes.Sobolev.euler_lagrange_of_orthogonal_eigen`: the equation on the whole space.
* `EllipticPdes.Sobolev.exists_higher_eigenpair`: the constrained eigenpair, with its eigenvalue
  at least the principal one.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 1; Y. Guo, *Partial
Differential Equations*, Section IX.1.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-! ### The orthogonality constraint -/

/-- The vectors of `H₀¹(Ω)` whose `L²` classes are orthogonal to those of a finite family. -/
def orthSubmodule {n : ℕ} (w : Fin n → H01 Ω) : Submodule ℝ (H01 Ω) where
  carrier := {U | ∀ i, ⟪embL2 Ω U, embL2 Ω (w i)⟫ = 0}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro a b ha hb i
    rw [map_add, inner_add_left, ha i, hb i, add_zero]
  smul_mem' := by
    intro c a ha i
    rw [map_smul, real_inner_smul_left, ha i, mul_zero]

@[simp] lemma mem_orthSubmodule {n : ℕ} {w : Fin n → H01 Ω} {U : H01 Ω} :
    U ∈ orthSubmodule w ↔ ∀ i, ⟪embL2 Ω U, embL2 Ω (w i)⟫ = 0 := Iff.rfl

/-- **Passage of the orthogonality constraint to weak limits.** Testing the weak convergence against
the adjoint image of each `wᵢ` turns it into convergence of the `L²` inner products. -/
lemma orthSubmodule_weaklyClosed {n : ℕ} (w : Fin n → H01 Ω) (u : ℕ → H01 Ω) (z : H01 Ω)
    (hu : ∀ k, u k ∈ orthSubmodule w)
    (hz : ∀ v : H01 Ω, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪z, v⟫)) :
    z ∈ orthSubmodule w := by
  intro i
  have hL2 : Tendsto (fun k => ⟪embL2 Ω (u k), embL2 Ω (w i)⟫) atTop
      (𝓝 ⟪embL2 Ω z, embL2 Ω (w i)⟫) := by
    simpa only [ContinuousLinearMap.adjoint_inner_right] using
      hz ((embL2 Ω).adjoint (embL2 Ω (w i)))
  have hconst : Tendsto (fun k => ⟪embL2 Ω (u k), embL2 Ω (w i)⟫) atTop (𝓝 0) := by
    simp only [fun k => hu k i]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hL2 hconst)

/-! ### The Rayleigh bound and the equation inside a submodule -/

/-- **Rayleigh bound inside a submodule.** Rescaling stays in the submodule, so the bound of
`principalEigenvalue_mul_norm_sq_le` runs there unchanged. -/
theorem eigenvalueOn_mul_norm_sq_le (hco : IsCoercive B) (K : Submodule ℝ (H01 Ω)) {U : H01 Ω}
    (hUK : U ∈ K) :
    eigenvalueOn B (K : Set (H01 Ω)) * ‖embL2 Ω U‖ ^ 2 ≤ B U U := by
  rcases eq_or_ne (embL2 Ω U) 0 with h0 | h0
  · rw [h0]
    simpa using nonneg_of_isCoercive hco U
  · have hpos : 0 < ‖embL2 Ω U‖ := norm_pos_iff.mpr h0
    have hsphere : ‖embL2 Ω (‖embL2 Ω U‖⁻¹ • U)‖ = 1 := by
      simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      exact inv_mul_cancel₀ hpos.ne'
    have hmemK : (‖embL2 Ω U‖⁻¹ • U) ∈ (K : Set (H01 Ω)) := K.smul_mem _ hUK
    have hval : B (‖embL2 Ω U‖⁻¹ • U) (‖embL2 Ω U‖⁻¹ • U)
        = ‖embL2 Ω U‖⁻¹ * (‖embL2 Ω U‖⁻¹ * B U U) := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    have hle := eigenvalueOn_le hco hsphere hmemK
    rw [hval] at hle
    have hs2 : (0 : ℝ) < ‖embL2 Ω U‖ ^ 2 := by positivity
    calc eigenvalueOn B (K : Set (H01 Ω)) * ‖embL2 Ω U‖ ^ 2
        ≤ ‖embL2 Ω U‖⁻¹ * (‖embL2 Ω U‖⁻¹ * B U U) * ‖embL2 Ω U‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hs2.le
      _ = B U U := by field_simp

/-- **Euler-Lagrange equation inside a submodule.** A minimiser over the unit `L²` sphere of
`K` satisfies the eigenvalue identity against every test vector of `K`. -/
theorem rayleigh_euler_lagrange_on (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (K : Submodule ℝ (H01 Ω)) {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) (hUK : U ∈ K)
    (hmin : B U U = eigenvalueOn B (K : Set (H01 Ω))) {V : H01 Ω} (hVK : V ∈ K) :
    B U V = eigenvalueOn B (K : Set (H01 Ω)) * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  let lam := eigenvalueOn B (K : Set (H01 Ω))
  have hlamdef : lam = eigenvalueOn B (K : Set (H01 Ω)) := rfl
  have key : ∀ t : ℝ,
      0 ≤ 2 * t * (B U V - lam * ⟪embL2 Ω U, embL2 Ω V⟫)
        + t ^ 2 * (B V V - lam * ‖embL2 Ω V‖ ^ 2) := by
    intro t
    have hmemK : U + t • V ∈ K := K.add_mem hUK (K.smul_mem _ hVK)
    have hmain := eigenvalueOn_mul_norm_sq_le hco K hmemK
    have hBexp : B (U + t • V) (U + t • V) = B U U + 2 * t * B U V + t ^ 2 * B V V := by
      have h1 : B (U + t • V) = B U + t • B V := by rw [map_add, map_smul]
      rw [h1]
      simp only [_root_.add_apply, _root_.smul_apply, map_add, map_smul,
        smul_eq_mul]
      rw [hsymm V U]
      ring
    have hNexp : ‖embL2 Ω (U + t • V)‖ ^ 2
        = ‖embL2 Ω U‖ ^ 2 + 2 * t * ⟪embL2 Ω U, embL2 Ω V⟫ + t ^ 2 * ‖embL2 Ω V‖ ^ 2 := by
      have h1 : embL2 Ω (U + t • V) = embL2 Ω U + t • embL2 Ω V := by
        rw [map_add, map_smul]
      rw [h1, ← real_inner_self_eq_norm_sq, real_inner_add_add_self, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      ring
    rw [hBexp, hNexp, hmin, hU] at hmain
    nlinarith [hmain]
  have hb := eq_zero_of_quadratic_nonneg key
  linarith

/-! ### The equation on the whole space -/

/-- **Constrained minimiser as a weak eigenfunction of the whole space.** Split a test vector
into its admissible part and a combination of the `wᵢ`; the second half contributes nothing to
either side. `B[U, wᵢ]` vanishes because `wᵢ` is an eigenfunction and `U` is orthogonal to it, and
`⟪U, wᵢ⟫_{L²}` vanishes by the constraint. -/
theorem euler_lagrange_of_orthogonal_eigen (hco : IsCoercive B)
    (hsymm : ∀ U V : H01 Ω, B U V = B V U) {n : ℕ} {w : Fin n → H01 Ω} {lam : Fin n → ℝ}
    (hwnorm : ∀ i, ‖embL2 Ω (w i)‖ = 1)
    (hworth : ∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0)
    (hweig : ∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫)
    {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) (hUK : U ∈ orthSubmodule w)
    (hmin : B U U = eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω)))
    (V : H01 Ω) :
    B U V
      = eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω))
        * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  let K : Submodule ℝ (H01 Ω) := orthSubmodule w
  have hKdef : K = orthSubmodule w := rfl
  let lamK := eigenvalueOn B (K : Set (H01 Ω))
  have hlamK : lamK = eigenvalueOn B (K : Set (H01 Ω)) := rfl
  let c : Fin n → ℝ := fun i => ⟪embL2 Ω V, embL2 Ω (w i)⟫
  have hcdef : c = fun i => ⟪embL2 Ω V, embL2 Ω (w i)⟫ := rfl
  let V' : H01 Ω := V - ∑ i, c i • w i
  have hV'def : V' = V - ∑ i, c i • w i := rfl
  -- The `L²` class of the correction.
  have hsum : embL2 Ω (∑ i, c i • w i) = ∑ i, c i • embL2 Ω (w i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  have hdiag : ∀ i, ⟪embL2 Ω (w i), embL2 Ω (w i)⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hwnorm i, one_pow]
  -- The admissible part.
  have hV'K : V' ∈ K := by
    intro j
    rw [hV'def, map_sub, inner_sub_left, hsum, sum_inner]
    have hpick : ∑ i, ⟪c i • embL2 Ω (w i), embL2 Ω (w j)⟫ = c j := by
      rw [Finset.sum_eq_single j]
      · rw [real_inner_smul_left, hdiag j, mul_one]
      · intro i _ hij
        rw [real_inner_smul_left, hworth i j hij, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hpick, hcdef]
    simp
  -- The correction pairs to zero on both sides.
  have hBzero : ∀ i, B U (w i) = 0 := by
    intro i
    rw [hsymm U (w i), hweig i U, real_inner_comm, hUK i, mul_zero]
  have hIzero : ∀ i, ⟪embL2 Ω U, embL2 Ω (w i)⟫ = 0 := hUK
  have hBsplit : B U V = B U V' := by
    have h1 : B U (∑ i, c i • w i) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [map_smul, smul_eq_mul, hBzero i, mul_zero]
    rw [hV'def, map_sub, h1, sub_zero]
  have hIsplit : ⟪embL2 Ω U, embL2 Ω V⟫ = ⟪embL2 Ω U, embL2 Ω V'⟫ := by
    have h1 : ⟪embL2 Ω U, embL2 Ω (∑ i, c i • w i)⟫ = 0 := by
      rw [hsum, inner_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [real_inner_smul_right, hIzero i, mul_zero]
    rw [hV'def, map_sub, inner_sub_right, h1, sub_zero]
  rw [hBsplit, hIsplit]
  exact rayleigh_euler_lagrange_on hco hsymm K hU hUK hmin hV'K

/-! ### The constrained eigenpair -/

/-- **Later eigenpair.** Minimising over the part of the unit `L²` sphere orthogonal to a
finite orthonormal family of eigenfunctions produces another eigenpair, whose eigenvalue is at
least the principal one. Iterating the step produces the whole sequence. -/
theorem exists_higher_eigenpair (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) {n : ℕ} {w : Fin n → H01 Ω} {lam : Fin n → ℝ}
    (hwnorm : ∀ i, ‖embL2 Ω (w i)‖ = 1)
    (hworth : ∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0)
    (hweig : ∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫)
    (hne : (rayleighSphere Ω ∩ (orthSubmodule w : Set (H01 Ω))).Nonempty) :
    ∃ (U : H01 Ω) (μ : ℝ), ‖embL2 Ω U‖ = 1 ∧ U ∈ orthSubmodule w ∧ B U U = μ ∧
      principalEigenvalue B ≤ μ ∧
      ∀ V : H01 Ω, B U V = μ * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  obtain ⟨U, hU, hUK, hmin⟩ :=
    exists_rayleigh_minimiser_on hco hsymm hRellich (orthSubmodule_weaklyClosed w) hne
  refine ⟨U, eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω)), hU, hUK,
    hmin, principalEigenvalue_le_eigenvalueOn hco hne, fun V => ?_⟩
  exact euler_lagrange_of_orthogonal_eigen hco hsymm hwnorm hworth hweig hU hUK hmin V

end EllipticPdes.Sobolev
