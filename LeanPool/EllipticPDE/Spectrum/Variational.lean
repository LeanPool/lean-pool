/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Spectrum.RellichDischarge
public import LeanPool.EllipticPDE.Analysis.DirectMethodForm


/-!
# Variational characterisation of the principal eigenvalue

`EllipticPdes.Sobolev.solOp_spectral` produces the Dirichlet eigenvalues from the spectral theorem
for the compact self-adjoint solution operator, one eigenvalue at a time and with no formula for
any of them. This file gives the first eigenvalue a formula: it is the infimum of the Rayleigh
quotient

`λ₁ = inf { B[U, U] : U ∈ H₀¹(Ω), ‖U‖_{L²(Ω)} = 1 }`,

the infimum is attained, and a minimiser is a weak eigenfunction at that eigenvalue. Every weak
eigenvalue of `B` is at least `λ₁`, so the name is the theorem.

The proof is the direct method in the abstract setting. Coercivity bounds a minimising sequence in
`H₀¹(Ω)`, `EllipticPdes.Analysis.exists_weakLimit` extracts a weak limit, and the Rellich compact
embedding `embL2 Ω` takes the constraint to that limit along a further subsequence. Weak lower
semicontinuity of the form is the expansion of `0 ≤ B[Uₖ - w, Uₖ - w]` together with
`B[Uₖ, w] → B[w, w]`, which needs symmetry and nothing else. The Euler-Lagrange step is a
one-variable argument: `t ↦ B[U + tV, U + tV] - λ₁‖U + tV‖²_{L²}` is a quadratic that vanishes at
`t = 0` and is nonnegative everywhere, so its linear coefficient vanishes.

`EllipticPdes.Embedding.exists_minimiser_of_lt` runs the same method at a subcritical `L^q`
constraint, where the compactness comes from `rellichEmbL_isCompact_of_lt`. The two files differ in
which compact embedding does the work and in whether the constraint is quadratic; at `q = 2` the
constraint is quadratic and the minimiser satisfies a linear equation, which is this file.

## Main declarations

* `EllipticPdes.Sobolev.principalEigenvalue`: the infimum of the Rayleigh quotient.
* `EllipticPdes.Sobolev.principalEigenvalue_mul_norm_sq_le`: `λ₁‖U‖²_{L²} ≤ B[U, U]` for every
  `U`, the Rayleigh quotient bound off the constraint set.
* `EllipticPdes.Sobolev.exists_rayleigh_minimiser`: the infimum is attained.
* `EllipticPdes.Sobolev.rayleigh_euler_lagrange`: a minimiser is a weak eigenfunction.
* `EllipticPdes.Sobolev.exists_principal_eigenpair`: the two previous statements combined.
* `EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen`: no weak eigenvalue is smaller.
* `EllipticPdes.Sobolev.dirichlet_principal_eigenpair`: the instance at `-Δ` on a bounded
  measurable domain, with the compact embedding discharged by `embL2_isCompact`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 2; Y. Guo, *Partial
Differential Equations*, Section IX.1.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-! ### The Rayleigh quotient and its infimum -/

/-- The unit `L²` sphere of `H₀¹(Ω)`, the constraint set of the Rayleigh problem. -/
def rayleighSphere (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H01 Ω) :=
  {U | ‖embL2 Ω U‖ = 1}

/-- The values a bilinear form takes on the unit `L²` sphere. -/
def rayleighValues (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) : Set ℝ :=
  (fun U => B U U) '' rayleighSphere Ω

/-- **Principal eigenvalue** of a symmetric coercive form on `H₀¹(Ω)`: the infimum of the
Rayleigh quotient `B[U, U]` over the functions of unit `L²` norm. -/
def principalEigenvalue (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) : ℝ := sInf (rayleighValues B)

/-- A coercive form is positive semidefinite. -/
lemma nonneg_of_isCoercive (hco : IsCoercive B) (U : H01 Ω) : 0 ≤ B U U :=
  bilin_self_nonneg hco U

/-- The constraint set is inhabited as soon as some element has a nonzero `L²` class: rescale. -/
lemma rayleighSphere_nonempty (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    (rayleighSphere Ω).Nonempty := by
  obtain ⟨V, hV⟩ := hne
  have hpos : 0 < ‖embL2 Ω V‖ := norm_pos_iff.mpr hV
  refine ⟨‖embL2 Ω V‖⁻¹ • V, ?_⟩
  simp only [rayleighSphere, Set.mem_ofPred_eq, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hpos.ne'

/-- Positive semidefiniteness bounds the Rayleigh values below by zero. -/
lemma rayleighValues_bddBelow (hco : IsCoercive B) : BddBelow (rayleighValues B) :=
  ⟨0, by rintro _ ⟨U, -, rfl⟩; exact nonneg_of_isCoercive hco U⟩

/-- The infimum is a lower bound on the constraint set. -/
lemma principalEigenvalue_le (hco : IsCoercive B) {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) :
    principalEigenvalue B ≤ B U U :=
  csInf_le (rayleighValues_bddBelow hco) ⟨U, hU, rfl⟩

/-- **Rayleigh bound off the constraint set**: `λ₁‖U‖²_{L²} ≤ B[U, U]` for every `U`. On the
constraint set this is the definition of the infimum, and elsewhere it follows by rescaling. -/
theorem principalEigenvalue_mul_norm_sq_le (hco : IsCoercive B) (U : H01 Ω) :
    principalEigenvalue B * ‖embL2 Ω U‖ ^ 2 ≤ B U U := by
  rcases eq_or_ne (embL2 Ω U) 0 with h0 | h0
  · rw [h0]
    simpa using nonneg_of_isCoercive hco U
  · have hpos : 0 < ‖embL2 Ω U‖ := norm_pos_iff.mpr h0
    have hsphere : ‖embL2 Ω (‖embL2 Ω U‖⁻¹ • U)‖ = 1 := by
      simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      exact inv_mul_cancel₀ hpos.ne'
    have hval : B (‖embL2 Ω U‖⁻¹ • U) (‖embL2 Ω U‖⁻¹ • U)
        = ‖embL2 Ω U‖⁻¹ * (‖embL2 Ω U‖⁻¹ * B U U) := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    have hle := principalEigenvalue_le hco hsphere
    rw [hval] at hle
    have hs2 : (0 : ℝ) < ‖embL2 Ω U‖ ^ 2 := by positivity
    calc principalEigenvalue B * ‖embL2 Ω U‖ ^ 2
        ≤ ‖embL2 Ω U‖⁻¹ * (‖embL2 Ω U‖⁻¹ * B U U) * ‖embL2 Ω U‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hs2.le
      _ = B U U := by field_simp

/-- Coercivity bounds the principal eigenvalue below by the coercivity constant: on the constraint
set `1 = ‖U‖_{L²} ≤ ‖U‖_{H₀¹}`, so `C ≤ C‖U‖² ≤ B[U, U]`. -/
lemma le_principalEigenvalue_of_coercive
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) {C : ℝ} (hC : 0 < C)
    (hcoer : ∀ U : H01 Ω, C * ‖U‖ * ‖U‖ ≤ B U U) : C ≤ principalEigenvalue B := by
  refine le_csInf ((rayleighSphere_nonempty hne).image _) ?_
  rintro _ ⟨U, hU, rfl⟩
  change C ≤ B U U
  have h1 : (1 : ℝ) ≤ ‖U‖ := hU ▸ embL2_norm_le U
  have h2 : (1 : ℝ) ≤ ‖U‖ * ‖U‖ := by nlinarith
  nlinarith [hcoer U, mul_le_mul_of_nonneg_left h2 hC.le]

/-- The principal eigenvalue of a coercive form is positive. -/
theorem principalEigenvalue_pos (hco : IsCoercive B) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    0 < principalEigenvalue B := by
  obtain ⟨C, hC, hcoer⟩ := id hco
  exact lt_of_lt_of_le hC (le_principalEigenvalue_of_coercive hne hC hcoer)

/-! ### The Euler-Lagrange equation -/

/-- A quadratic in `t` that vanishes at `t = 0` and is nonnegative everywhere has no linear
term. -/
lemma eq_zero_of_quadratic_nonneg {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a) :
    b = 0 := by
  by_contra hb
  have hb2 : 0 < b ^ 2 := by positivity
  have hεpos : (0 : ℝ) < 1 / (|a| + 1) := by positivity
  have hεa : 1 / (|a| + 1) * a < 2 := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : (0 : ℝ) < |a| + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2]
    linarith
  have hneg := h (-(1 / (|a| + 1) * b))
  nlinarith [mul_pos (mul_pos hεpos hb2) (show (0 : ℝ) < 2 - 1 / (|a| + 1) * a by linarith)]

/-- **Euler-Lagrange equation of the Rayleigh problem.** A minimiser on the unit `L²` sphere is
a weak eigenfunction at the principal eigenvalue: `B[U, V] = λ₁⟪U, V⟫_{L²}` for every `V`. -/
theorem rayleigh_euler_lagrange (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) (hmin : B U U = principalEigenvalue B) (V : H01 Ω) :
    B U V = principalEigenvalue B * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  have key : ∀ t : ℝ,
      0 ≤ 2 * t * (B U V - principalEigenvalue B * ⟪embL2 Ω U, embL2 Ω V⟫)
        + t ^ 2 * (B V V - principalEigenvalue B * ‖embL2 Ω V‖ ^ 2) := by
    intro t
    have hmain := principalEigenvalue_mul_norm_sq_le hco (U + t • V)
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

/-! ### The Rayleigh problem under a further constraint -/

/-- The values a form takes on the unit `L²` sphere inside a set `S`. -/
def rayleighValuesOn (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) (S : Set (H01 Ω)) : Set ℝ :=
  (fun U => B U U) '' (rayleighSphere Ω ∩ S)

/-- The infimum of the Rayleigh quotient over the unit `L²` sphere inside `S`. Taking `S` to be
the vectors `L²`-orthogonal to the earlier eigenfunctions gives the later eigenvalues. -/
def eigenvalueOn (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) (S : Set (H01 Ω)) : ℝ :=
  sInf (rayleighValuesOn B S)

/-- With no constraint the values are those of the whole sphere. -/
lemma rayleighValuesOn_univ : rayleighValuesOn B Set.univ = rayleighValues B := by
  rw [rayleighValuesOn, rayleighValues, Set.inter_univ]

/-- With no constraint the infimum is the principal eigenvalue. -/
lemma eigenvalueOn_univ : eigenvalueOn B Set.univ = principalEigenvalue B := by
  rw [eigenvalueOn, rayleighValuesOn_univ, principalEigenvalue]

/-- Positive semidefiniteness bounds the constrained values below by zero. -/
lemma rayleighValuesOn_bddBelow (hco : IsCoercive B) (S : Set (H01 Ω)) :
    BddBelow (rayleighValuesOn B S) :=
  ⟨0, by rintro _ ⟨U, -, rfl⟩; exact nonneg_of_isCoercive hco U⟩

/-- The constrained infimum is a lower bound on the constrained sphere. -/
lemma eigenvalueOn_le (hco : IsCoercive B) {S : Set (H01 Ω)} {U : H01 Ω}
    (hU : ‖embL2 Ω U‖ = 1) (hUS : U ∈ S) : eigenvalueOn B S ≤ B U U :=
  csInf_le (rayleighValuesOn_bddBelow hco S) ⟨U, ⟨hU, hUS⟩, rfl⟩

/-- **Tightening the constraint raises the infimum.** -/
lemma principalEigenvalue_le_eigenvalueOn (hco : IsCoercive B) {S : Set (H01 Ω)}
    (hne : (rayleighSphere Ω ∩ S).Nonempty) :
    principalEigenvalue B ≤ eigenvalueOn B S := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨U, hU, rfl⟩
  exact principalEigenvalue_le hco hU.1

/-! ### Existence of a minimiser -/

/-- **Attainment of the infimum of the Rayleigh quotient over a weakly closed set.** Coercivity
bounds a minimising sequence, weak compactness supplies a limit, the constraint `S` passes to that
limit by hypothesis, and the Rellich compact embedding takes the unit `L²` norm to it. -/
theorem exists_rayleigh_minimiser_on (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) {S : Set (H01 Ω)}
    (hSclosed : ∀ (u : ℕ → H01 Ω) (w : H01 Ω), (∀ k, u k ∈ S) →
      (∀ v : H01 Ω, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫)) → w ∈ S)
    (hne : (rayleighSphere Ω ∩ S).Nonempty) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧ U ∈ S ∧ B U U = eigenvalueOn B S := by
  obtain ⟨C, hC, hcoer⟩ := id hco
  have hbdd : BddBelow (rayleighValuesOn B S) := rayleighValuesOn_bddBelow hco S
  have hnonempty : (rayleighValuesOn B S).Nonempty := hne.image _
  -- A minimising sequence.
  have hchoice : ∀ n : ℕ, ∃ U : H01 Ω,
      (‖embL2 Ω U‖ = 1 ∧ U ∈ S) ∧ B U U < eigenvalueOn B S + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt : eigenvalueOn B S < eigenvalueOn B S + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt hnonempty hlt
    obtain ⟨U, hU, rfl⟩ := hr
    exact ⟨U, hU, hrlt⟩
  choose U hUmem hUlt using hchoice
  have hUs : ∀ n, ‖embL2 Ω (U n)‖ = 1 := fun n => (hUmem n).1
  have hUS : ∀ n, U n ∈ S := fun n => (hUmem n).2
  have hUB : ∀ n, B (U n) (U n) < eigenvalueOn B S + 1 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [hUlt n]
  set M : ℝ := Real.sqrt ((eigenvalueOn B S + 1) / C) with hMdef
  have hMbound : ∀ n, ‖U n‖ ≤ M := by
    intro n
    have h2 : ‖U n‖ ^ 2 ≤ (eigenvalueOn B S + 1) / C := by
      rw [le_div_iff₀ hC]
      nlinarith [hcoer (U n), hUB n]
    calc ‖U n‖ = Real.sqrt (‖U n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ M := Real.sqrt_le_sqrt h2
  -- Weak compactness.
  obtain ⟨w, φ, hφ, hweak⟩ := exists_weakLimit (u := U) hMbound
  have hweakL2 : ∀ g : L2D Ω,
      Tendsto (fun k => ⟪embL2 Ω (U (φ k)), g⟫) atTop (𝓝 ⟪embL2 Ω w, g⟫) := by
    intro g
    simpa only [ContinuousLinearMap.adjoint_inner_right] using hweak ((embL2 Ω).adjoint g)
  -- Rellich gives a further subsequence converging strongly in `L²`.
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hcptL : IsCompactOperator ((embL2 Ω).toLinearMap) := hRellich
  have hcl :=
    (isCompactOperator_iff_isCompact_closure_image_closedBall (embL2 Ω).toLinearMap hM1).mp hcptL
  have hmemcl : ∀ k, embL2 Ω (U (φ k))
      ∈ closure (⇑(embL2 Ω).toLinearMap '' Metric.closedBall (0 : H01 Ω) (M + 1)) :=
    fun k => subset_closure ⟨U (φ k), by
      simpa [Metric.mem_closedBall, dist_zero_right] using (hMbound (φ k)).trans (by linarith), rfl⟩
  obtain ⟨z, -, ψ, hψ, hψtend⟩ := hcl.tendsto_subseq hmemcl
  -- The strong limit is the `L²` class of the weak limit.
  have hzw : z = embL2 Ω w := by
    refine ext_inner_right ℝ (fun g => ?_)
    have hstrong : Tendsto (fun j => ⟪embL2 Ω (U (φ (ψ j))), g⟫) atTop (𝓝 ⟪z, g⟫) := by
      simpa [Function.comp_def] using hψtend.inner (tendsto_const_nhds (x := g))
    exact tendsto_nhds_unique hstrong ((hweakL2 g).comp hψ.tendsto_atTop)
  have hwnorm : ‖embL2 Ω w‖ = 1 := by
    have h1 : Tendsto (fun j => ‖embL2 Ω (U (φ (ψ j)))‖) atTop (𝓝 ‖z‖) := by
      simpa [Function.comp_def] using (continuous_norm.tendsto z).comp hψtend
    have h2 : Tendsto (fun j => ‖embL2 Ω (U (φ (ψ j)))‖) atTop (𝓝 1) := by
      simp only [hUs]
      exact tendsto_const_nhds
    rw [← hzw]
    exact tendsto_nhds_unique h1 h2
  have hwS : w ∈ S := hSclosed (fun k => U (φ k)) w (fun k => hUS (φ k)) hweak
  -- Weak lower semicontinuity of the form.
  have hBUU : Tendsto (fun n => B (U n) (U n)) atTop (𝓝 (eigenvalueOn B S)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => eigenvalueOn B S)
      (h := fun n => eigenvalueOn B S + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_
      (fun n => csInf_le hbdd ⟨U n, hUmem n, rfl⟩) (fun n => (hUlt n).le)
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum : Tendsto (fun n : ℕ => eigenvalueOn B S + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (eigenvalueOn B S + 0)) := tendsto_const_nhds.add hzero
    rwa [add_zero] at hsum
  have hlsc : B w w ≤ eigenvalueOn B S := by
    refine bilin_le_of_weakLimit hco hsymm hweak ?_
    simpa [Function.comp_def] using hBUU.comp hφ.tendsto_atTop
  exact ⟨w, hwnorm, hwS, le_antisymm hlsc (eigenvalueOn_le hco hwnorm hwS)⟩

/-- **Attainment of the infimum of the Rayleigh quotient.** The unconstrained case. -/
theorem exists_rayleigh_minimiser (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧ B U U = principalEigenvalue B := by
  have hne' : (rayleighSphere Ω ∩ Set.univ).Nonempty := by
    simpa using rayleighSphere_nonempty hne
  obtain ⟨U, hU, -, hmin⟩ :=
    exists_rayleigh_minimiser_on hco hsymm hRellich (S := Set.univ)
      (fun _ _ _ _ => Set.mem_univ _) hne'
  exact ⟨U, hU, by rwa [eigenvalueOn_univ] at hmin⟩

/-- **Principal eigenpair.** For a symmetric coercive form with the Rellich compact embedding
there is a `U` of unit `L²` norm attaining the infimum of the Rayleigh quotient, and it solves the
weak eigenvalue problem at that value. -/
theorem exists_principal_eigenpair (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧ B U U = principalEigenvalue B ∧
      ∀ V : H01 Ω, B U V = principalEigenvalue B * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  obtain ⟨U, hU, hmin⟩ := exists_rayleigh_minimiser hco hsymm hRellich hne
  exact ⟨U, hU, hmin, fun V => rayleigh_euler_lagrange hco hsymm hU hmin V⟩

/-- **Minimality of the principal eigenvalue.** Any nonzero weak eigenfunction has eigenvalue
at least `λ₁`. Coercivity rules out a nonzero element with vanishing `L²` class, so the Rayleigh
bound applies. -/
theorem principalEigenvalue_le_of_weak_eigen (hco : IsCoercive B) {lam : ℝ} {U : H01 Ω}
    (hU : U ≠ 0) (heig : ∀ V : H01 Ω, B U V = lam * ⟪embL2 Ω U, embL2 Ω V⟫) :
    principalEigenvalue B ≤ lam := by
  have hUU : B U U = lam * ‖embL2 Ω U‖ ^ 2 := by
    rw [heig U, real_inner_self_eq_norm_sq]
  have hnz : embL2 Ω U ≠ 0 := by
    intro h0
    obtain ⟨C, hC, hcoer⟩ := id hco
    have hzero : B U U = 0 := by rw [hUU, h0]; simp
    have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
    nlinarith [hcoer U, mul_pos (mul_pos hC hUpos) hUpos]
  have hpos : 0 < ‖embL2 Ω U‖ ^ 2 := by
    have := norm_pos_iff.mpr hnz
    positivity
  have hkey := principalEigenvalue_mul_norm_sq_le hco U
  rw [hUU] at hkey
  exact le_of_mul_le_mul_right hkey hpos

/-! ### The Dirichlet Laplacian on a bounded measurable domain -/

/-- **Principal Dirichlet eigenvalue of `-Δ`** on a bounded measurable domain, with the compact
embedding discharged by `embL2_isCompact`. The eigenvalue of `-Δ` itself is `λ₁ - 1`, since the
graph norm on `H₀¹(Ω)` includes the function coordinate: the identity below reads
`∫ ∇u · ∇v = (λ₁ - 1) ∫ u v` once `⟪U, V⟫_{H₀¹}` is split off. -/
theorem dirichlet_principal_eigenpair (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧
      laplaceBilin Ω U U = principalEigenvalue (laplaceBilin Ω) ∧
      ∀ V : H01 Ω, laplaceBilin Ω U V
        = principalEigenvalue (laplaceBilin Ω) * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  exists_principal_eigenpair (laplaceBilin_coercive Ω CP hCP hbase) (laplaceBilin_symm Ω)
    (embL2_isCompact hΩm hΩb) hne

/-- **Poincaré inequality with its optimal constant.** The principal Dirichlet eigenvalue is
the largest constant for which `λ‖u‖²_{L²} ≤ ∫ |∇u|²` on all of `H₀¹(Ω)`, since
`dirichlet_poincare_attained` produces an equality case. -/
theorem dirichlet_poincare_sharp (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (U : H01 Ω) :
    principalEigenvalue (laplaceBilin Ω) * ‖(U : H1amb Ω) 0‖ ^ 2
      ≤ ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 := by
  simpa [laplaceBilin_self] using
    principalEigenvalue_mul_norm_sq_le (laplaceBilin_coercive Ω CP hCP hbase) U

/-- The optimal Poincaré constant is attained: some `u` of unit `L²` norm has Dirichlet energy
exactly `λ₁`. -/
theorem dirichlet_poincare_attained (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖(U : H1amb Ω) 0‖ = 1 ∧
      ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 = principalEigenvalue (laplaceBilin Ω) := by
  obtain ⟨U, hU, hmin⟩ := exists_rayleigh_minimiser (laplaceBilin_coercive Ω CP hCP hbase)
    (laplaceBilin_symm Ω) (embL2_isCompact hΩm hΩb) hne
  exact ⟨U, by simpa using hU, by simpa [laplaceBilin_self] using hmin⟩

/-- The principal Dirichlet eigenvalue is positive. -/
theorem dirichlet_principalEigenvalue_pos (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ)
    (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    0 < principalEigenvalue (laplaceBilin Ω) :=
  principalEigenvalue_pos (laplaceBilin_coercive Ω CP hCP hbase) hne

/-- **Principal Dirichlet eigenpair on a bounded domain**, with no abstract Poincaré
hypothesis: `EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded` names the constant, so
boundedness and measurability of `Ω` are the whole input. This is the statement Evans makes, and
it includes the positivity of `λ₁`. -/
theorem dirichlet_principal_eigenpair_of_bounded {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧
      laplaceBilin Ω U U = principalEigenvalue (laplaceBilin Ω) ∧
      0 < principalEigenvalue (laplaceBilin Ω) ∧
      ∀ V : H01 Ω, laplaceBilin Ω U V
        = principalEigenvalue (laplaceBilin Ω) * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  have hco := EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded hΩb
  obtain ⟨U, hU, hmin, heq⟩ :=
    exists_principal_eigenpair hco (laplaceBilin_symm Ω) (embL2_isCompact hΩm hΩb) hne
  exact ⟨U, hU, hmin, principalEigenvalue_pos hco hne, heq⟩

end EllipticPdes.Sobolev
