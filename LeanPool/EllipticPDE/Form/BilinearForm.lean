/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Poincare.Density
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram


/-!
# Divergence-form bilinear form (dependency-chain step 5)

We treat the symmetric, transport-free, zeroth-order-free case first: the bilinear
form of the Laplacian, `B[U, V] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫_{L²}`, i.e. the coefficient matrix is
the identity and `c = 0`. In the graph encoding of `Sobolev/Basic.lean` the `i`-th weak
partial of `U ∈ H₀¹(Ω)` is the coordinate `U (i.succ)`, so

  `B[U, V] = ∑ i, ⟪(↑U) i.succ, (↑V) i.succ⟫`.

* **Continuity** (`β = d`): each coordinate norm is bounded by the ambient `H¹` norm.
* **Coercivity** (`α = 1 / (C_P + 1)`): `B[U, U] = ∑ᵢ ‖∂ᵢu‖²` is the Dirichlet energy,
  and the density Poincaré inequality `poincare_H01` controls the function part `‖u‖²`
  by that energy, so `B` dominates the full `H¹` norm.

This is the `γ = 0` case of the coercivity examples closing Evans §6.2.2: coercivity is
immediate from the energy identity plus Poincaré, with no Gårding absorption. It is
exactly the hypothesis the
Lax-Milgram theorem (M6) consumes. The general elliptic matrix `A` and `c ≥ 0` follow the
same shape with `A`'s ellipticity constant in place of `1` (cf. DeGiorgi
`WeakFormulation/CoefficientOperator.lean`).
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

open EllipticPdes.Sobolev EllipticPdes.Poincare

variable {d : ℕ}

/-- The bilinear form of the Laplacian as a bare bilinear map on `H₀¹(Ω)`:
`B[U, V] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫_{L²}`. -/
def laplaceBilinₗ (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →ₗ[ℝ] (H01 Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun U V => ∑ i : Fin d, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_left,
          Finset.sum_add_distrib])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_left,
          smul_eq_mul, Finset.mul_sum])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_right,
          Finset.sum_add_distrib])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_right,
          smul_eq_mul, Finset.mul_sum])

/-- The bilinear form of the Laplacian on `H₀¹(Ω)` as a bounded (continuous) bilinear form,
with operator-norm bound `d`. -/
def laplaceBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (laplaceBilinₗ Ω).mkContinuous₂ (d : ℝ) (by
    intro U V
    simp only [laplaceBilinₗ, LinearMap.mk₂_apply]
    calc ‖∑ i : Fin d, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫‖
        ≤ ∑ i : Fin d, ‖⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ * ‖(V : H1amb Ω) i.succ‖ :=
          Finset.sum_le_sum (fun i _ => norm_inner_le_norm _ _)
      _ ≤ ∑ _i : Fin d, ‖U‖ * ‖V‖ :=
          Finset.sum_le_sum (fun i _ => by
            gcongr
            · exact PiLp.norm_apply_le _ _
            · exact PiLp.norm_apply_le _ _)
      _ = (d : ℝ) * ‖U‖ * ‖V‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc])

/-- Simp lemma: `laplaceBilin Ω U V = ∑ i, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫`. -/
@[simp] lemma laplaceBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    laplaceBilin Ω U V = ∑ i : Fin d, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫ := by
  simp only [laplaceBilin, LinearMap.mkContinuous₂_apply, laplaceBilinₗ, LinearMap.mk₂_apply]

/-- The Dirichlet energy identity: `B[U, U] = ∑ᵢ ‖∂ᵢu‖²`. -/
lemma laplaceBilin_self (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    laplaceBilin Ω U U = ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 := by
  rw [laplaceBilin_apply]
  exact Finset.sum_congr rfl (fun i _ => real_inner_self_eq_norm_sq _)

/-- **Quantitative coercivity of the bilinear form of the Laplacian.** Given the
test-function Poincaré bound with constant `C_P ≥ 0`, that form dominates the full
`H¹` norm with the explicit constant `1 / (C_P + 1)`: the density Poincaré
inequality controls the function part by the Dirichlet energy. This is the constant-level form of
[`laplaceBilin_coercive`]; the explicit constant feeds the Lax-Milgram a-priori
estimate [`norm_weak_solution_le`]. -/
theorem laplaceBilin_coercive_const (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (U : H01 Ω) :
    1 / (CP + 1) * ‖U‖ * ‖U‖ ≤ laplaceBilin Ω U U := by
  have hpos : (0 : ℝ) < CP + 1 := by linarith
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  -- The Dirichlet energy is `S`.
  have hBUU : laplaceBilin Ω U U = S := laplaceBilin_self Ω U
  -- The full `H¹` norm splits into function part plus `S`.
  have hnorm : ‖U‖ ^ 2 = ‖(U : H1amb Ω) 0‖ ^ 2 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  -- Density Poincaré controls the function part by the energy.
  have hpoin : ‖(U : H1amb Ω) 0‖ ^ 2 ≤ CP * S :=
    poincare_H01 CP hbase U.2
  -- Hence `‖U‖² ≤ (C_P + 1) · S`, i.e. `(1 / (C_P + 1)) ‖U‖² ≤ B[U, U]`.
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * S := by
    have : ‖U‖ ^ 2 ≤ (CP + 1) * S := by rw [hnorm]; nlinarith [hpoin]
    nlinarith [this]
  rw [hBUU, mul_assoc]
  calc 1 / (CP + 1) * (‖U‖ * ‖U‖)
      ≤ 1 / (CP + 1) * ((CP + 1) * S) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = S := by rw [← mul_assoc, one_div_mul_cancel hpos.ne', one_mul]

/-- **Coercivity of the bilinear form of the Laplacian.** Given the test-function
Poincaré bound with constant `C_P ≥ 0`, that form is coercive on `H₀¹(Ω)` with constant
`1 / (C_P + 1)`: the density Poincaré inequality controls the function part by the
Dirichlet energy, so `B[U, U]` dominates the full `H¹` norm. -/
theorem laplaceBilin_coercive (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    IsCoercive (laplaceBilin Ω) :=
  ⟨1 / (CP + 1), by positivity, laplaceBilin_coercive_const Ω CP hCP hbase⟩

/-! ### Lax-Milgram -/

/-- **Lax-Milgram Theorem.** If `(H, (·, ·))` is a Hilbert space and `B : H × H → ℝ` is a
bounded coercive (i.e. `B(u, u) ≥ β‖u‖²_H`) bilinear form, and `f` is a continuous linear
functional on `H`, then there is a unique `u ∈ H` such that `B(u, v) = ⟪f, v⟫` for all
`v ∈ H`.

Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VII.3.1,
p. 49. The two hypotheses are boundedness and coercivity, and `B` is otherwise
arbitrary, which is Remark VII.3.2 there.

Boundedness is the continuity the type `H →L[ℝ] H →L[ℝ] ℝ` states, and coercivity is
`IsCoercive`. Mathlib's `IsCoercive.continuousLinearEquivOfBilin` supplies the equivalence
`B♯` with `⟪B♯ u, v⟫ = B[u, v]`; the step taken here is from that equivalence to solvability
against a functional, by Riesz representation of `f`. -/
theorem lax_milgram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B) (f : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v : H, B u v = f v := by
  set g : H := (InnerProductSpace.toDual ℝ H).symm f with hg
  have hgrep : ∀ w : H, ⟪g, w⟫ = f w := fun w => InnerProductSpace.toDual_symm_apply
  refine ⟨hB.continuousLinearEquivOfBilin.symm g, ?_, ?_⟩
  · -- existence: `B[T⁻¹g, v] = ⟪T T⁻¹ g, v⟫ = ⟪g, v⟫ = f v`.
    intro v
    rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hgrep]
  · -- uniqueness: any solution `u` has `⟪T u, w⟫ = f w = ⟪g, w⟫`, so `T u = g`.
    intro u hu
    apply hB.continuousLinearEquivOfBilin.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    refine ext_inner_right (𝕜 := ℝ) (fun w => ?_)
    rw [hB.continuousLinearEquivOfBilin_apply, hu w, ← hgrep w]

/-! ### Lax-Milgram a-priori estimate -/

/-- **Lax-Milgram a-priori estimate.** If the bilinear form `B` satisfies the
quantitative coercivity bound `α ‖U‖² ≤ B[U, U]` with `α > 0`, then any weak solution
`u` of `B[u, v] = f v` obeys `‖u‖ ≤ α⁻¹ ‖f‖`: coercivity gives
`α ‖u‖² ≤ B[u, u] = f u ≤ ‖f‖ ‖u‖`, and dividing by `‖u‖` gives the bound. This is the
Hilbert-space a-priori estimate underlying the Lax-Milgram theorem (Evans §6.2.1,
Theorem 1, step 3): `β ‖u‖ ≤ ‖Au‖`. -/
theorem norm_weak_solution_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {B : H →L[ℝ] H →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    (hcoer : ∀ U : H, α * ‖U‖ * ‖U‖ ≤ B U U)
    {f : H →L[ℝ] ℝ} {u : H} (hu : ∀ v : H, B u v = f v) :
    ‖u‖ ≤ α⁻¹ * ‖f‖ := by
  rcases eq_or_lt_of_le (norm_nonneg u) with h0 | h0
  · rw [← h0]
    positivity
  · have h1 : α * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ :=
      calc α * ‖u‖ * ‖u‖ ≤ B u u := hcoer u
        _ = f u := hu u
        _ ≤ ‖f u‖ := Real.le_norm_self _
        _ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
    have h2 : α * ‖u‖ ≤ ‖f‖ := le_of_mul_le_mul_right h1 h0
    rw [inv_mul_eq_div, le_div_iff₀ hα]
    linarith

/-! ### `L²` right-hand sides as functionals on `H₀¹` -/

/-- A right-hand side `f ∈ L²(Ω)` as a continuous linear functional on `H₀¹(Ω)`:
`v ↦ ⟪f, v₀⟫_{L²}`, the weak pairing `⟨f, v⟩ = ∫_Ω f · v₀`. This is the embedding
`L²(Ω) ⊆ H⁻¹(Ω)` (Evans §5.9.1, Theorem 1(iii)) through which the classical Dirichlet
problem
`Lu = f`, `f ∈ L²(Ω)`, enters the abstract Lax-Milgram statement. -/
def l2Functional (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : L2D Ω) : (H01 Ω) →L[ℝ] ℝ :=
  ((innerSL ℝ f).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) (0 : Fin (d + 1)))).comp
    (H01 Ω).subtypeL

/-- Simp lemma: `l2Functional Ω f V = ⟪f, (V : H1amb Ω) 0⟫`. -/
@[simp] lemma l2Functional_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : L2D Ω)
    (V : H01 Ω) : l2Functional Ω f V = ⟪f, (V : H1amb Ω) 0⟫ := rfl

/-- The `L²` pairing is the integral `⟨f, v⟩ = ∫_Ω f · v₀`. -/
lemma l2Functional_eq_integral (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : L2D Ω)
    (V : H01 Ω) :
    l2Functional Ω f V = ∫ x in Ω, (f x : ℝ) * ((V : H1amb Ω) 0 x : ℝ) := by
  rw [l2Functional_apply, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => Real.inner_apply _ _)

/-- The embedding `L²(Ω) ⊆ H⁻¹(Ω)` is a contraction: `‖⟨f, ·⟩‖_{H⁻¹} ≤ ‖f‖_{L²}`,
since `‖v₀‖_{L²} ≤ ‖V‖_{H¹}` in the graph encoding. -/
lemma norm_l2Functional_le (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : L2D Ω) :
    ‖l2Functional Ω f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (fun V => ?_)
  rw [l2Functional_apply]
  calc ‖⟪f, (V : H1amb Ω) 0⟫‖ ≤ ‖f‖ * ‖(V : H1amb Ω) 0‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖V‖ := by
        gcongr
        exact PiLp.norm_apply_le _ _

end EllipticPdes
