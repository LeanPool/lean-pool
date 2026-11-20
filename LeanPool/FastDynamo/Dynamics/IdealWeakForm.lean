/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate
public import LeanPool.FastDynamo.Analysis.LiteralTorusRepresentative
public import LeanPool.FastDynamo.Analysis.R3BlockComplexify

/-!
# The weak form of the ideal induction equation

**Statement layer.**  The paper (§1.2, proof of `cor:ideal-growth`) calls the ideal induction
solution group `𝒯₀` the solution group of the ideal induction equation
`∂ₜB + (u·∇)B − (B·∇)u = 0` on `L²_σ(T³)`, with solutions understood in the distributional sense
in `C([−T, T]; L²)`.  This module states that notion on the literal torus `Torus 3`:

* `literalFDeriv v` is the derivative `∇v` of a velocity, read on the canonical lift;
* `literalAdvection v φ` is `(v·∇)φ` and `literalStretch v B` is `(B·∇)v = Dv · B`;
* `literalFDeriv_literalTorusPoint`, `literalAdvection_literalTorusPoint` compute the two from
  any lift of the point;
* `IsIdealTestField` singles out the smooth periodic test fields;
* `IsIdealWeakSolution v T W` says that `W : ℝ → L²` is continuous on `[−T, T]` and satisfies,
  for every test field `φ` and all `s, t ∈ [−T, T]`,
  `⟨W t, φ⟩ − ⟨W s, φ⟩ = ∫ₛᵗ ⟨(W·∇)v, φ⟩ + ⟨W, (v·∇)φ⟩`, the time-integrated form of the paper's
  `d/dt ⟨B, φ⟩ = …`; pairings are `∫ ⟪φ, B⟫` (the paper's `∫ B · conj φ`);
* `IsIdealSolutionGroup v G` says that `G` is a group of operators on `L²_σ` all of whose orbits
  are weak solutions.

The notion differs from the paper's in these respects: the identity is tested against smooth
spatial fields and integrated in time (the equivalence with space–time test functions is not
formalised); `Div B = 0` is not part of it; the derivative `∇v` is the pointwise derivative of
the lift; the integrals are Bochner integrals.

`IsIdealInductionGroup` (`FastDynamo/Dynamics/ParticleFlow.lean`) asks `𝒯₀` to be a solution
group in this sense and the only one.  At the velocity of the paper (at every admissible parameter
tuple) the Cauchy group is a solution group by `isIdealSolutionGroup_idealGroup`
(`FastDynamo/Dynamics/Ideal/WeakSolution.lean`), and every solution group equals it by
`IsIdealSolutionGroup.eq_idealGroup` (`FastDynamo/Dynamics/Ideal/WeakSolutionUniqueness.lean`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- The derivative `∇v` of a velocity `v` on `Torus 3`, read on the canonical lift at the Ioc
representative of the point. -/
def literalFDeriv (v : Torus 3 → R3) (x : Torus 3) : R3 →L[ℝ] R3 :=
  fderiv ℝ (fun a : R3 ↦ v (literalTorusPoint a)) (literalIocRepresentative x)

/-- The advection `(v·∇)φ` of a field `φ` whose lift is differentiable. -/
def literalAdvection (v : Torus 3 → R3) (φ : Torus 3 → C3) (x : Torus 3) : C3 :=
  fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a)) (literalIocRepresentative x) (v x)

/-- The stretching `(B·∇)v = Dv · B`, pointwise. -/
def literalStretch (v : Torus 3 → R3) (B : Torus 3 → C3) (x : Torus 3) : C3 :=
  r3Complexify (literalFDeriv v x) (B x)

/-- The derivative of the lift of a function on `Torus 3` only depends on the point of the torus:
two representatives of the same point give the same Fréchet derivative. -/
theorem fderiv_literalLift_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus 3 → F) {a b : R3} (hab : literalTorusPoint a = literalTorusPoint b) :
    fderiv ℝ (fun x : R3 ↦ f (literalTorusPoint x)) a =
      fderiv ℝ (fun x : R3 ↦ f (literalTorusPoint x)) b := by
  have hv : literalTorusPoint (b - a) = 0 := by
    rw [sub_eq_add_neg, literalTorusPoint_add, literalTorusPoint_neg, hab, add_neg_cancel]
  have h1 : fderiv ℝ (fun x : R3 ↦ f (literalTorusPoint (x + (b - a)))) a =
      fderiv ℝ (fun x : R3 ↦ f (literalTorusPoint x)) (a + (b - a)) :=
    fderiv_comp_add_right (f := fun x : R3 ↦ f (literalTorusPoint x)) (x := a) (b - a)
  rw [add_sub_cancel] at h1
  rw [← h1]
  simp only [literalTorusPoint_add, hv, add_zero]

/-- `∇v` at the class of `a` is the derivative of the lift at `a`: the choice of representative
in the definition of `literalFDeriv` is immaterial. -/
theorem literalFDeriv_literalTorusPoint (v : Torus 3 → R3) (a : R3) :
    literalFDeriv v (literalTorusPoint a) =
      fderiv ℝ (fun b : R3 ↦ v (literalTorusPoint b)) a := by
  rw [literalFDeriv, fderiv_literalLift_congr v
    (literalTorusPoint_literalIocRepresentative (literalTorusPoint a))]

/-- `(v·∇)φ` at the class of `a` is the derivative of the lift of `φ` at `a` in the direction of
`v`. -/
theorem literalAdvection_literalTorusPoint (v : Torus 3 → R3) (φ : Torus 3 → C3) (a : R3) :
    literalAdvection v φ (literalTorusPoint a) =
      fderiv ℝ (fun b : R3 ↦ φ (literalTorusPoint b)) a (v (literalTorusPoint a)) := by
  rw [literalAdvection, fderiv_literalLift_congr φ
    (literalTorusPoint_literalIocRepresentative (literalTorusPoint a))]

/-- The test fields of the weak form: fields with smooth `ℤ³`-periodic lift. -/
def IsIdealTestField (φ : Torus 3 → C3) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) fun a : R3 ↦ φ (literalTorusPoint a)

/-- `W` is a distributional solution of the ideal induction equation `∂ₜB + (v·∇)B − (B·∇)v = 0`
in `C([−T, T]; L²)`: `W` is continuous on `[−T, T]` and satisfies the time-integrated weak
identity against every smooth periodic test field. -/
structure IsIdealWeakSolution (v : Torus 3 → R3) (T : ℝ) (W : ℝ → LiteralC3L2) : Prop where
  /-- `W` is continuous on `[−T, T]` with values in `L²`. -/
  continuousOn : ContinuousOn W (Set.Icc (-T) T)
  /-- The weak identity against smooth periodic test fields. -/
  weak : ∀ φ : Torus 3 → C3, IsIdealTestField φ →
    ∀ s ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T,
      (∫ x, inner ℂ (φ x) ((W t : Torus 3 → C3) x)) -
          ∫ x, inner ℂ (φ x) ((W s : Torus 3 → C3) x) =
        ∫ τ in s..t, ∫ x, (inner ℂ (φ x) (literalStretch v (W τ : Torus 3 → C3) x) +
          inner ℂ (literalAdvection v φ x) ((W τ : Torus 3 → C3) x))

/-- `G` is a solution group of the ideal induction equation on `L²_σ`: a one-parameter group of
operators on `literalSolenoidalSubspace` whose orbits are weak solutions on every `[−T, T]`. -/
structure IsIdealSolutionGroup (v : Torus 3 → R3)
    (G : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace) : Prop where
  /-- `G 0` is the identity. -/
  group_zero : G 0 = ContinuousLinearMap.id ℂ literalSolenoidalSubspace
  /-- The group law. -/
  group_add : ∀ s t : ℝ, G (s + t) = (G s).comp (G t)
  /-- Every orbit is a weak solution. -/
  weakSolution : ∀ (B : literalSolenoidalSubspace) (T : ℝ),
    IsIdealWeakSolution v T fun t ↦ ((G t B : literalSolenoidalSubspace) : LiteralC3L2)

end

end FastDynamo
