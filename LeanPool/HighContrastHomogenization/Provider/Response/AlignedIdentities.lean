/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.EnergyMap
public import LeanPool.HighContrastHomogenization.Provider.Response.AdjointCongruence
public import LeanPool.HighContrastHomogenization.Provider.Response.CoefficientBridge

/-!
# High-contrast homogenization: Provider.Response.AlignedIdentities

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The variational identities on the aligned subdivision

The identities of `HCPoly.Provider.Response.VariationalIdentities` and
`HCPoly.Provider.Response.EnergyMap` are stated over an arbitrary Chapter 2 domain.  This
file supplies the two structural steps that the weak-norm estimate for the
optimizer state performs on the aligned subdivision itself, and then reads every
identity on the adapted parent cell `U_t = q□_t` and its aligned children
`U_k(z) = z + q□_k`, with the paper's blocks `A_t = 𝐀(U_t;a)` and
`A_k(z) = 𝐀(U_k(z);a)` in place of the Chapter 2 coarse block matrix.

The two structural steps are:

* **restriction** — *"the primal and adjoint solutions representing `Y` remain
  solutions after restriction to every `U_k(z)`"*, and *"the parent optimizer
  restricts to an admissible solution on every child: its equation holds against
  test functions supported in that child"*;
* **membership** — the doubled state `X = (∇v, a∇v)` of a solution lies in the
  response space `𝒮(V;a)`, and so does the difference `X_t - X(U_k(z))` of two
  such states, because the difference of two `a`-harmonic functions is
  `a`-harmonic.

Both are stated with the pointwise ellipticity of the representative as a
hypothesis; that is exactly what the coefficient bridge
`Response.exists_coeffOn_family` produces for a sample of the law, simultaneously on
the parent and on every aligned cell.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ} {q : Mat d}

/-! ## Solutions restrict to subdomains -/

/-- The weak flux of a solution pairs integrably with every test gradient, on a
domain carrying a pointwise elliptic representative. -/
theorem weakFluxIntegrable_of_isEllipticFieldOn {U : Domain d} {lam Lam : ℝ}
    {a : CoeffOn U} (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a) :
    weakFluxIntegrable (U : Set (Vec d)) a.toCoeffField u := fun φ =>
  integrableOn_vecDot_of_memVectorL2
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2)
    φ.toH1Function.grad_memVectorL2

/-- **The parent solution restricts to a subdomain**: its equation holds
against every test function supported in the subdomain, so its
gradient is again an admissible solution gradient there. -/
theorem exists_restrict_solution {U V : Domain d} {lam Lam : ℝ}
    {b : CoeffOn U} {c : CoeffOn V} (hrep : c.toCoeffField = b.toCoeffField)
    (hVU : (V : Set (Vec d)) ⊆ (U : Set (Vec d)))
    (hEll : IsEllipticFieldOn lam Lam (V : Set (Vec d)) c.toCoeffField)
    (u : Solution U b) :
    ∃ z : Solution V c, z.toH1.grad = u.toH1.grad := by
  refine ⟨{ toH1 := u.toH1.restrict V.isOpen hVU, isHarmonic := ?_ }, rfl⟩
  rw [hrep]
  exact u.isHarmonic.restrict_of_isOpen_of_isEllipticFieldOn U.isOpen V.isOpen hVU
    (hrep ▸ hEll)

/-- **The parent solution restricts to an aligned child cell** of the adapted
subdivision: the maximizer on `U_p = q□_p` restricts to a solution on
`U_j(z) = z + q□_j` for every aligned centre `z` inside the parent. -/
theorem exists_restrict_solution_adaptedCellAt (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p)
    {w : Fin d → ℤ} (hmem : adaptedCellCenter q j w ∈ adaptedCell q p) {lam Lam : ℝ}
    {b : CoeffOn (adaptedDomain hq p)} {c : CoeffOn (adaptedDomainAt hq j w)}
    (hrep : c.toCoeffField = b.toCoeffField)
    (hEll : IsEllipticFieldOn lam Lam (adaptedCellAt q j w) c.toCoeffField)
    (u : Solution (adaptedDomain hq p) b) :
    ∃ z : Solution (adaptedDomainAt hq j w) c, z.toH1.grad = u.toH1.grad :=
  exists_restrict_solution hrep (adaptedDomainAt_subset hq hjp hmem) hEll u

/-- The difference of two solutions on the same domain is again a solution: the
gradient difference is `a`-harmonic. -/
theorem exists_solution_grad_sub {U : Domain d} {lam Lam : ℝ} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (u w : Solution U a) :
    ∃ z : Solution U a, z.toH1.grad = fun x => u.toH1.grad x - w.toH1.grad x := by
  refine ⟨AHarmonicFunction.addSMulOfIntegrable u w
    (weakFluxIntegrable_of_isEllipticFieldOn hEll u)
    (weakFluxIntegrable_of_isEllipticFieldOn hEll w) (-1), ?_⟩
  rw [AHarmonicFunction.grad_addSMulOfIntegrable]
  funext x
  change u.toH1.grad x + (-1 : ℝ) • w.toH1.grad x = u.toH1.grad x - w.toH1.grad x
  rw [neg_one_smul, sub_eq_add_neg]

/-! ## The doubled response space of a cell -/

/-- **The doubled state of a solution lies in the response space**: taking the
adjoint solution to be zero in the description
`𝒮(V;a) = {(∇u + ∇u^*, a∇u - aᵗ∇u^*)}` gives `X = (∇v, a∇v) ∈ 𝒮(V;a)`. -/
theorem isDoubledResponseField_gradFlux {U : Domain d} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (v : Solution U a) :
    IsDoubledResponseField U a
      { potential := v.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) } := by
  have h := Internal.Ch02.BookCh02.doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn
    U a hEll v (zeroSolution U a.transpose)
  have hfield : doubledFieldOfSolutions a v (zeroSolution U a.transpose) =
      { potential := v.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) } := by
    unfold doubledFieldOfSolutions
    have hzero : (zeroSolution U a.transpose).toH1.grad = 0 := rfl
    rw [hzero]
    congr 1
    · funext x
      show v.toH1.grad x + (0 : Vec d → Vec d) x = v.toH1.grad x
      simp
    · funext x
      change matVecMul (a.toCoeffField x) (v.toH1.grad x) -
          matVecMul (matTranspose (a.toCoeffField x)) ((0 : Vec d → Vec d) x) =
        matVecMul (a.toCoeffField x) (v.toH1.grad x)
      rw [show ((0 : Vec d → Vec d) x) = (0 : Vec d) from rfl, matVecMul_zero, sub_zero]
  rwa [hfield] at h

/-- **The difference of two optimizer states lies in the response space of the
cell**: *"the parent optimizer restricts to an admissible solution on every
child … thus `X_t - X(U_k(z)) ∈ 𝒮(U_k(z);a)`"*. -/
theorem isDoubledResponseField_grad_sub {U : Domain d} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u w : Solution U a) :
    IsDoubledResponseField U a
      { potential := fun x => u.toH1.grad x - w.toH1.grad x
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) -
          matVecMul (a.toCoeffField x) (w.toH1.grad x) } := by
  obtain ⟨z, hz⟩ := exists_solution_grad_sub hEll u w
  have h := isDoubledResponseField_gradFlux hEll z
  have hfield :
      ({ potential := z.toH1.grad
         flux := fun x => matVecMul (a.toCoeffField x) (z.toH1.grad x) } : DoubledField d) =
        { potential := fun x => u.toH1.grad x - w.toH1.grad x
          flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) -
            matVecMul (a.toCoeffField x) (w.toH1.grad x) } := by
    rw [hz]
    congr 1
    funext x
    change matVecMul (a.toCoeffField x) (u.toH1.grad x - w.toH1.grad x) =
      matVecMul (a.toCoeffField x) (u.toH1.grad x) -
        matVecMul (a.toCoeffField x) (w.toH1.grad x)
    rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]
  rwa [hfield] at h

/-! ## The identities read on the adapted cells -/

/-- **The average identity on an aligned cell**, the average of the optimizer
state at `U_k(z)`: `(X(U_k(z)))_{U_k(z)} = (RA_k(z) + I_{2d})P`, with `A_k(z)`
the adapted response block of that child cell. -/
theorem blockAverage_adaptedCellAt (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    {a : CoeffSpace d} {c : CoeffOn (adaptedDomainAt hq k w)}
    (hc : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c = adaptedResponse q k w a)
    {p₀ q₀ : Vec d} {v : Solution (adaptedDomainAt hq k w) c}
    (hv : Book.Ch02.IsResponseMaximizer (adaptedDomainAt hq k w) c p₀ q₀ v) :
    ((Book.Ch02.averageGradient (adaptedDomainAt hq k w) c v,
        averageFlux (adaptedDomainAt hq k w) c v) : BlockVec d) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (adaptedResponse q k w a) ((-p₀, q₀) : BlockVec d)) +
        ((-p₀, q₀) : BlockVec d) := by
  rw [← hc]
  exact blockAverage_eq c hv

/-- **The average identity on the parent cell**, the average of the optimizer
state at `U_t`: `(X_t)_{U_t} = (RA_t + I_{2d})P`. -/
theorem blockAverage_adaptedCell (hq : q.PosDef) (p : ℤ)
    {a : CoeffSpace d} {b : CoeffOn (adaptedDomain hq p)}
    (hb : Book.Ch02.coarseBlockMatrix (adaptedDomain hq p) b = coarseBlock (adaptedCell q p) a)
    {p₀ q₀ : Vec d} {v : Solution (adaptedDomain hq p) b}
    (hv : Book.Ch02.IsResponseMaximizer (adaptedDomain hq p) b p₀ q₀ v) :
    ((Book.Ch02.averageGradient (adaptedDomain hq p) b v,
        averageFlux (adaptedDomain hq p) b v) : BlockVec d) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (coarseBlock (adaptedCell q p) a) ((-p₀, q₀) : BlockVec d)) +
        ((-p₀, q₀) : BlockVec d) := by
  rw [← hb]
  exact blockAverage_eq b hv

/-- **The exact comparison identity across the aligned subdivision**, the
comparison of the optimizer averages at the pair `(U_k(z), U_t)`:
`|M_0^{1/2}((X(U_k(z)))_{U_k(z)} - (X_t)_{U_t})|²
  = P·(A_k(z) - A_t)M_0^{-1}(A_k(z) - A_t)P`, the block defect being exactly the
one averaged in the recent cell defects `C_{k,t}(E)` and `D_{k,t}(E)`. -/
theorem metricNormSq_blockAverage_sub_adapted (hq : q.PosDef) (k p : ℤ)
    (w : Fin d → ℤ) {a : CoeffSpace d} {c : CoeffOn (adaptedDomainAt hq k w)}
    {b : CoeffOn (adaptedDomain hq p)} (m : Mat d)
    (hc : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c = adaptedResponse q k w a)
    (hb : Book.Ch02.coarseBlockMatrix (adaptedDomain hq p) b = coarseBlock (adaptedCell q p) a)
    {p₀ q₀ : Vec d} {v : Solution (adaptedDomainAt hq k w) c} {u : Solution (adaptedDomain hq p) b}
    (hv : Book.Ch02.IsResponseMaximizer (adaptedDomainAt hq k w) c p₀ q₀ v)
    (hu : Book.Ch02.IsResponseMaximizer (adaptedDomain hq p) b p₀ q₀ u) :
    blockVecDot
        (((Book.Ch02.averageGradient (adaptedDomainAt hq k w) c v,
            averageFlux (adaptedDomainAt hq k w) c v) : BlockVec d) -
          ((Book.Ch02.averageGradient (adaptedDomain hq p) b u,
            averageFlux (adaptedDomain hq p) b u) : BlockVec d))
        (blockMatVecMul (blockDiag m m⁻¹)
          (((Book.Ch02.averageGradient (adaptedDomainAt hq k w) c v,
              averageFlux (adaptedDomainAt hq k w) c v) : BlockVec d) -
            ((Book.Ch02.averageGradient (adaptedDomain hq p) b u,
              averageFlux (adaptedDomain hq p) b u) : BlockVec d))) =
      blockVecDot
        (blockMatVecMul
          (blockSub (adaptedResponse q k w a) (coarseBlock (adaptedCell q p) a))
          ((-p₀, q₀) : BlockVec d))
        (blockMatVecMul (blockReflect (blockDiag m m⁻¹))
          (blockMatVecMul
            (blockSub (adaptedResponse q k w a) (coarseBlock (adaptedCell q p) a))
            ((-p₀, q₀) : BlockVec d))) := by
  rw [← hc, ← hb]
  exact metricNormSq_blockAverage_sub c b m hv hu

end

end Response
end HighContrast
end HCPolySupport
