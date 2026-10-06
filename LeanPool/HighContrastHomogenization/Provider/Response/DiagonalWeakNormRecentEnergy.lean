/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentCell

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The optimizer-difference energy on recent cells

The parent optimizer is an admissible child solution.  Expanding the child
functional around its canonical maximizer identifies the block energy of the
optimizer difference with four times the corresponding response deficit.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The response integrand of the canonical parent optimizer is integrable on
the parent cell, so its averages may be recombined across the aligned
partition. -/
theorem responseIntegrand_diagonalWeakOptimizer_integrableOn
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d)
    (p r : Vec d) :
    IntegrableOn
      (responseIntegrand (adaptedDomain hq t)
        (a.coeffOn (adaptedDomain hq t)) p r
        (diagonalWeakOptimizer hq t a p r))
      (adaptedCell q t) volume := by
  let v := diagonalWeakOptimizer hq t a p r
  let g : Vec d → Vec d := v.toH1.grad
  let f : Vec d → Vec d := fun x =>
    matVecMul ((⇑a.1 : CoeffField d) x) (g x)
  obtain ⟨hg, hf⟩ := diagonalWeakState_memVectorL2 hq t a p r
  change MemVectorL2 (adaptedCell q t) g at hg
  change MemVectorL2 (adaptedCell q t) f at hf
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCell q t)) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isFiniteMeasure_restrict_volume
  have hp : MemVectorL2 (adaptedCell q t) (fun _ => p) := memLp_const p
  have hr : MemVectorL2 (adaptedCell q t) (fun _ => r) := memLp_const r
  have henergyRaw : IntegrableOn (fun x => vecDot (g x) (f x))
      (adaptedCell q t) volume := integrableOn_vecDot_of_memVectorL2 hg hf
  have henergy : IntegrableOn (fun x =>
      vecDot (g x) (matVecMul (symmPart ((⇑a.1 : CoeffField d) x)) (g x)))
      (adaptedCell q t) volume := by
    refine henergyRaw.congr ?_
    filter_upwards with x
    exact vecDot_matVecMul_self_eq_symmPart ((⇑a.1 : CoeffField d) x) (g x)
  have hpflux : IntegrableOn (fun x => vecDot p (f x))
      (adaptedCell q t) volume := integrableOn_vecDot_of_memVectorL2 hp hf
  have hrgrad : IntegrableOn (fun x => vecDot r (g x))
      (adaptedCell q t) volume := integrableOn_vecDot_of_memVectorL2 hr hg
  have hsum := (henergy.const_mul (-(1 / 2 : ℝ))).sub hpflux |>.add hrgrad
  refine hsum.congr ?_
  filter_upwards with x
  change (-(1 / 2 : ℝ)) *
      vecDot (g x) (matVecMul (symmPart ((⇑a.1 : CoeffField d) x)) (g x)) -
      vecDot p (f x) + vecDot r (g x) =
    responseIntegrand (adaptedDomain hq t)
      (a.coeffOn (adaptedDomain hq t)) p r v x
  unfold responseIntegrand
  change _ = -((1 / 2 : ℝ) *
      vecDot (g x) (matVecMul (symmPart ((⇑a.1 : CoeffField d) x)) (g x))) -
    vecDot p (f x) + vecDot r (g x)
  ring

/-- On one aligned child, the optimizer-difference block energy is four times
the child response deficit of the restricted parent optimizer. -/
theorem diagonalWeak_child_difference_energy_eq [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    ∃ u : Solution (adaptedDomainAt hq k w)
        (a.coeffOn (adaptedDomainAt hq k w)),
      u.toH1.grad = (diagonalWeakOptimizer hq t a p r).toH1.grad ∧
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
          blockVecDot
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x)
            (blockMatVecMul
              (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
              (diagonalWeakChildState hq k w a p r x -
                diagonalWeakState hq t a p r x))) =
        4 * (responseJ (adaptedDomainAt hq k w)
              (a.coeffOn (adaptedDomainAt hq k w)) p r -
            responseValue (adaptedDomainAt hq k w)
              (a.coeffOn (adaptedDomainAt hq k w)) p r u) := by
  obtain ⟨u, hu⟩ := exists_diagonalWeakOptimizer_restrict_child
    hq hkt hw a p r
  refine ⟨u, hu, ?_⟩
  have henergy := average_block_energy_sub_eq
    (a.coeffOn (adaptedDomainAt hq k w))
    (diagonalWeakChildOptimizer_isMaximizer hq k w a p r) u
  have hstate : ∀ x,
      diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x =
        ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x -
            (diagonalWeakOptimizer hq t a p r).toH1.grad x,
          matVecMul ((⇑a.1 : CoeffField d) x)
            ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x -
              (diagonalWeakOptimizer hq t a p r).toH1.grad x)) := by
    intro x
    rw [diagonalWeakChildState_eq, diagonalWeakState_eq]
    apply Prod.ext
    · rfl
    · change matVecMul ((⇑a.1 : CoeffField d) x)
          ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x) -
          matVecMul ((⇑a.1 : CoeffField d) x)
            ((diagonalWeakOptimizer hq t a p r).toH1.grad x) =
          matVecMul ((⇑a.1 : CoeffField d) x)
            ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x -
              (diagonalWeakOptimizer hq t a p r).toH1.grad x)
      symm
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]
      rw [sub_eq_add_neg]
  have hintegrand : (fun x =>
      blockVecDot
        (diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)
        (blockMatVecMul
          (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
          (diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x))) =
      fun x =>
        blockVecDot
          ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x - u.toH1.grad x,
            matVecMul ((a.coeffOn (adaptedDomainAt hq k w)).toCoeffField x)
              ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x - u.toH1.grad x))
          (blockMatVecMul
            (blockMatrixField (a.coeffOn (adaptedDomainAt hq k w)) x)
            ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x - u.toH1.grad x,
              matVecMul ((a.coeffOn (adaptedDomainAt hq k w)).toCoeffField x)
                ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x - u.toH1.grad x))) := by
    funext x
    rw [hstate x, hu]
    rfl
  rw [hintegrand]
  exact henergy

end

end HCPolySupport.HighContrast.Response

end HighContrast

end HCPolySupport

end
