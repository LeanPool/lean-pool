/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Interior


/-!
# Outer cutoff tower and second derivatives near `tsupport ξ`

Higher interior regularity (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2) runs the interior `H²` estimate a second time, on the cutoff derivative
`ξ · ∂_ℓu` rather than on `u`. The commutator terms it produces are supported inside
`tsupport ξ` of the first tower, so the second run needs its own tower, based at that compact
set rather than at the original `V`, together with the second derivatives of `u` there.

Both follow from what the interior `H²` chain already provides. `tsupport ξ` is compact and sits
inside `Ω`, so `cutoffTowerOfIsCompactSubsetIsOpen` builds the outer tower, and
`interior_secondWeakDeriv` and `interior_H2_estimate` apply at that compact set verbatim.

## Main declarations

* `outerCutoffTower`: a cutoff tower based at `tsupport T.ξ`.
* `outer_secondWeakDeriv`: the interior second derivatives at the outer tower, as whole-space
  `EucL2 d` classes with one constant covering every direction pair.
* `interior_H2_estimate_near_tsupport_xi`: the interior `H²` estimate on `tsupport T.ξ`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Outer tower -/

/-- **Outer cutoff tower.** A tower based at the compact set `tsupport T.ξ` of a given
tower `T`. Its innermost cutoff is identically `1` on `tsupport T.ξ`
(`CutoffTower.zeta_eqOn_one`), which is what makes it invisible to every term of the
differentiated equation. -/
noncomputable def outerCutoffTower {V : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (T : CutoffTower Ω V) : CutoffTower Ω (tsupport T.ξ) :=
  cutoffTowerOfIsCompactSubsetIsOpen T.hξ.2.1 hΩo T.hξ.2.2

/-! ### Second derivatives at the outer tower -/

/-- **Interior second derivatives at the outer tower.** For every direction pair `(k, i)`
the whole-space extension of `ζ' · ∂ᵢu`, with `ζ'` the innermost cutoff of the outer tower, has
an `L²` weak `k`-derivative bounded by the data, with a single constant covering the whole index
square. The constant is quantified before the solution and the datum, so it depends only on the
operator and the tower. This is `interior_secondWeakDeriv` at `outerCutoffTower`, with the
per-pair constants collected into one. -/
theorem outer_secondWeakDeriv (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff) {V : Set (EuclideanSpace ℝ (Fin d))}
    (T : CutoffTower Ω V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ k i : Fin d, ∃ w : EucL2 d,
        HasWeakDeriv k
            (extendL2 hΩm (mulTest (outerCutoffTower hΩo T).hζ ((u : H1amb Ω) i.succ))) w
          ∧ ‖w‖ ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  classical
  choose Cd hCd0 hCd using fun k i : Fin d =>
    interior_secondWeakDeriv Op hΩm hA (outerCutoffTower hΩo T) k i
  refine ⟨∑ k : Fin d, ∑ i : Fin d, Cd k i,
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => hCd0 k i)), ?_⟩
  intro u f hu k i
  obtain ⟨w, hw, hwn⟩ := hCd k i u f hu
  refine ⟨w, hw, le_trans hwn ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc Cd k i ≤ ∑ i' : Fin d, Cd k i' :=
        Finset.single_le_sum (f := fun i' => Cd k i')
          (fun i' _ => hCd0 k i') (Finset.mem_univ i)
    _ ≤ ∑ k' : Fin d, ∑ i' : Fin d, Cd k' i' :=
        Finset.single_le_sum (f := fun k' => ∑ i' : Fin d, Cd k' i')
          (fun k' _ => Finset.sum_nonneg (fun i' _ => hCd0 k' i')) (Finset.mem_univ k)

/-- **Interior `H²` estimate on `tsupport T.ξ`.** The middle cutoff of a tower has
compact support inside `Ω`, so the interior `H²` estimate applies at that set: the second
weak derivatives of `u` exist in `L²(tsupport T.ξ)` and are bounded by the data. This is the
regularity of `u` the differentiated equation consumes on the region where the cutoff
commutators live. -/
theorem interior_H2_estimate_near_tsupport_xi {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff) {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (T : CutoffTower Ω V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ k i : Fin (n + 1),
      ∃ wki : Lp ℝ 2 (volume.restrict (tsupport T.ξ)),
        HasWeakDerivOn (tsupport T.ξ) k
            (restrictL2 (Ω := tsupport T.ξ) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
          ‖wki‖
            + ‖restrictL2 (Ω := tsupport T.ξ) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
            + ‖restrictL2 (Ω := tsupport T.ξ) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖) :=
  interior_H2_estimate Op hΩm hΩo hA T.hξ.2.1 T.hξ.2.2

end EllipticPdes.Regularity
