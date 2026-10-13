/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.UnitCubeWeakIBP
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.SkewCancellation

/-!
# SplitIdentity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `D_h` splitting identity `e.sensitivity.basic.split`

Source: ABK26.  With `w = ½ v(·, U, p, q; a)` and `w* = ½ v(·, U, p, -q; aᵗ)`,

  `⨍ ∇w* · h ∇w = -p · ⨍ h ∇w - ⨍ (w + w* + ℓ_p) (∇·h) · ∇w`.

The two ingredients are already proved upstream: the pointwise skew
cancellation (`quadForm_coarseMatrixDerivative_eq_average_sum_pairing`) and the
weak integration by parts
(`integral_grad_dot_matVecMul_grad_eq_neg_of_hasWeakDeriv`).  What this module
adds is the bookkeeping that turns the two into a single identity for the
frozen quadratic form at the *unscaled* maximizers `vAdj`, `v`, namely

  `P · D_h P = -2 p · ⨍ h ∇v - 2 ⨍ u (∇·h) · ∇v`,

where `u ∈ H¹₀(U)` is any zero-trace witness for the source combination
`½(∇vAdj + ∇v) + p = ∇w + ∇w* + p`.

The identity is proved at a **general** Chapter 2 domain `U` with a general
`L∞` skew field and general essentially bounded weak first-derivative data;
the frozen unit-cube carrier is a specialization at the end of the file.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Integrability of the two pairings -/

/-- Coordinates of `h ∇v` are square integrable. -/
theorem memScalarL2_matVecMul_grad {U : Domain d} (h : LInfSkewMatrixFieldOn U)
    (v : H1Function ((U : Set (Vec d)))) (i : Fin d) :
    MemScalarL2 ((U : Set (Vec d))) fun x => matVecMul (h.1.1 x) (v.grad x) i :=
  memScalarL2_matVecMul_coord (fun i j => h.1.2 i j) (fun j => v.gradMemL2 j) i

/-- The `∇u · h ∇v` integrand is integrable. -/
theorem integrable_vecDot_matVecMul_grad {U : Domain d}
    (h : LInfSkewMatrixFieldOn U) (u v : H1Function ((U : Set (Vec d)))) :
    Integrable (fun x => vecDot (u.grad x) (matVecMul (h.1.1 x) (v.grad x)))
      (volumeMeasureOn ((U : Set (Vec d)))) := by
  have hpt : (fun x => vecDot (u.grad x) (matVecMul (h.1.1 x) (v.grad x))) =
      fun x => ∑ i, u.grad x i * matVecMul (h.1.1 x) (v.grad x) i := rfl
  rw [hpt]
  exact integrable_finsetSum Finset.univ fun i _ =>
    (u.gradMemL2 i).integrable_mul (memScalarL2_matVecMul_grad h v i)

/-- The `p · h ∇v` integrand is integrable. -/
theorem integrable_vecDot_const_matVecMul_grad {U : Domain d}
    (h : LInfSkewMatrixFieldOn U) (v : H1Function ((U : Set (Vec d))))
    (p : Vec d) :
    Integrable (fun x => vecDot p (matVecMul (h.1.1 x) (v.grad x)))
      (volumeMeasureOn ((U : Set (Vec d)))) := by
  have : IsFiniteMeasure (volumeMeasureOn ((U : Set (Vec d)))) :=
    U.isDomain.isFiniteMeasure_restrict_volume
  have hpt : (fun x => vecDot p (matVecMul (h.1.1 x) (v.grad x))) =
      fun x => ∑ i, p i * matVecMul (h.1.1 x) (v.grad x) i := rfl
  rw [hpt]
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  exact ((memScalarL2_matVecMul_grad h v i).integrable one_le_two).const_mul (p i)

/-! ## Average-level bookkeeping -/

/-- Pulling a constant vector out of the average. -/
theorem average_vecDot_const_eq_vecDot_averageVec {U : Domain d}
    {G : Vec d → Vec d} (hG : ∀ i, Integrable (fun x => G x i)
      (volumeMeasureOn ((U : Set (Vec d))))) (p : Vec d) :
    Book.Ch02.average U (fun x => vecDot p (G x)) =
      vecDot p (Book.Ch02.averageVec U G) := by
  classical
  have hpt : (fun x => vecDot p (G x)) = fun x => ∑ i, p i * G x i := rfl
  have hdot : vecDot p (Book.Ch02.averageVec U G) =
      ∑ i, p i * Book.Ch02.average U (fun x => G x i) := rfl
  rw [hpt, hdot]
  change (MeasureTheory.volume ((U : Set (Vec d)))).toReal⁻¹ *
      ∫ x in ((U : Set (Vec d))), (∑ i, p i * G x i) ∂MeasureTheory.volume =
    ∑ i, p i * Book.Ch02.average U (fun x => G x i)
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => (hG i).const_mul (p i)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul]
  change (MeasureTheory.volume ((U : Set (Vec d)))).toReal⁻¹ *
      (p i * ∫ x in ((U : Set (Vec d))), G x i ∂MeasureTheory.volume) =
    p i * Book.Ch02.average U (fun x => G x i)
  unfold Book.Ch02.average
  ring

/-- Averages are additive on integrable summands. -/
theorem average_sub {U : Domain d} {f g : Vec d → ℝ}
    (hf : Integrable f (volumeMeasureOn ((U : Set (Vec d)))))
    (hg : Integrable g (volumeMeasureOn ((U : Set (Vec d))))) :
    Book.Ch02.average U (fun x => f x - g x) =
      Book.Ch02.average U f - Book.Ch02.average U g := by
  unfold Book.Ch02.average
  rw [MeasureTheory.integral_sub hf hg]
  ring

/-- Averages commute with multiplication by a real constant. -/
theorem average_const_mul {U : Domain d} (c : ℝ) (f : Vec d → ℝ) :
    Book.Ch02.average U (fun x => c * f x) = c * Book.Ch02.average U f := by
  unfold Book.Ch02.average
  rw [MeasureTheory.integral_const_mul]
  ring

/-! ## The splitting identity -/

/-- **The `D_h` splitting identity at a general domain.**

`P · D_h(U; a) P = -2 p · ⨍_U h ∇v - 2 ⨍_U u (∇·h) · ∇v`,

for `P = (p, -q)`, arbitrary response maximizers `vAdj` (for `(aᵗ, p, -q)`) and
`v` (for `(a, p, q)`), and any `H¹₀(U)` witness `u` for the source combination
`½(∇vAdj + ∇v) + p`.

The `u`-hypothesis is exactly the source claim `∇w + ∇w* + p ∈ L²_{pot,0}(U)`;
it is discharged at every use. -/
theorem quadForm_coarseMatrixDerivative_eq_split
    (U : Domain d) (a : CoeffOn U) (h : LInfSkewMatrixFieldOn U)
    {Dh : Fin d → Vec d → Mat d}
    (hDmem : ∀ k i j, MemLp (fun x => Dh k x i j) ∞
      (volumeMeasureOn ((U : Set (Vec d)))))
    (hweak : ∀ k i j, HasWeakPartialDerivOn ((U : Set (Vec d))) k
      (fun x => h.1.1 x i j) (fun x => Dh k x i j))
    (p q : Vec d) (vAdj : Solution U a.transpose) (v : Solution U a)
    (hvAdj : IsResponseMaximizer U a.transpose p (-q) vAdj)
    (hv : IsResponseMaximizer U a p q v)
    (u : H10Function ((U : Set (Vec d))))
    (hu : ∀ᵐ x ∂volumeMeasureOn ((U : Set (Vec d))),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p) :
    blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q)) =
      -2 * vecDot p
          (Book.Ch02.averageVec U
            (fun x => matVecMul (h.1.1 x) (v.toH1.grad x)))
        - 2 * Book.Ch02.average U (fun x => u.toH1Function.toFun x *
            vecDot (matWeakDiv Dh x) (v.toH1.grad x)) := by
  classical
  have hquad :=
    quadForm_coarseMatrixDerivative_eq_average_sum_pairing U a h p q vAdj v hvAdj hv
  -- pointwise rewriting of the summed gradient through the `H¹₀` witness
  have hpt : (fun x => vecDot (vAdj.toH1.grad x + v.toH1.grad x)
        (matVecMul (h.1.1 x) (v.toH1.grad x)))
      =ᵐ[volumeMeasureOn ((U : Set (Vec d)))]
      fun x => 2 * vecDot (u.toH1Function.grad x)
            (matVecMul (h.1.1 x) (v.toH1.grad x)) -
          2 * vecDot p (matVecMul (h.1.1 x) (v.toH1.grad x)) := by
    filter_upwards [hu] with x hx
    have hcoord : ∀ i : Fin d, vAdj.toH1.grad x i + v.toH1.grad x i =
        2 * (u.toH1Function.grad x i - p i) := by
      intro i
      have hxi := congrFun hx i
      have hxi' : u.toH1Function.grad x i =
          2⁻¹ * (vAdj.toH1.grad x i + v.toH1.grad x i) + p i := hxi
      linarith
    change (∑ i, (vAdj.toH1.grad x i + v.toH1.grad x i) *
          matVecMul (h.1.1 x) (v.toH1.grad x) i) =
        2 * (∑ i, u.toH1Function.grad x i *
            matVecMul (h.1.1 x) (v.toH1.grad x) i) -
          2 * ∑ i, p i * matVecMul (h.1.1 x) (v.toH1.grad x) i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord i]
    ring
  have haverage : Book.Ch02.average U (fun x =>
      vecDot (vAdj.toH1.grad x + v.toH1.grad x)
        (matVecMul (h.1.1 x) (v.toH1.grad x))) =
      Book.Ch02.average U (fun x => 2 * vecDot (u.toH1Function.grad x)
            (matVecMul (h.1.1 x) (v.toH1.grad x)) -
          2 * vecDot p (matVecMul (h.1.1 x) (v.toH1.grad x))) := by
    unfold Book.Ch02.average
    congr 1
    exact MeasureTheory.integral_congr_ae hpt
  have hiA : Integrable (fun x => (2 : ℝ) * vecDot (u.toH1Function.grad x)
      (matVecMul (h.1.1 x) (v.toH1.grad x)))
      (volumeMeasureOn ((U : Set (Vec d)))) :=
    (integrable_vecDot_matVecMul_grad h u.toH1Function v.toH1).const_mul 2
  have hiB : Integrable (fun x => (2 : ℝ) *
      vecDot p (matVecMul (h.1.1 x) (v.toH1.grad x)))
      (volumeMeasureOn ((U : Set (Vec d)))) :=
    (integrable_vecDot_const_matVecMul_grad h v.toH1 p).const_mul 2
  have hsplit := average_sub (U := U) hiA hiB
  have hconst : Book.Ch02.average U (fun x =>
      (2 : ℝ) * vecDot p (matVecMul (h.1.1 x) (v.toH1.grad x))) =
      2 * vecDot p
        (Book.Ch02.averageVec U
          (fun x => matVecMul (h.1.1 x) (v.toH1.grad x))) := by
    rw [average_const_mul,
      average_vecDot_const_eq_vecDot_averageVec (U := U)
        (G := fun x => matVecMul (h.1.1 x) (v.toH1.grad x))
        (fun i => (memScalarL2_matVecMul_grad h v.toH1 i).integrable one_le_two) p]
  have hibp := integral_grad_dot_matVecMul_grad_eq_neg_of_hasWeakDeriv
    U.isDomain U.nonempty h.2 (fun i j => h.1.2 i j) hDmem hweak u v.toH1
  have hibpAvg : Book.Ch02.average U (fun x =>
      (2 : ℝ) * vecDot (u.toH1Function.grad x)
        (matVecMul (h.1.1 x) (v.toH1.grad x))) =
      -2 * Book.Ch02.average U (fun x => u.toH1Function.toFun x *
        vecDot (matWeakDiv Dh x) (v.toH1.grad x)) := by
    rw [average_const_mul]
    unfold Book.Ch02.average
    rw [hibp]
    ring
  rw [hquad, haverage, hsplit, hconst, hibpAvg]
  ring

/-! ## The frozen unit-cube carrier -/

/-- **The `D_h` splitting identity at the frozen unit-cube carrier.**  All
analytic premises are discharged by the frozen `UnitCubeSkewW2Infinity`
structure fields; the only remaining input is the `H¹₀` witness. -/
theorem quadForm_coarseMatrixDerivative_unitCube_eq_split
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (h : UnitCubeSkewW2Infinity d) (p q : Vec d)
    (vAdj : Solution (cubeDomain (originCube d 0)) a.transpose)
    (v : Solution (cubeDomain (originCube d 0)) a)
    (hvAdj : IsResponseMaximizer (cubeDomain (originCube d 0)) a.transpose p (-q) vAdj)
    (hv : IsResponseMaximizer (cubeDomain (originCube d 0)) a p q v)
    (u : H10Function ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (hu : ∀ᵐ x ∂volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      u.toH1Function.grad x =
        (2 : ℝ)⁻¹ • (vAdj.toH1.grad x + v.toH1.grad x) + p) :
    blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative (cubeDomain (originCube d 0)) a
          h.toLInfSkewMatrixFieldOn.1) (p, -q)) =
      -2 * vecDot p (Book.Ch02.averageVec (cubeDomain (originCube d 0))
            (fun x => matVecMul (h.toLInfSkewMatrixFieldOn.1.1 x) (v.toH1.grad x)))
        - 2 * Book.Ch02.average (cubeDomain (originCube d 0)) (fun x =>
            u.toH1Function.toFun x *
              vecDot (matWeakDiv (unitCubeDerivData h) x) (v.toH1.grad x)) :=
  quadForm_coarseMatrixDerivative_eq_split (cubeDomain (originCube d 0)) a
    h.toLInfSkewMatrixFieldOn
    (fun k i j => h.firstDeriv_memLp k i j)
    (fun k i j => h.hasWeakPartialDeriv_value k i j)
    p q vAdj v hvAdj hv u hu

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Assembly
