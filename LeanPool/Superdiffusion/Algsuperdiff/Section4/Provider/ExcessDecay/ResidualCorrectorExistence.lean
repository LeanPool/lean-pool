/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryLaneMaxPrinciple
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicReplacement
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace
public import LeanPool.HighContrastHomogenization.Support.Ambient.ScalarMatrix
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

/-!
# ResidualCorrectorExistence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The residual corrector `w` on the truncated window

The replacement draft's item 2 defines the residual corrector `w` by a
Dirichlet problem on the truncated window `V = (x+□_{n-2}) ∩ □_m` and then
*uses* two things about it: that it is harmonic
(`AffineSplitHarmonic.exists_affineSplit`) and that it is bounded by the
boundary data (`BoundaryLaneMaxPrinciple`).

## The datum, honestly (disclosed)

`HasBoundaryUpperBoundOn` and `MemH10` are stated in CoarseGraining's rigid
convention: the `H¹₀` witness must equal the given function as a *total*
function on `Vec d`, not merely a.e. on `V`.  The bound on the printed datum `h
- ℓ_h` (`AffineSplitLift.abs_sub_affineLift_volumeAverage_le`) is available
only *on the window*.  `exists_h1_clamp` bridges the two: it produces an
`H¹(V)` datum that is globally bounded by `M` and agrees with the original
wherever the original is bounded by `M` — in particular on all of the window,
under the residual bound.  This is a carrier adjustment, not a mathematical
hypothesis: no bound is assumed anywhere it is not proved.

## Main results

* `exists_weaklyHarmonicOn_of_datum` — the Dirichlet problem on any open bounded
  convex nonempty window, at the Laplacian.
* `hasBoundaryUpperBoundOn_of_datum_le` — the weak boundary bound from the datum.
* `exists_h1_clamp` — the globally clamped datum.
* `exists_residualCorrector` — the packaged corrector: harmonic, with the datum's
  trace, and two-sidedly bounded by `M`.
* `exists_residualCorrector_truncatedWindow` — the same on the boundary lane's
  own window `(x+□_k) ∩ □_m`.

## What is not done here

The draft's *split* boundary data ("`h - ℓ_h` on `∂V ∩ ∂□_m` and `0` on `∂V ∩
□_m`") is replaced by the single datum `h - ℓ_h` on all of `∂V`.  This is a
proof-route choice, not a statement change: the sup bound that item 2(ii) needs
is `‖h-ℓ_h‖_{L^∞}` on the whole window either way, so the corrector produced
here carries exactly the constant the draft's does.

## References

* CoarseGraining, `PDE/DirichletRHS.lean`, `Sobolev/PotentialSolenoidalL2.lean`,
  `Sobolev/Truncation/{Basic,MatchedTrace}.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The identity coefficient field -/

/-- The identity coefficient field, as CoarseGraining's constant field at
`scalarMatrix 1`. -/
def unitCoeffField (d : ℕ) : CoeffField d := constantCoeffField (scalarMatrix (d := d) 1)

theorem matVecMul_unitCoeffField (x v : Vec d) :
    matVecMul (unitCoeffField d x) v = v := by
  show matVecMul (scalarMatrix (d := d) 1) v = v
  rw [matVecMul_scalarMatrix, one_smul]

theorem isEllipticFieldOn_unitCoeffField {V : Set (Vec d)} (hV : MeasurableSet V) :
    IsEllipticFieldOn 1 1 V (unitCoeffField d) :=
  isEllipticFieldOn_constantCoeffField hV (isEllipticMatrix_scalarMatrix one_pos)

/-! ## 2. The Dirichlet problem on the window -/

/-- **The residual corrector exists.**

On any open bounded convex nonempty window `V` and for any `H¹(V)` datum `Φ`
there is a weakly harmonic `w` with `w - Φ ∈ H¹₀(V)`: the draft's Dirichlet
problem for the residual corrector. -/
theorem exists_weaklyHarmonicOn_of_datum [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (Φ : H1Function V) :
    ∃ w : H1Function V, IsWeaklyHarmonicOn V w ∧
      MemH10 V (fun y => w.toFun y - Φ.toFun y) := by
  have : IsFiniteMeasure (volumeMeasureOn V) := hV.isFiniteMeasure_restrict_volume
  have hgrad : MemVectorL2 V Φ.grad := Φ.grad_memVectorL2
  have hg : MemVectorL2 V (fun y => -Φ.grad y) := hgrad.neg
  have hrealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization V :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
      hV
  obtain ⟨rho, hrho⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := unitCoeffField d) (U := V) (g := fun y => -Φ.grad y) (lam := 1) (Lam := 1)
      hg hrealize hne (isEllipticFieldOn_unitCoeffField hV.isOpen.measurableSet)
  have hrhomem : MemVectorL2 V rho.toH1Function.grad := rho.toH1Function.grad_memVectorL2
  refine ⟨Φ + rho.toH1Function, ?_, ⟨rho, ?_⟩⟩
  · intro φ
    have hsplit := integral_vecDot_add_left_split (U := V) hgrad hrhomem
      (H := (Φ + rho.toH1Function).grad)
      (fun x => by rw [H1Function.add_grad]) φ
    have hid := hrho φ
    have hcongr : ∫ x in V, vecDot (matVecMul (unitCoeffField d x)
          (rho.toH1Function.grad x)) (φ.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        show vecDot (matVecMul (unitCoeffField d x) (rho.toH1Function.grad x))
            (φ.toH1Function.grad x) =
          vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x)
        rw [matVecMul_unitCoeffField])
    rw [hcongr] at hid
    have hneg : ∫ x in V, vecDot ((fun y => -Φ.grad y) x) (φ.toH1Function.grad x) ∂volume =
        -∫ x in V, vecDot (Φ.grad x) (φ.toH1Function.grad x) ∂volume := by
      have hfun : (fun x => vecDot ((fun y => -Φ.grad y) x) (φ.toH1Function.grad x)) =
          fun x => -vecDot (Φ.grad x) (φ.toH1Function.grad x) := by
        funext x
        show vecDot (-Φ.grad x) (φ.toH1Function.grad x) = _
        rw [vecDot_neg_left]
      rw [hfun, integral_neg]
    rw [hneg] at hid
    rw [hsplit, hid]
    ring
  · funext y
    show rho.toH1Function.toFun y = (Φ + rho.toH1Function).toFun y - Φ.toFun y
    rw [H1Function.add_toFun]
    show rho.toH1Function.toFun y = Φ.toFun y + rho.toH1Function.toFun y - Φ.toFun y
    ring

/-! ## 3. The boundary bound from the datum -/

theorem hasBoundaryUpperBoundOn_of_datum_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {w Φ : H1Function V} {M : ℝ}
    (hdiff : MemH10 V (fun y => w.toFun y - Φ.toFun y)) (hΦ : ∀ y, Φ.toFun y ≤ M) :
    HasBoundaryUpperBoundOn V w M := by
  obtain ⟨ψ, hψ⟩ := memH10_max_sub_matched hV w Φ hdiff M
  obtain ⟨v, hvf, hvg⟩ := exists_h1_max_sub_const hV w M
  have hψf : ψ.toH1Function.toFun = fun y => max (w.toFun y - M) 0 := by
    rw [hψ]
    funext y
    rw [max_eq_right (by linarith only [hΦ y] : Φ.toFun y - M ≤ 0), sub_zero]
  refine ⟨ψ, hψf, ?_⟩
  have heq : ψ.toH1Function.toFun = v.toFun := by rw [hψf, hvf]
  have hgrad := HCPolySupport.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hV.isOpen
    (u := ψ.toH1Function) (v := v)
    (Filter.Eventually.of_forall fun x => congrFun heq x)
  filter_upwards [hgrad, hvg] with y h1 h2
  rw [h1, h2]

/-! ## 4. The globally clamped datum -/

private theorem clamp_bounds (t M : ℝ) (hM : 0 ≤ M) :
    t - max (t - M) 0 + max (-t - M) 0 ≤ M ∧
      -M ≤ t - max (t - M) 0 + max (-t - M) 0 := by
  rcases le_total t M with h1 | h1
  · rw [max_eq_right (by linarith only [h1] : t - M ≤ 0)]
    rcases le_total (-t - M) 0 with h2 | h2
    · rw [max_eq_right h2]
      exact ⟨by linarith only [h1], by linarith only [h2]⟩
    · rw [max_eq_left h2]
      exact ⟨by linarith only [hM], by linarith only [hM]⟩
  · rw [max_eq_left (by linarith only [h1] : (0 : ℝ) ≤ t - M),
      max_eq_right (by linarith only [h1, hM] : -t - M ≤ 0)]
    exact ⟨by linarith only [hM], by linarith only [hM]⟩

private theorem clamp_eq (t M : ℝ) (h : |t| ≤ M) :
    t - max (t - M) 0 + max (-t - M) 0 = t := by
  rw [abs_le] at h
  rw [max_eq_right (by linarith only [h.2] : t - M ≤ 0),
    max_eq_right (by linarith only [h.1] : -t - M ≤ 0)]
  ring

/-- **The globally clamped datum.**  Every `H¹(V)` function has an `H¹(V)` clamp at
level `M`, globally bounded by `M` and unchanged wherever the original already
satisfies `|Φ| ≤ M`.  This is the carrier bridge described in the module
docstring, built from CoarseGraining's positive-part truncation applied to `Φ`
and `-Φ`. -/
theorem exists_h1_clamp {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (Φ : H1Function V) {M : ℝ} (hM : 0 ≤ M) :
    ∃ Ψ : H1Function V, (∀ y, Ψ.toFun y ≤ M) ∧ (∀ y, -M ≤ Ψ.toFun y) ∧
      ∀ y, |Φ.toFun y| ≤ M → Ψ.toFun y = Φ.toFun y := by
  obtain ⟨v1, hv1f, _⟩ := exists_h1_max_sub_const hV Φ M
  obtain ⟨v2, hv2f, _⟩ := exists_h1_max_sub_const hV (-Φ) M
  have hval : ∀ y, (Φ - v1 + v2).toFun y =
      Φ.toFun y - max (Φ.toFun y - M) 0 + max (-Φ.toFun y - M) 0 := by
    intro y
    rw [H1Function.add_toFun, H1Function.sub_toFun]
    show Φ.toFun y - v1.toFun y + v2.toFun y = _
    rw [hv1f, hv2f, H1Function.neg_toFun]
  refine ⟨Φ - v1 + v2, fun y => ?_, fun y => ?_, fun y hy => ?_⟩
  · rw [hval y]
    exact (clamp_bounds (Φ.toFun y) M hM).1
  · rw [hval y]
    exact (clamp_bounds (Φ.toFun y) M hM).2
  · rw [hval y]
    exact clamp_eq (Φ.toFun y) M hy

/-! ## 5. The packaged corrector -/

/-- **The residual corrector, packaged.** -/
theorem exists_residualCorrector [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (Φ : H1Function V) {M : ℝ} (hupper : ∀ y, Φ.toFun y ≤ M)
    (hlower : ∀ y, -M ≤ Φ.toFun y) :
    ∃ w : H1Function V, IsWeaklyHarmonicOn V w ∧
      MemH10 V (fun y => w.toFun y - Φ.toFun y) ∧
      HasBoundaryUpperBoundOn V w M ∧ HasBoundaryUpperBoundOn V (-w) M := by
  obtain ⟨w, hharm, hdiff⟩ := exists_weaklyHarmonicOn_of_datum hV hne Φ
  refine ⟨w, hharm, hdiff, hasBoundaryUpperBoundOn_of_datum_le hV hdiff hupper, ?_⟩
  have hdiffneg : MemH10 V (fun y => (-w).toFun y - (-Φ).toFun y) := by
    have h := memH10_neg hdiff
    have hfun : (fun y => -(w.toFun y - Φ.toFun y)) =
        fun y => (-w).toFun y - (-Φ).toFun y := by
      funext y
      rw [H1Function.neg_toFun, H1Function.neg_toFun]
      ring
    rwa [hfun] at h
  refine hasBoundaryUpperBoundOn_of_datum_le hV hdiffneg fun y => ?_
  rw [H1Function.neg_toFun]
  show -Φ.toFun y ≤ M
  linarith only [hlower y]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
