/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedFlow

/-!
# The truncated Cauchy transport

`FastDynamo/Dynamics/Ideal/TruncatedFlow.lean` packages the truncated plane flow as the datum
`truncatedFlowData` and reads off the truncated particle flow `literalTruncatedFlow … N t`, its
`C^∞` periodic lift and its derivative flow `truncatedFlowFDeriv … N t`.  The truncated Cauchy
transport

```
  (𝒯₀^{(N)}(t) B)(x) = DΦ^{(N)}_t(Φ^{(N)}_{-t} x) · B(Φ^{(N)}_{-t} x)
```

(`eq:ideal-cauchy-formula`) is then the generic
`PeriodizedPlaneFlowData.transport` of
`FastDynamo/Dynamics/Flow/PeriodizedFlowSymbol.lean` at that datum, exactly as the untruncated
`idealTransport` (`FastDynamo/Dynamics/Ideal/CauchyOperator.lean`) is at `fullFlowData`.
Delivered here:

* `truncatedSymbol`, `memLp_truncatedSymbol`, with the sup bound `norm_truncatedSymbol_le` by
  `flowComplexDerivativeBound … t` of `FastDynamo/Dynamics/Flow/FlowDerivative.lean`, uniform
  in `N`;
* `idealTruncatedTransport`, its almost-everywhere representative and
  the `cauchy`-clause identity `(𝒯₀^{(N)}(t)B)(Φ^{(N)}_t a) = DΦ^{(N)}_t(a) B(a)` in the
  coordinatewise shape `IsIdealInductionGroup` uses;
* the plane-level comparison of the truncated objects with the untruncated ones: off the buffer
  discs of index `≥ N` the two flows, the two axial shifts and their differentials coincide
  (`planeTruncatedTransverseFlow_eq_planeTransverseFlow` and friends).  This is the geometric
  input of the `L²` convergence `𝒯₀^{(N)}(t)B → 𝒯₀(t)B` of
  `FastDynamo/Dynamics/Ideal/TruncatedConvergence.lean`, and it is the one part
  of the truncated tower that depends on the truncation itself.

The `L^∞` membership of the symbol rests on the derivative bound `norm_truncatedFlowFDerivC_le`,
which holds only under `0 ≤ tau`; following the convention of `FastDynamo/Conventions.lean`, the
generic `PeriodizedPlaneFlowData.symbolLInf` does **not** take that hypothesis as an argument but
branches on the membership itself, and `PeriodizedPlaneFlowData.symbolLInf_eq_toLp` recovers the
intended value from it.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The symbol of the truncated Cauchy transport -/

/-- **The symbol of the truncated Cauchy transport**: the complexified truncated derivative flow
read at the pre-image `Φ^{(N)}_{-t} x`, so that the transport is
`(𝒯₀^{(N)}(t)B)(x) = DΦ^{(N)}_t(Φ^{(N)}_{-t}x) B(Φ^{(N)}_{-t}x)`
(`eq:ideal-cauchy-formula`). -/
abbrev truncatedSymbol (N : ℕ) (t : ℝ) (x : Torus 3) : C3 →L[ℂ] C3 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).symbol t x

/-- The truncated symbol is the complexified truncated derivative read at the pre-image. -/
theorem truncatedSymbol_eq (N : ℕ) (t : ℝ) (x : Torus 3) :
    truncatedSymbol h P angularSpeed axialSpeed tau N t x =
      truncatedFlowFDerivC h P angularSpeed axialSpeed tau N t
        (literalTruncatedFlow h P angularSpeed axialSpeed tau N (-t) x) := rfl

/-- **The symbol is bounded by `24 (1 + |t| · slope)`, uniformly in `N` and in the point.** -/
theorem norm_truncatedSymbol_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ) (x : Torus 3) :
    ‖truncatedSymbol h P angularSpeed axialSpeed tau N t x‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau t :=
  norm_truncatedFlowFDerivC_le h P angularSpeed axialSpeed tau htau N t _

/-- The symbol is essentially bounded, hence an element of `L^∞(T³; ℂ³ →L[ℂ] ℂ³)`. -/
theorem memLp_truncatedSymbol (htau : 0 ≤ tau) (N : ℕ) (t : ℝ) :
    MemLp (truncatedSymbol h P angularSpeed axialSpeed tau N t) ∞
      (volume : Measure (Torus 3)) :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).memLp_symbol_of_bound
    (norm_truncatedSymbol_le h P angularSpeed axialSpeed tau htau N t)

/-! ## The truncated Cauchy transport -/

/-- **The truncated Cauchy transport** `𝒯₀^{(N)}(t)` (`eq:ideal-cauchy-formula`):
pointwise multiplication by the truncated symbol, composed with the `L²` pull-back along the
measure-preserving map `Φ^{(N)}_{-t}`. -/
abbrev idealTruncatedTransport (N : ℕ) (t : ℝ) :
    LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).transport t

/-- **The almost-everywhere representative of the truncated Cauchy transport.** -/
theorem idealTruncatedTransport_coe_ae (htau : 0 ≤ tau) (N : ℕ) (t : ℝ) (B : LiteralC3L2) :
    ((idealTruncatedTransport h P angularSpeed axialSpeed tau N t B : LiteralC3L2) :
        Torus 3 → C3) =ᵐ[volume]
      fun x ↦ truncatedSymbol h P angularSpeed axialSpeed tau N t x
        ((B : Torus 3 → C3)
          (literalTruncatedFlow h P angularSpeed axialSpeed tau N (-t) x)) :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).transport_coe_ae
    (memLp_truncatedSymbol h P angularSpeed axialSpeed tau htau N t) B

/-- **The Cauchy formula for the truncated transport**, in the coordinatewise shape of the
`cauchy` clause of `IsIdealInductionGroup`: `(𝒯₀^{(N)}(t)B)(Φ^{(N)}_t a) = DΦ^{(N)}_t(a) B(a)`
almost everywhere (`eq:ideal-cauchy-formula`). -/
theorem idealTruncatedTransport_cauchy (htau : 0 ≤ tau) (N : ℕ) (t : ℝ) (B : LiteralC3L2) :
    ∀ᵐ a : Torus 3, ∀ i : Fin 3,
      ((idealTruncatedTransport h P angularSpeed axialSpeed tau N t B : LiteralC3L2) :
          Torus 3 → C3) (literalTruncatedFlow h P angularSpeed axialSpeed tau N t a) i =
        ∑ j : Fin 3,
          ((truncatedFlowFDeriv h P angularSpeed axialSpeed tau N t a
            (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * (B : Torus 3 → C3) a j :=
  (truncatedFlowData h P angularSpeed axialSpeed tau N).transport_cauchy
    (memLp_truncatedSymbol h P angularSpeed axialSpeed tau htau N t) B

/-! ## Comparison with the untruncated flow, off the discarded buffer discs -/

/-- **Off the discarded buffer discs the truncated plane flow is the full plane flow**: either the
point lies in a retained disc, where both are the cell flow, or it lies in no disc at all, where
both are the identity. -/
theorem planeTruncatedTransverseFlow_eq_planeTransverseFlow (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, N ≤ n → x ∉ P.scaleFamily.bufferDisk n) :
    planeTruncatedTransverseFlow h P angularSpeed N t x =
      planeTransverseFlow h P angularSpeed t x := by
  by_cases hbuf : ∃ k : ℕ, x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    have hlt : k < N := by
      by_contra hcon
      exact hx k (Nat.not_lt.1 hcon) hk
    rw [planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hlt hk,
      planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hk]
  · rw [planeTruncatedTransverseFlow_eq_self h P angularSpeed N t
      fun n _ hmem ↦ hbuf ⟨n, hmem⟩,
      planeTransverseFlow_eq_self_of_outside_buffers h P angularSpeed t
        fun n hmem ↦ hbuf ⟨n, hmem⟩]

/-- Off the discarded buffer discs the truncated axial shift is the full axial shift. -/
theorem planeTruncatedAxialShift_eq_planeAxialShift (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, N ≤ n → x ∉ P.scaleFamily.bufferDisk n) :
    planeTruncatedAxialShift h P axialSpeed tau N t x = planeAxialShift h P axialSpeed tau t x := by
  by_cases hbuf : ∃ k : ℕ, x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    have hlt : k < N := by
      by_contra hcon
      exact hx k (Nat.not_lt.1 hcon) hk
    rw [planeTruncatedAxialShift_eq_cell h P axialSpeed tau N t hlt hk,
      planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hk]
  · rw [planeTruncatedAxialShift_eq_zero h P axialSpeed tau N t fun n _ hmem ↦ hbuf ⟨n, hmem⟩,
      planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t fun n hmem ↦ hbuf ⟨n, hmem⟩]

/-- Off the discarded buffer discs the two transverse differentials coincide. -/
theorem fderiv_planeTruncatedTransverseFlow_eq (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, N ≤ n → x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeTruncatedTransverseFlow h P angularSpeed N t) x =
      fderiv ℝ (planeTransverseFlow h P angularSpeed t) x := by
  by_cases hbuf : ∃ k : ℕ, x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    have hlt : k < N := by
      by_contra hcon
      exact hx k (Nat.not_lt.1 hcon) hk
    rw [fderiv_planeTruncatedTransverseFlow_eq_cell h P angularSpeed N t hlt hk,
      fderiv_planeTransverseFlow_eq_cell_of_mem_bufferDisk h P angularSpeed t hk]
  · rw [fderiv_planeTruncatedTransverseFlow_eq_id h P angularSpeed N t
      fun n _ hmem ↦ hbuf ⟨n, hmem⟩,
      fderiv_planeTransverseFlow_eq_id_of_outside_buffers h P angularSpeed t
        fun n hmem ↦ hbuf ⟨n, hmem⟩]

/-- Off the discarded buffer discs the two axial differentials coincide. -/
theorem fderiv_planeTruncatedAxialShift_eq (N : ℕ) (t : ℝ) {x : ℝ × ℝ}
    (hx : ∀ n : ℕ, N ≤ n → x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (planeTruncatedAxialShift h P axialSpeed tau N t) x =
      fderiv ℝ (planeAxialShift h P axialSpeed tau t) x := by
  by_cases hbuf : ∃ k : ℕ, x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    have hlt : k < N := by
      by_contra hcon
      exact hx k (Nat.not_lt.1 hcon) hk
    rw [fderiv_planeTruncatedAxialShift_eq_cell h P axialSpeed tau N t hlt hk,
      fderiv_planeAxialShift_eq_cell_of_mem_bufferDisk h P axialSpeed tau t hk]
  · rw [fderiv_planeTruncatedAxialShift_eq_zero h P axialSpeed tau N t
      fun n _ hmem ↦ hbuf ⟨n, hmem⟩,
      fderiv_planeAxialShift_eq_zero_of_outside_buffers h P axialSpeed tau t
        fun n hmem ↦ hbuf ⟨n, hmem⟩]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
