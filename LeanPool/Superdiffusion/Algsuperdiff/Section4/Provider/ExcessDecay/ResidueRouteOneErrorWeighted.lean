/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueRouteOne

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueEnergyLeg
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueCapChild
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidueFlushTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexComposed
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms

/-!
# ResidueRouteOneErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Route 1, machine-assembled at the flush sub-cube `K'`,
# at the error-weighted legs

Nothing here claims the anchor or any
source node.  It is `ResidueRouteOne`'s script with the same single row of
the regrouping changed as in `AssemblyComposedErrorWeighted` (the flat `∇h` leg keeps its
`𝓔`); the `ResidueRouteOne` module itself is untouched.

## What is proved

derived, from the *shapes* of the proved theorems, that the `p = 2`
coarse-graining comparison read at the flush scale-`n` sub-cube `K' =
flushSubCentre z m n i σ + □_n` prices the harmonic-approximation residue `‖u −
w‖_{L²(K')}` on the five canonical legs, but could not assemble it, because
the proved caps carry the anchor's geometry binder and `K'` provably fails it.
This module *is* that assembly:

```text
  ‖u − w‖_{L²(K')} ≤ Cfin ·
      ( s^{-4}·𝓔·‖u − (u)_{W'}‖_{L²(W')}
      + s^{-7}·σ_{n+3}^{-1}·3^{(1+s)n}·[g]_{H^s(W')}
      + s^{-6}·3^{(1+s)n}·[∇h]_{H^s(W')}
      + s^{-6}·𝓔·3^{n}·‖∇h‖_{L²(W')}
      + s^{-4}·𝓔·S )
```

with `𝓔 = fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩ (translate z ω)`
carried **explicitly** (not substituted by the frozen good event's `ε = 1/2`),
and `S` the boundary scalar at the flush cube `K = wellPlacedCentre z m (n+2) +
□_{n+2}` — which is the covering cube of `K'`
(`ResidueCapGeometry.wellPlacedCentre_flushSubCentre`).

* the deterministic `x`-frame envelope
  `ReindexEllipticity.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased_addThree`
  (binder-free: it needs only `translateSet x □_n ⊆ □_m`);
* the boundary energy leg at the two hinges (`ResidueEnergyLeg`);
* the child cube's `𝓔`-cap and forcing bracket at hinge (C)
  (`ResidueCapChild`);
* the **one-hop** Gagliardo transport `K' → W'` (`ResidueFlushTransport`) in
  place of the proved two-hop route through the `(n+2)` window, which `K'` does
  not meet.

## The `σ`-cancellation, machine-verified

The envelope is divided by `σ₀ = σ_{n+3}` and the energy term carries
`‖a₀‖^{1/2} = √σ_{n+3}` (`constantCoeffMatrixNormHalf_scalarComparator_sqrt`).
The two identities `√σ·√σ = σ` and `√σ·√(σ^{-1}) = 1` are consumed at `hET`
below: they cancel `σ` exactly on the four `√σ` legs and leave exactly one
`σ^{-1}` on the force leg.  **No `ν` is divided anywhere**: CoarseGraining's
`h1EnergyNormOnCube` at the re-based family equals `√(ν·⨍|∇u|²)`, and that
quantity is consumed *whole* by the boundary energy leg — it is never converted
to a Euclidean gradient.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application;
  `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

private theorem residueRouteOneErrorWeighted_comparisonBounds2 :
    ∀ (CE KE kappa cg A1 : ℝ) (_ : A1 = cg * (216 : ℝ) * (kappa * KE)) (_ : (0 : ℝ) ≤ A1) (s : ℝ)
      (_ : (0 : ℝ) < s) (n : ℤ) (_ : s ≤ (1 : ℝ)) (S Erep : ℝ) (_ : Erep ≤ CE * (1 / 2 : ℝ))
      (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn P2 : ℝ) (_ : P2 = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) :
        ℝ))) (Q3s : ℝ)
      (_ : Q3s = Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ))) (Q3sn : ℝ)
      (_ : Q3sn = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (Q1s : ℝ)
      (_ : Q1s = Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))) (R3n : ℝ) (_ : R3n = Real.rpow (3 :
        ℝ) (↑n : ℝ))
      (S4 S7 S6 Sm3 Sm2 : ℝ) (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Gs) (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ)
        ≤ S)
      (_ : (0 : ℝ) ≤ Q3s) (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ Sm3) (_ : (0 : ℝ) ≤ Sm2)
      (_ : (0 : ℝ) ≤ sig⁻¹) (_ : sig⁻¹ * sig = (1 : ℝ)) (_ : s⁻¹ ^ (4 : ℕ) = S4) (_ : S4 * Sm3 = S7)
      (_ : S4 * Sm2 = S6),
      R3n * Q3sn = Q1s ∧
        sig⁻¹ * R3n *
            (cg *
              ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                (kappa * KE * Erep *
                  (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                    Sm2 * (sig * Hn))))) ≤
          A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
                (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
              A1 * (S6 * Erep * R3n * Hn) +
            A1 * (S4 * Erep * S) := by
  intro CE KE kappa cg A1 hA1def hA1 s hs n hs1 S Erep hErepCap hErep0 sig X Gs Hs Hn P2 hP2def
    Q3s hQ3sdef Q3sn hQ3sndef Q1s hQ1sdef R3n hR3ndef S4 S7 S6 Sm3 Sm2 hX0 hGs0 hHs0 hS0 hQ3s0
      hR3n0 hSm30 hSm20 hsiginv0 hsinv hS4eq hS4Sm3 hS4Sm2
  have hRP2 : R3n * P2 ≤ 1 := by
    rw [hR3ndef, hP2def]
    exact rpow_three_frame_l2_le_one n
  have hRQ3s : R3n * Q3s ≤ 9 * Q1s := by
    rw [hR3ndef, hQ3sdef, hQ1sdef]
    exact rpow_three_frame_force_le n hs1
  have hRQ3sn : R3n * Q3sn = Q1s := by
    rw [hR3ndef, hQ3sndef, hQ1sdef]
    exact rpow_three_mul_eq_one_add s n
  have hT1 : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        A1 * (S6 * Erep * R3n * Hn) + A1 * (S4 * Erep * S) := by
    have hsplit : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
          (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) =
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * X)))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * S)))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) *
            (Erep * ((sig⁻¹ * sig) * (Sm2 * ((R3n * Q3s) * Hs))))) +
          A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * (Sm2 * (R3n * Hn))))) := by
      rw [hA1def]; ring
    rw [hsplit, hsinv]
    have hsinv4 : (0 : ℝ) ≤ (s⁻¹) ^ (4 : ℕ) := pow_nonneg (inv_nonneg.mpr hs.le) 4
    have hi : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X)))) ≤
        A1 * (S4 * Erep * X) := by
      have h1 : (R3n * P2) * X ≤ X := by
        have h := mul_le_mul_of_nonneg_right hRP2 hX0
        linarith only [h]
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * X))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * X)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
        _ = A1 * (S4 * Erep * X) := by rw [hS4eq]; ring
    have hii : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S)))) ≤
        A1 * (S4 * Erep * S) := by
      have h1 : (R3n * P2) * S ≤ S := by
        have h := mul_le_mul_of_nonneg_right hRP2 hS0
        linarith only [h]
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * S))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * S)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
        _ = A1 * (S4 * Erep * S) := by rw [hS4eq]; ring
    have hiii : A1 * ((s⁻¹) ^ (4 : ℕ) *
        (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) ≤
        (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
      have h2 : (R3n * Q3s) * (Sm3 * Gs) ≤ (9 * Q1s) * (Sm3 * Gs) :=
        mul_le_mul_of_nonneg_right hRQ3s (mul_nonneg hSm30 hGs0)
      have h2nn : (0 : ℝ) ≤ sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)) :=
        mul_nonneg hsiginv0 (mul_nonneg (mul_nonneg hR3n0 hQ3s0)
          (mul_nonneg hSm30 hGs0))
      have hinner : Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))) ≤
          (CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))) :=
        mul_le_mul hErepCap (mul_le_mul_of_nonneg_left h2 hsiginv0) h2nn
          (le_trans hErep0 hErepCap)
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)))))
          ≤ A1 * ((s⁻¹) ^ (4 : ℕ) *
              ((CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
        _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm3) * sig⁻¹ * Q1s * Gs) := by
            ring
        _ = (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
            rw [hS4eq, hS4Sm3]
    have hiv : A1 * ((s⁻¹) ^ (4 : ℕ) *
        (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs))))) ≤
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by
      have h2 : Sm2 * ((R3n * Q3s) * Hs) ≤ Sm2 * ((9 * Q1s) * Hs) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRQ3s hHs0) hSm20
      have h2nn : (0 : ℝ) ≤ Sm2 * ((R3n * Q3s) * Hs) :=
        mul_nonneg hSm20 (mul_nonneg (mul_nonneg hR3n0 hQ3s0) hHs0)
      have hinner : Erep * (Sm2 * ((R3n * Q3s) * Hs)) ≤
          (CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)) :=
        mul_le_mul hErepCap h2 h2nn (le_trans hErep0 hErepCap)
      calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs)))))
          = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (Sm2 * ((R3n * Q3s) * Hs)))) := by ring
        _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * ((CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
        _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm2) * Q1s * Hs) := by ring
        _ = (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by rw [hS4eq, hS4Sm2]
    -- the declined discard: the flat leg keeps `𝓔`.
    have hv : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * (R3n * Hn))))) ≤
        A1 * (S6 * Erep * R3n * Hn) := by
      have hprod : (s⁻¹) ^ (4 : ℕ) * Sm2 = S6 := by rw [hS4eq]; exact hS4Sm2
      refine le_of_eq ?_
      rw [← hprod]; ring
    linarith only [hi, hii, hiii, hiv, hv]
  exact ⟨hRQ3sn, hT1⟩

private theorem residueRouteOneErrorWeighted_comparisonBounds3 : ∀ (d : ℕ) (b0 cg A2 : ℝ)
      (_ : A2 = cg * (1944 : ℝ) * (b0 * (besovGagliardoConstant d * flushWindowConst d))) (_ : (0
        : ℝ) ≤ A2) (A3 : ℝ)
      (_ : A3 = interiorCorrectionConst d * flushWindowConst d) (_ : (0 : ℝ) ≤ A3) (s S Erep : ℝ)
      (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn Q3sn Q1s R3n S4 S7 S6 : ℝ) (_ : (0 : ℝ) ≤ X) (_ : (0 :
        ℝ) ≤ Gs)
      (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ) ≤ Hn) (_ : (0 : ℝ) ≤ S) (_ : (0 : ℝ) ≤ Q1s) (_ : (0 : ℝ) ≤
        R3n)
      (_ : (0 : ℝ) ≤ S4) (_ : (0 : ℝ) ≤ S7) (_ : (0 : ℝ) ≤ S6) (_ : (0 : ℝ) ≤ sig⁻¹)
      (_ : s⁻¹ ^ (6 : ℕ) = S6) (_ : S6 ≤ S7) (_ : s.rpow (-(1 / 2 : ℝ)) ≤ S7) (_ : R3n * Q3sn =
        Q1s),
      sig⁻¹ * R3n *
            (cg * ((1944 : ℝ) * s⁻¹ ^ (6 : ℕ) * (b0 * (besovGagliardoConstant d * Q3sn *
              (flushWindowConst d * Gs))))) ≤
          A2 * (S7 * sig⁻¹ * Q1s * Gs) ∧
        sig⁻¹ * R3n * (interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
          (flushWindowConst d * Gs)) ≤
            A3 * (S7 * sig⁻¹ * Q1s * Gs) ∧
          (0 : ℝ) ≤ S4 * Erep * X ∧
            (0 : ℝ) ≤ S4 * Erep * S ∧
              (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs ∧ (0 : ℝ) ≤ S6 * Q1s * Hs ∧ (0 : ℝ) ≤ S6 * Erep *
                R3n * Hn := by
  intro d b0 cg A2 hA2def hA2 A3 hA3def hA3 s S Erep hErep0 sig X Gs Hs Hn Q3sn Q1s R3n S4 S7 S6
    hX0 hGs0 hHs0 hHn0 hS0 hQ1s0 hR3n0 hS40 hS70 hS60 hsiginv0 hS6eq hS6le hQScle hRQ3sn
  have hT2 : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) ≤
      A2 * (S7 * sig⁻¹ * Q1s * Gs) := by
    have hrw : (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) =
        A2 * ((s⁻¹) ^ (6 : ℕ) * (sig⁻¹ * ((R3n * Q3sn) * Gs))) := by
      rw [hA2def]; ring
    rw [hrw, hRQ3sn, hS6eq]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Gs) :=
      mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hGs0)
    calc A2 * (S6 * (sig⁻¹ * (Q1s * Gs)))
        ≤ A2 * (S7 * (sig⁻¹ * (Q1s * Gs))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS6le hnn) hA2
      _ = A2 * (S7 * sig⁻¹ * Q1s * Gs) := by ring
  have hT3 : (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
        Q3sn * (flushWindowConst d * Gs)) ≤ A3 * (S7 * sig⁻¹ * Q1s * Gs) := by
    have hrw : (sig⁻¹ * R3n) * (interiorCorrectionConst d *
          Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * (flushWindowConst d * Gs)) =
        A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * ((R3n * Q3sn) * Gs))) := by
      rw [hA3def]; ring
    rw [hrw, hRQ3sn]
    have hnn : (0 : ℝ) ≤ sig⁻¹ * (Q1s * Gs) :=
      mul_nonneg hsiginv0 (mul_nonneg hQ1s0 hGs0)
    calc A3 * (Real.rpow s (-(1 / 2 : ℝ)) * (sig⁻¹ * (Q1s * Gs)))
        ≤ A3 * (S7 * (sig⁻¹ * (Q1s * Gs))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQScle hnn) hA3
      _ = A3 * (S7 * sig⁻¹ * Q1s * Gs) := by ring
  -- (h) the conclusion
  have hXterm : (0 : ℝ) ≤ S4 * Erep * X := mul_nonneg (mul_nonneg hS40 hErep0) hX0
  have hSterm : (0 : ℝ) ≤ S4 * Erep * S := mul_nonneg (mul_nonneg hS40 hErep0) hS0
  have hGterm : (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs :=
    mul_nonneg (mul_nonneg (mul_nonneg hS70 hsiginv0) hQ1s0) hGs0
  have hHsterm : (0 : ℝ) ≤ S6 * Q1s * Hs :=
    mul_nonneg (mul_nonneg hS60 hQ1s0) hHs0
  have hHnterm : (0 : ℝ) ≤ S6 * Erep * R3n * Hn :=
    mul_nonneg (mul_nonneg (mul_nonneg hS60 hErep0) hR3n0) hHn0
  exact ⟨hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩

private theorem residueRouteOneErrorWeighted_comparisonBounds7 :
    ∀ (d : ℕ) (CE : ℝ) (_ : (0 : ℝ) < CE) (CB : ℝ) (_ : (0 : ℝ) < CB) (M : ABKModel d) (s : ℝ)
      (_ : s ∈ Set.Icc ((64 : ℝ) * M.gamma) (1 : ℝ)) (_ : M.gamma ≤ (max CE CB)⁻¹ * Disorder.cstar
        M ^ (10 : ℕ))
      (_ m n : ℤ) (_ : n + (3 : ℤ) ≤ m) (z : Vec d) (_ : z ∈ openCubeSet (originCube d m)) (i :
        Fin d) (sigma : ℝ)
      (_ : sigma = (1 : ℝ) ∨ sigma = (-1 : ℝ)),
      s ≤ (1 : ℝ) ∧
        n + (2 : ℤ) ≤ m ∧
          M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
            M.gamma ≤ CB⁻¹ * Disorder.cstar M ^ (10 : ℕ) ∧
              flushSubCentre z m n i sigma ∈ openCubeSet (originCube d m) ∧
                (fun (y : Vec d) => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + (2 :
                  ℤ)) + y) ''
                      openCubeSet (originCube d (n + (2 : ℤ))) ⊆
                    (fun (y : Vec d) => z + y) '' openCubeSet (originCube d (n + (3 : ℤ))) ∩
                      openCubeSet (originCube d m) ∧
                  translateSet (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + (2 : ℤ)) - z)
                        (cubeSet (originCube d (n + (2 : ℤ)))) ⊆
                      cubeSet (originCube d (n + (3 : ℤ))) ∧
                    translateSet (flushSubCentre z m n i sigma - z) (cubeSet (originCube d n)) ⊆
                      cubeSet (originCube d (n + (3 : ℤ))) := by
  classical
  intro d CE hCEpos CB hCBpos M s hsrange hregime _ m n _ z hz i sigma hsigma
  have hs1 : s ≤ 1 := hsrange.2
  have hnm2 : n + 2 ≤ m := by omega
  have hregimeCE : M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans
      (mul_le_mul_of_nonneg_right ?_ (Even.pow_nonneg (by exact ⟨5, rfl⟩) _))
    have h1 := one_div_le_one_div_of_le hCEpos (le_max_left CE CB)
    rw [one_div, one_div] at h1
    exact h1
  have hregimeCB : M.gamma ≤ CB⁻¹ * Disorder.cstar M ^ (10 : ℕ) := by
    refine hregime.trans
      (mul_le_mul_of_nonneg_right ?_ (Even.pow_nonneg (by exact ⟨5, rfl⟩) _))
    have h1 := one_div_le_one_div_of_le hCBpos (le_max_right CE CB)
    rw [one_div, one_div] at h1
    exact h1
  have hxc : flushSubCentre z m n i sigma ∈ openCubeSet (originCube d m) :=
    flushSubCentre_mem_openCubeSet hnm2 z i hsigma
  have hcov : (fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
    image_add_flushCoveringCube_subset_anchorWindow hnm2 hz i hsigma
  have hPhinge : translateSet
      (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) - z)
      (cubeSet (originCube d (n + 2))) ⊆ cubeSet (originCube d (n + 3)) :=
    translateSet_cubeSet_flushCoveringCube_subset_anchorParent hnm2 hz i hsigma
  have hChinge : translateSet (flushSubCentre z m n i sigma - z)
      (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 3)) :=
    translateSet_cubeSet_flushSubCube_subset_anchorParent hnm2 hz i hsigma
  exact ⟨hs1, hnm2, hregimeCE, hregimeCB, hxc, hcov, hPhinge, hChinge⟩

private theorem residueRouteOneErrorWeighted_comparisonBounds8 :
    ∀ (d : ℕ) (CE KE kappa b0 cg A1 : ℝ) (_ : (0 : ℝ) ≤ A1)
      (_ : A1 = cg * (216 : ℝ) * (kappa * KE)) (A2 : ℝ) (_ : (0 : ℝ) ≤ A2)
      (_ : A2 = cg * (1944 : ℝ) * (b0 * (besovGagliardoConstant d * flushWindowConst d))) (A3
        : ℝ)
      (_ : (0 : ℝ) ≤ A3) (_ : A3 = interiorCorrectionConst d * flushWindowConst d) (s : ℝ)
        (_ : (0 : ℝ) < s) (n : ℤ)
      (_ : s ≤ (1 : ℝ)) (S : ℝ) (_ : (0 : ℝ) ≤ S) (Erep : ℝ) (_ : Erep ≤ CE * (1 / 2 :
        ℝ))
      (_ : (0 : ℝ) ≤ Erep) (sig : ℝ) (_ : (0 : ℝ) ≤ sig⁻¹) (X : ℝ) (_ : (0 : ℝ) ≤ X)
        (Gs : ℝ)
      (_ : (0 : ℝ) ≤ Gs) (Hs : ℝ) (_ : (0 : ℝ) ≤ Hs) (Hn : ℝ) (_ : (0 : ℝ) ≤ Hn) (P2 : ℝ)
      (_ : P2 = Real.rpow (3 : ℝ) (-(↑(n + (2 : ℤ)) : ℝ))) (Q3s : ℝ)
        (_ : (0 : ℝ) ≤ Q3s)
      (_ : Q3s = Real.rpow (3 : ℝ) (s * (↑(n + (2 : ℤ)) : ℝ))) (Q3sn : ℝ)
      (_ : Q3sn = Real.rpow (3 : ℝ) (s * (↑n : ℝ))) (Q1s : ℝ) (_
        : (0 : ℝ) ≤ Q1s)
      (_ : Q1s = Real.rpow (3 : ℝ) (((1 : ℝ) + s) * (↑n : ℝ))) (R3n : ℝ) (_ : (0 : ℝ) ≤ R3n)
      (_ : R3n = Real.rpow (3 : ℝ) (↑n : ℝ)) (S4 : ℝ) (_ : (0 : ℝ) ≤ S4)
      (_ : S4 = s.rpow (-4 : ℝ)) (S7 : ℝ) (_ : (0 : ℝ) ≤ S7) (_ :
        S7 = s.rpow (-7 : ℝ))
      (S6 : ℝ) (_ : (0 : ℝ) ≤ S6) (_ : S6 = s.rpow (-6 : ℝ)) (Sm3 : ℝ)
      (_ : (0 : ℝ) ≤ Sm3) (_ : Sm3 = s.rpow (-3 : ℝ)) (Sm2 : ℝ)
        (_ : (0 : ℝ) ≤ Sm2)
      (_ : Sm2 = s.rpow (-2 : ℝ)) (_ : sig⁻¹ * sig = (1 : ℝ)),
      sig⁻¹ * R3n *
            (cg *
              ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
                (kappa * KE * Erep *
                  (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                    Sm2 * (sig * Hn))))) ≤
          A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
                (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
              A1 * (S6 * Erep * R3n * Hn) +
            A1 * (S4 * Erep * S) ∧
        sig⁻¹ * R3n *
              (cg * ((1944 : ℝ) * s⁻¹ ^ (6 : ℕ) * (b0 * (besovGagliardoConstant d * Q3sn *
                (flushWindowConst d * Gs))))) ≤
            A2 * (S7 * sig⁻¹ * Q1s * Gs) ∧
          sig⁻¹ * R3n * (interiorCorrectionConst d * s.rpow (-(1 / 2 : ℝ)) * Q3sn *
            (flushWindowConst d * Gs)) ≤
              A3 * (S7 * sig⁻¹ * Q1s * Gs) ∧
            (0 : ℝ) ≤ S4 * Erep * X ∧
              (0 : ℝ) ≤ S4 * Erep * S ∧
                (0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs ∧ (0 : ℝ) ≤ S6 * Q1s * Hs ∧ (0 : ℝ) ≤ S6 * Erep *
                  R3n * Hn := by
  classical
  intro d CE KE kappa b0 cg A1 hA1 hA1def A2 hA2 hA2def A3 hA3 hA3def s hs
    n hs1 S hS0 Erep hErepCap hErep0 sig hsiginv0 X hX0 Gs hGs0 Hs hHs0 Hn hHn0 P2 hP2def
      Q3s hQ3s0 hQ3sdef Q3sn hQ3sndef Q1s hQ1s0 hQ1sdef R3n hR3n0
        hR3ndef S4 hS40 hS4def S7 hS70 hS7def S6 hS60 hS6def Sm3
          hSm30 hSm3def Sm2 hSm20 hSm2def hsinv
  have hS4eq : (s⁻¹) ^ (4 : ℕ) = S4 := by
    rw [hS4def, inv_pow_eq_rpow_neg hs 4]
    congr 1
  have hS6eq : (s⁻¹) ^ (6 : ℕ) = S6 := by
    rw [hS6def, inv_pow_eq_rpow_neg hs 6]
    congr 1
  have hS4Sm3 : S4 * Sm3 = S7 := by
    rw [hS4def, hSm3def, hS7def]
    exact rpow_s_four_mul_three hs
  have hS4Sm2 : S4 * Sm2 = S6 := by
    rw [hS4def, hSm2def, hS6def]
    exact rpow_neg_four_mul_neg_two hs
  have hS6le : S6 ≤ S7 := by
    rw [hS6def, hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  have hQScle : Real.rpow s (-(1 / 2 : ℝ)) ≤ S7 := by
    rw [hS7def]
    exact rpow_le_rpow_neg_seven hs hs1 (by norm_num)
  obtain ⟨hRQ3sn, hT1⟩ :=
    (show (R3n * Q3sn = Q1s) ∧ ((sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) ≤
      A1 * (S4 * Erep * X) + (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        A1 * (S6 * Erep * R3n * Hn) + A1 * (S4 * Erep * S)) from
      @residueRouteOneErrorWeighted_comparisonBounds2 (CE) (KE) (kappa) (cg) (A1) (hA1def) (hA1)
        (s) (hs) (n) (hs1) (S) (Erep) (hErepCap) (hErep0) (sig) (X) (Gs) (Hs) (Hn) (P2) (hP2def)
          (Q3s) (hQ3sdef) (Q3sn) (hQ3sndef) (Q1s) (hQ1sdef) (R3n) (hR3ndef) (S4) (S7) (S6) (Sm3)
            (Sm2) (hX0) (hGs0) (hHs0) (hS0) (hQ3s0) (hR3n0) (hSm30) (hSm20) (hsiginv0) (hsinv)
              (hS4eq) (hS4Sm3) (hS4Sm2))
  obtain ⟨hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩ :=
    (show ((sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) ≤
      A2 * (S7 * sig⁻¹ * Q1s * Gs)) ∧ ((sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s
        (-(1 / 2 : ℝ)) *
        Q3sn * (flushWindowConst d * Gs)) ≤ A3 * (S7 * sig⁻¹ * Q1s * Gs)) ∧ ((0 : ℝ) ≤ S4 * Erep *
          X) ∧ ((0 : ℝ) ≤ S4 * Erep * S) ∧ ((0 : ℝ) ≤ S7 * sig⁻¹ * Q1s * Gs) ∧ ((0 : ℝ) ≤ S6 * Q1s
            * Hs) ∧ ((0 : ℝ) ≤ S6 * Erep * R3n * Hn) from
      @residueRouteOneErrorWeighted_comparisonBounds3 (d) (b0) (cg) (A2)
        (hA2def) (hA2) (A3) (hA3def) (hA3) (s) (S) (Erep) (hErep0) (sig) (X) (Gs) (Hs) (Hn) (Q3sn)
          (Q1s) (R3n) (S4) (S7) (S6) (hX0) (hGs0) (hHs0) (hHn0) (hS0) (hQ1s0) (hR3n0) (hS40)
            (hS70) (hS60) (hsiginv0) (hS6eq) (hS6le) (hQScle) (hRQ3sn))
  exact ⟨hT1, hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩

/-- **Route 1, composed at the flush sub-cube — the error-weighted legs.**

The harmonic-approximation residue at `K'`, priced on the five canonical legs
with the good-event error `𝓔` carried explicitly.  As in `AssemblyComposedErrorWeighted`,
the monotone discard is declined on the flat `∇h` row, so that leg reads
`s^{-6}·𝓔·3^n·‖∇h‖_{L²(W')}`. -/
theorem exists_flushResidue_route1_composed_errorWeighted (d : ℕ) [NeZero d] :
    ∃ C Cfin : ℝ, 0 < C ∧ 0 < Cfin ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ z : Vec d,
          z ∈ openCubeSet (originCube d m) →
          ∀ (i : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) →
            wellPlacedHalfGap m (n + 2) < σ * z i →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (Support.cgEllipLowerConstant d) (n + 3) z
                  ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d) (S : ℝ),
                  Support.IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                  MemLp g 2 (Support.normalizedVolumeMeasureOn
                    (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (Support.normalizedGagliardoMeasureOn
                      (openCubeSet (originCube d m))) →
                  |volumeAverage ((fun y => wellPlacedCentre z m (n + 2) + y) ''
                      openCubeSet (originCube d (n + 2)))
                      (fun y => u.toFun y - hdat.toFun y)| ≤ S →
                  ∀ (v : H1Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n)))
                    (w : H10Function ((fun y => flushSubCentre z m n i σ + y) ''
                      openCubeSet (originCube d n))),
                    Support.IsWeaklyHarmonicOn
                        ((fun y => flushSubCentre z m n i σ + y) ''
                          openCubeSet (originCube d n)) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                      (eLpNorm (fun y => u.toFun y - v.toFun y) 2
                        (Support.normalizedVolumeMeasureOn
                          ((fun y => flushSubCentre z m n i σ + y) ''
                            openCubeSet (originCube d n)))).toReal ≤
                        Cfin *
                          (Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              (eLpNorm (fun y => u.toFun y -
                                  volumeAverage ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))) u.toFun) 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(7 : ℝ)) *
                              ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s g).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                              Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) *
                              (Support.normalizedGagliardoESeminormOn
                                ((((fun y' => z + y') ''
                                    openCubeSet (originCube d (n + 3))) ∩
                                  openCubeSet (originCube d m))) s hdat.grad).toReal +
                            Real.rpow s (-(6 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) *
                              Real.rpow (3 : ℝ) (n : ℝ) *
                              (eLpNorm hdat.grad 2
                                (Support.normalizedVolumeMeasureOn
                                  ((((fun y' => z + y') ''
                                      openCubeSet (originCube d (n + 3))) ∩
                                    openCubeSet (originCube d m))))).toReal +
                            Real.rpow s (-(4 : ℝ)) *
                              Support.fluxCorrectedErrorRepresentative M L (n + 3)
                                ⟨s / 8, by linarith only [hs]⟩
                                (Cutoff.translateCutoffSample z omega) * S) := by
  classical
  obtain ⟨CE, hCEpos, hCE, CB, KE, hCBpos, hEnergyLeg, hkappadef, hkappa, he0def, hk0def, hb0def,
    hb0, hcg, hA1def, hA1, hA2def, hA2, hA3def, hA3, hCE2, hCE3⟩ :=
    @residueRouteOne_comparisonBounds6 (d) (by infer_instance)
  set kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3 with hkappadef
  set e0 : ℝ := kappa * (CE * (1 / 2)) with he0def
  set k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1) with hk0def
  set b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0 with hb0def
  set cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d with hcgdef
  set A1 : ℝ := cg * 216 * (kappa * KE) with hA1def
  set A2 : ℝ := cg * 1944 * (b0 * (besovGagliardoConstant d * flushWindowConst d))
    with hA2def
  set A3 : ℝ := interiorCorrectionConst d * flushWindowConst d with hA3def
  refine ⟨max CE CB,
    A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1,
    lt_of_lt_of_le hCEpos (le_max_left _ _),
    add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg hA1 hCE2) hCE3) hA2) hA3)
      zero_lt_one, ?_⟩
  intro M s hsrange hregime hsmall hs L m n hmL hnm z hz i sigma hsigma hover
  obtain ⟨hs1, hnm2, hregimeCE, hregimeCB, hxc, hcov, hPhinge, hChinge⟩ :=
    (show (s ≤ 1) ∧ (n + 2 ≤ m) ∧ (M.gamma ≤ CE⁻¹ * Disorder.cstar M ^ (10 : ℕ)) ∧ (M.gamma ≤ CB⁻¹
      * Disorder.cstar M ^ (10 : ℕ)) ∧ (flushSubCentre z m n i sigma ∈ openCubeSet (originCube d
        m)) ∧ ((fun y => wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) ∧ (translateSet
      (wellPlacedCentre (flushSubCentre z m n i sigma) m (n + 2) - z)
      (cubeSet (originCube d (n + 2))) ⊆ cubeSet (originCube d (n + 3))) ∧ (translateSet
        (flushSubCentre z m n i sigma - z)
      (cubeSet (originCube d n)) ⊆ cubeSet (originCube d (n + 3))) from
      @residueRouteOneErrorWeighted_comparisonBounds7 (d) (CE) (hCEpos) (CB) (hCBpos) (M) (s)
        (hsrange) (hregime) (L) (m) (n) (hnm) (z) (hz) (i) (sigma) (hsigma))
  filter_upwards [hCE M s hsrange hregimeCE hsmall hs n z,
    hEnergyLeg M s hsrange hregimeCB hsmall hs L m n hmL hnm
      (flushSubCentre z m n i sigma) z hxc hcov hPhinge,
    ae_coarseGrainingErrorAtDepth_rebased_le_representative_gapThree M L n z hs hs1,
    ae_forceBracket_rebased_le_gapThree M L n z hs hs1] with omega hcapE hEnLeg herrD hbrk
  intro hmem u hdat g S hsol hgL2 hgW hhW hmean v w hharm hval hgrad
  obtain ⟨hsubx, hErepCap, hErep0, hsig, hP2def, hQ3sdef, hxf, hQ3sndef, hQ1sdef, hR3ndef, hS4def,
    hS7def, hS6def, hSm3def, hSm2def, hX0, hGs0, hHs0, hHn0, hS0, hQ3s0, hQ3sn0, hQ1s0, hR3n0,
      hS40, hS70, hS60, hSm30, hSm20, hsiginv0, hbrkCap, hET, hGbes, hGbes0, hYchild3⟩ :=
    @residueRouteOne_comparisonBounds4 (d) (by infer_instance) (CE) (KE) (hkappadef)
      (hkappa) (he0def) (hk0def) (hb0def) (M) (s) (hs) (L) (m) (n) (hmL) (hnm) (z) (hz) (i)
        (sigma) (hsigma) (hover) (hs1) (hnm2) (hChinge) (omega) (hcapE) (hEnLeg) (herrD) (hbrk)
          (hmem) (u) (hdat) (g) (S) (hsol) (hgL2) (hgW) (hhW) (hmean) (v) (w) (hharm) (hval) (hgrad)
  set Erep : ℝ := Support.fluxCorrectedErrorRepresentative M L (n + 3)
    ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) with hErepdef
  set Eb : ℝ := Real.sqrt (offGridStabilityConst d (s / 6) (s / 8)) *
    ((3 : ℝ) ^ (3 * (s / 8)) * Erep) with hEbdef
  set sig : ℝ := (Annealed.sigmaBar M (n + 3) : ℝ) with hsigdef
  set X : ℝ := (eLpNorm (fun y => u.toFun y -
      volumeAverage ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) u.toFun) 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hXdef
  set Gs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s g).toReal with hGsdef
  set Hs : ℝ := (Support.normalizedGagliardoESeminormOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) s hdat.grad).toReal with hHsdef
  set Hn : ℝ := (eLpNorm hdat.grad 2
      (Support.normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))))).toReal with hHndef
  set Ychild : ℝ := (Support.normalizedGagliardoESeminormOn
      ((fun y => flushSubCentre z m n i sigma + y) ''
        openCubeSet (originCube d n)) s g).toReal with hYchilddef
  set Lhs : ℝ := (eLpNorm (fun y => u.toFun y - v.toFun y) 2
      (Support.normalizedVolumeMeasureOn
        ((fun y => flushSubCentre z m n i sigma + y) ''
          openCubeSet (originCube d n)))).toReal with hLhsdef
  set P2 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hP2def
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set Q3sn : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ)) with hQ3sndef
  set Q1s : ℝ := Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) with hQ1sdef
  set R3n : ℝ := Real.rpow (3 : ℝ) ((n : ℝ)) with hR3ndef
  set S4 : ℝ := Real.rpow s (-(4 : ℝ)) with hS4def
  set S7 : ℝ := Real.rpow s (-(7 : ℝ)) with hS7def
  set S6 : ℝ := Real.rpow s (-(6 : ℝ)) with hS6def
  set Sm3 : ℝ := Real.rpow s (-(3 : ℝ)) with hSm3def
  set Sm2 : ℝ := Real.rpow s (-(2 : ℝ)) with hSm2def
  have hFT : coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + flushSubCentre z m n i sigma)) ≤
      b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)) := by
    rw [coarseGrainingForceTerm]
    refine mul_le_mul hbrkCap ?_ hGbes0 hb0
    refine hGbes.trans ?_
    exact mul_le_mul_of_nonneg_left hYchild3
      (mul_nonneg (besovGagliardoConstant_nonneg d) hQ3sn0)
  -- (e) the frame division
  set ET : ℝ := coarseGrainingEnergyTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3)
      (H1Function.untranslate (flushSubCentre z m n i sigma)
        (u.restrict (isOpen_translateSet_openCubeSet
          (flushSubCentre z m n i sigma) n) hsubx))
    with hETdef
  set FT : ℝ := coarseGrainingForceTerm (originCube d n)
      (parentRebasedFamily M L (n + 3) (flushSubCentre z m n i sigma) z omega)
      (scalarComparator (Annealed.sigmaBar M (n + 3)).2) (s / 3) s
      (fun y => -g (y + flushSubCentre z m n i sigma))
    with hFTdef
  have hW1 : cubeBesovScaleWeight (1 : ℝ) (originCube d n) =
      Real.rpow (3 : ℝ) (-(n : ℝ)) := by
    have h := cubeBesovScaleWeight_neg_originCube (d := d) n (-1)
    rw [neg_neg] at h
    rw [h]
    congr 1
    ring
  rw [hW1] at hxf
  obtain ⟨hfac0, hsinv, hstep, hleg1, hleg2, hleg3⟩ :=
    (show ((0 : ℝ) ≤ sig⁻¹ * R3n) ∧ (sig⁻¹ * sig = 1) ∧ (Lhs ≤ (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) * ET + 1944 * (s⁻¹) ^ (6 : ℕ) * FT) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild)) ∧ (216 * (s⁻¹) ^
          (4 : ℕ) * ET ≤
      216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn)))) ∧ (1944 * (s⁻¹) ^ (6 : ℕ) * FT ≤
      1944 * (s⁻¹) ^ (6 : ℕ) *
        (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)))) ∧
          (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn * Ychild ≤
      interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
        (flushWindowConst d * Gs)) from
      @residueRouteOne_comparisonBounds5 (d) (by infer_instance) (CE) (KE) (M) (s)
        (hs) (L) (m) (n) (z) (i) (sigma) (omega) (u) (hdat) (g) (S) (v) (hsubx) (hsig) (hsiginv0)
          (hYchild3) (hQ3sn0) (hR3n0) (hET) (hFT) (hxf))
  have hmono := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hleg1 hleg2) hcg) hleg3
  clear_value Lhs X Gs Hs Hn Ychild ET FT Erep Eb sig P2 Q3s Q3sn Q1s R3n S4 S7 S6
    Sm3 Sm2 A3 A2 A1 cg b0 k0 e0 kappa
  -- (g) the regrouping
  obtain ⟨hT1, hT2, hT3, hXterm, hSterm, hGterm, hHsterm, hHnterm⟩ :=
    @residueRouteOneErrorWeighted_comparisonBounds8 (d) (CE) (KE) (kappa) (b0)
      (cg) (A1) (hA1) (hA1def) (A2) (hA2) (hA2def) (A3) (hA3) (hA3def) (s) (hs) (n) (hs1) (S)
        (hS0) (Erep) (hErepCap) (hErep0) (sig)
          (hsiginv0) (X) (hX0) (Gs) (hGs0) (Hs) (hHs0) (Hn) (hHn0) (P2) (hP2def)
            (Q3s) (hQ3s0) (hQ3sdef) (Q3sn) (hQ3sndef) (Q1s) (hQ1s0) (hQ1sdef) (R3n) (hR3n0)
              (hR3ndef) (S4) (hS40) (hS4def) (S7) (hS70) (hS7def) (S6) (hS60) (hS6def) (Sm3)
                (hSm30) (hSm3def) (Sm2) (hSm20) (hSm2def) (hsinv)
  refine hstep.trans (le_trans (mul_le_mul_of_nonneg_left hmono hfac0) ?_)
  have hdistrib : (sig⁻¹ * R3n) *
      (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
            (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
              Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))) +
          1944 * (s⁻¹) ^ (6 : ℕ) *
            (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs)))) +
        interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) * Q3sn *
          (flushWindowConst d * Gs)) =
      (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
          (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
            Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) +
        (sig⁻¹ * R3n) * (cg * (1944 * (s⁻¹) ^ (6 : ℕ) *
          (b0 * (besovGagliardoConstant d * Q3sn * (flushWindowConst d * Gs))))) +
        (sig⁻¹ * R3n) * (interiorCorrectionConst d * Real.rpow s (-(1 / 2 : ℝ)) *
          Q3sn * (flushWindowConst d * Gs)) := by ring
  rw [hdistrib]
  have habs : A1 * (S4 * Erep * X) +
        (9 * (CE * (1 / 2)) * A1 + A2 + A3) * (S7 * sig⁻¹ * Q1s * Gs) +
        (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) +
        A1 * (S6 * Erep * R3n * Hn) + A1 * (S4 * Erep * S) ≤
      (A1 + 9 * (CE * (1 / 2)) * A1 + CE * (1 / 2) * A1 + A2 + A3 + 1) *
        (S4 * Erep * X + S7 * sig⁻¹ * Q1s * Gs + S6 * Q1s * Hs +
          S6 * Erep * R3n * Hn + S4 * Erep * S) :=
    five_leg_bound le_rfl (by linarith only [hCE2, hCE3, hA2, hA3])
      (by linarith only [hA1, hCE3]) (by linarith only [hA1, hCE3, hA2, hA3])
      (by linarith only [hCE2, hCE3, hA2, hA3])
      (by linarith only [hCE2, hCE3, hA2, hA3]) hXterm hGterm hHsterm hHnterm hSterm
  linarith only [hT1, hT2, hT3, habs]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
