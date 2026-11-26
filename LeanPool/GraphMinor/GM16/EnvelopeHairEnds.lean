/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM16.EnvelopeExitPaths
import LeanPool.GraphMinor.GM16.EnvelopeHairMetric
import LeanPool.GraphMinor.GM11.Section88

/-!
# Moving the hair centres to the envelope boundaries

Choose the first exit path for every centre. Its new end survives
clearing. Distinct ends lie on disjoint zone boundaries, so they
are distinct. The compression and the two radius bounds preserve
the required separation. This proves the family version of XVI
(7.1), Claim (5), pages 69–70.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14 GraphMinor.GM15
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The exit ends of the centres are distinct, remain separated,
and have paths meeting the cleared drawing just in their new ends. -/
theorem exists_envelope_hair_ends (hS : IsClosedSurface S) {H : Drawing S}
    {θ γ θ₂ : ℕ} {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {Y : Set S} {Λ : S → Set S} {loss : ℕ}
    (hEnv : IsEnvelope H d Y γ Λ)
    (hComp : IsLambdaCompression H (clearEnvelopeDrawing H Y Λ) θ loss T T' d d')
    (hSep : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → θ ≤ d {y} {z})
    (hBudget : θ₂ + 2 * γ + loss ≤ θ) :
    ∃ (p : Y → S) (P : Y → Drawing S),
      (∀ y, p y ∈ (clearEnvelopeDrawing H Y Λ).V ∧ p y ∈ subBd (Λ y.val) ∧
        (P y).IsPathBetween y.val (p y) ∧ (P y).IsSubdrawing H ∧
        (P y).U ⊆ closure (Λ y.val) ∧
        (P y).V ∩ (clearEnvelopeDrawing H Y Λ).V = {p y} ∧ d {y.val} {p y} ≤ γ) ∧
      Function.Injective p ∧ Pairwise (fun y z => θ₂ ≤ d' {p y} {p z}) := by
  classical
  have hExit := fun y : Y => exists_envelope_centre_exit hS hComp.hasMetric.1.1 hEnv y.prop
  choose p hp hBd P hPath hPH hPU hInter hDist using hExit
  have hInj : Function.Injective p := by
    intro y z heq
    apply Subtype.ext
    by_contra hyz
    exact (hEnv.2.2.1 y.val y.prop z.val z.prop hyz).notMem_of_mem_left
      (hBd y).1 (heq.symm ▸ (hBd z).1)
  refine ⟨p, P, fun y => ⟨hp y, hBd y, hPath y, hPH y, hPU y, hInter y, hDist y⟩, hInj, ?_⟩
  intro y z hyz
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  exact envelope_boundary_distance hS interSet_isSub hComp (hEnv.1 y.prop) (hEnv.1 z.prop)
    (hp y) (hp z) (hSep y.val y.prop z.val z.prop hyz') (hDist y) (hDist z) hBudget

end GraphMinor.GM16
