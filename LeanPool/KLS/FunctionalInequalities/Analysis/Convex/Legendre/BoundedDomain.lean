/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Extended-real potentials with bounded effective domain and their conjugates

For an extended-real potential `φ` on a real inner-product space whose effective domain lies in
`closedBall 0 L`:
`closedBallCap φ L` is `φ` on the ball and `⊤` outside, lower semicontinuous with `φ`
(`closedBallCap_lowerSemicontinuous`); in finite dimension a proper lower semicontinuous `φ` attains
a real minimum
(`exists_real_global_minimum_of_bounded_domain`); a real floor `m` gives `φ* x ≤ L‖x‖ − m`
(`legendre_le_of_real_lower_bound`), so the conjugate is finite everywhere
(`legendre_finite_of_bounded_domain`); a real
representative `ψ` of a finite conjugate is convex (`real_convexOn_legendre`) and `L`-Lipschitz
(`lipschitzWith_real_legendre`), and satisfies the real Fenchel inequality at finite points
(`real_legendre_fenchel`).
Infinite values are excluded before every real conversion. Used by the bounded-source producer of
`KLS/CEK/BoundedPrimal.lean`.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace

open FunctionalInequalities
open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Restrict an extended-real potential to the closed ball, assigning top outside. -/
noncomputable def closedBallCap (φ : E → EReal) (L : NNReal) : E → EReal := by
  classical
  exact fun x => if x ∈ closedBall (0 : E) (L : ℝ) then φ x else ⊤

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The top sublevel is the whole ambient space; every other sublevel is an
intersection with the closed ball. This helper honestly assumes input LSC. -/
theorem closedBallCap_lowerSemicontinuous
    (φ : E → EReal) (L : NNReal)
    (hφ : LowerSemicontinuous φ) : LowerSemicontinuous (closedBallCap φ L) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ⊤
  · subst r
    have hs : closedBallCap φ L ⁻¹' Iic (⊤ : EReal) = (univ : Set E) := by
      ext x
      simp
    rw [hs]
    exact isClosed_univ
  · have hs : closedBallCap φ L ⁻¹' Iic r =
        closedBall (0 : E) (L : ℝ) ∩ (φ ⁻¹' Iic r) := by
      ext x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simp [closedBallCap, hx]
      · have hnr : ¬ (⊤ : EReal) ≤ r := by
          intro h
          exact hr (top_unique h)
        simp [closedBallCap, hx, hnr]
    rw [hs]
    exact isClosed_closedBall.inter
      (lowerSemicontinuous_iff_isClosed_preimage.mp hφ r)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A proper LSC potential with bounded effective domain attains a finite real
minimum. The real conversion is made only after excluding both infinities. -/
theorem exists_real_global_minimum_of_bounded_domain
    (φ : E → EReal) (L : NNReal)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hlsc : LowerSemicontinuous φ)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) :
    ∃ a ∈ closedBall (0 : E) (L : ℝ), ∃ m : ℝ,
      φ a = (m : EReal) ∧ ∀ y, (m : EReal) ≤ φ y := by
  classical
  obtain ⟨z, hz⟩ := hfinite
  have hzB : z ∈ closedBall (0 : E) (L : ℝ) := hdom z hz
  obtain ⟨a, haB, haMin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn
      (show (closedBall (0 : E) (L : ℝ)).Nonempty from ⟨z, hzB⟩)
      (isCompact_closedBall (0 : E) (L : ℝ))
      (hlsc.lowerSemicontinuousOn (closedBall (0 : E) (L : ℝ)))
  change ∀ y ∈ closedBall (0 : E) (L : ℝ), φ a ≤ φ y at haMin
  have haTop : φ a ≠ ⊤ := by
    intro hat
    have h := haMin z hzB
    rw [hat] at h
    exact hz (top_unique h)
  have haReal : ((φ a).toReal : EReal) = φ a :=
    EReal.coe_toReal haTop (hbot a)
  refine ⟨a, haB, (φ a).toReal, haReal.symm, ?_⟩
  intro y
  rw [haReal]
  by_cases hy : φ y = ⊤
  · rw [hy]
    exact le_top
  · exact haMin y (hdom y hy)

section BoundedDomainConjugates

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- A real floor and bounded effective domain give a finite upper bound for the
actual extended-real Legendre transform, at every primal point. -/
theorem legendre_le_of_real_lower_bound
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) (x : E) :
    legendre φ x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by
  classical
  unfold legendre
  refine iSup_le ?_
  intro y
  by_cases hy : φ y = ⊤
  · simp [hy, sub_eq_add_neg]
  · have hyReal : ((φ y).toReal : EReal) = φ y :=
      EReal.coe_toReal hy (hbot y)
    have hm : m ≤ (φ y).toReal := by
      have hm' : (m : EReal) ≤ ((φ y).toReal : EReal) := by
        rw [hyReal]
        exact hfloor y
      exact_mod_cast hm'
    have hynorm : ‖y‖ ≤ (L : ℝ) := by
      simpa [mem_closedBall] using hdom y hy
    have hinner : inner ℝ y x ≤ (L : ℝ) * ‖x‖ :=
      (real_inner_le_norm y x).trans
        (mul_le_mul_of_nonneg_right hynorm (norm_nonneg x))
    calc
      (inner ℝ y x : EReal) - φ y =
          ((inner ℝ y x - (φ y).toReal : ℝ) : EReal) := by
            rw [EReal.coe_sub, hyReal]
      _ ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by
        exact_mod_cast (sub_le_sub hinner hm)

/-- Properness excludes bottom for the actual conjugate, and the bounded-slope
upper bound excludes top. No conversion of an infinite value is used. -/
theorem legendre_finite_of_bounded_domain
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) :
    ∀ x, legendre φ x ≠ ⊤ ∧ legendre φ x ≠ ⊥ := by
  intro x
  refine ⟨?_, (convexPotential_legendre φ hfinite).1 x⟩
  intro htop
  have hu := legendre_le_of_real_lower_bound φ L m hbot hdom hfloor x
  rw [htop] at hu
  exact (not_le_of_gt (EReal.coe_lt_top ((L : ℝ) * ‖x‖ - m))) hu

/-- Transfer the actual conjugate's convex epigraph to a real representative.
The finite equality, rather than any global algebraic rule for `toReal`, is used. -/
theorem real_convexOn_legendre
    (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
    ConvexOn ℝ (univ : Set E) ψ := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h : legendre q (a • x + b • y) ≤
      ((a * ψ x + b * ψ y : ℝ) : EReal) :=
    (convex_epigraph_legendre q)
      (show (x, ψ x) ∈ {p : E × ℝ | legendre q p.1 ≤ (p.2 : EReal)}
        from (hψ x).le)
      (show (y, ψ y) ∈ {p : E × ℝ | legendre q p.1 ≤ (p.2 : EReal)}
        from (hψ y).le)
      ha hb hab
  rw [hψ (a • x + b • y)] at h
  simpa only [smul_eq_mul] using (EReal.coe_le_coe_iff.mp h)

/-- Bounded effective-domain slopes control the EReal supremum itself.
Only finite intercepts are converted to real numbers. -/
theorem lipschitzWith_real_legendre
    (q : E → EReal) (L : NNReal) (ψ : E → ℝ)
    (hbot : ∀ y, q y ≠ ⊥)
    (hdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
    LipschitzWith L ψ := by
  classical
  apply LipschitzWith.of_le_add_mul L
  intro x z
  apply EReal.coe_le_coe_iff.mp
  rw [← hψ x]
  unfold legendre
  refine iSup_le ?_
  intro y
  by_cases hy : q y = ⊤
  · simp only [hy, EReal.sub_top, bot_le]
  · have hyReal : ((q y).toReal : EReal) = q y :=
      EReal.coe_toReal hy (hbot y)
    have hterm : ((inner ℝ y z - (q y).toReal : ℝ) : EReal) ≤
        (ψ z : EReal) := by
      rw [EReal.coe_sub, hyReal, ← hψ z]
      exact le_iSup (fun w : E => (inner ℝ w z : EReal) - q w) y
    have hz : inner ℝ y z - (q y).toReal ≤ ψ z :=
      EReal.coe_le_coe_iff.mp hterm
    have hynorm : ‖y‖ ≤ (L : ℝ) := by
      simpa [mem_closedBall] using hdom y hy
    have hinner : inner ℝ y (x - z) ≤ (L : ℝ) * dist x z := by
      calc
        inner ℝ y (x - z) ≤ ‖y‖ * ‖x - z‖ :=
          real_inner_le_norm y (x - z)
        _ ≤ (L : ℝ) * ‖x - z‖ :=
          mul_le_mul_of_nonneg_right hynorm (norm_nonneg (x - z))
        _ = (L : ℝ) * dist x z := by rw [dist_eq_norm]
    rw [inner_sub_right] at hinner
    calc
      (inner ℝ y x : EReal) - q y =
          ((inner ℝ y x - (q y).toReal : ℝ) : EReal) := by
            rw [EReal.coe_sub, hyReal]
      _ ≤ ((ψ z + (L : ℝ) * dist x z : ℝ) : EReal) := by
        apply EReal.coe_le_coe_iff.mpr
        linarith only [hz, hinner]

/-- Real Fenchel inequality at any genuinely finite dual point, retaining the
actual extended-real conjugate rather than replacing it by an unrelated primal. -/
theorem real_legendre_fenchel
    (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal))
    (y : E) (r : ℝ) (hy : q y = (r : EReal)) (x : E) :
    inner ℝ y x - r ≤ ψ x := by
  have h : (inner ℝ y x : EReal) - q y ≤ legendre q x :=
    le_iSup (fun z : E => (inner ℝ z x : EReal) - q z) y
  rw [hy, hψ x, ← EReal.coe_sub] at h
  exact EReal.coe_le_coe_iff.mp h

end BoundedDomainConjugates

end FunctionalInequalities.Analysis
