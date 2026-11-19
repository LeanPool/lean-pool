/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Extremum
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.AffineMaximum
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Attainment of the Legendre supremum and the gradient of the conjugate

For a proper (`ProperPotential`) extended-real `φ` on a finite-dimensional real inner-product space
(dimension zero
included) and a point `y` in the interior of the finite domain `{q | φ* q ≠ ⊤}` of its Legendre
transform `φ*`:

* every maximizing affine term is the dual gradient: if `⟪z, y⟫ − φ z = φ* y` and `q ↦ (φ*
  q).toReal` is differentiable
  at `y`, then `z = ∇(φ*)(y)` (`conjugate_maximizer_eq_gradient`);
* the tilted primal grows linearly, `a‖z‖ − b ≤ φ z − ⟪z, y⟫` with `a > 0`
  (`exists_coercive_tilt_of_mem_interior_legendre_domain`),
  so `z ↦ ⟪z, y⟫ − φ z` has the data of `exists_finite_maximum_of_upperSemicontinuous_linear_decay`
  when `φ` is lower
  semicontinuous (`tiltedObjective_data`);
* hence the supremum is attained, and the maximizer is the dual gradient when the conjugate is
  differentiable
  (`exists_legendre_maximizer_with_gradient_identity`).

No convexity, differentiability, nonnegativity or global finiteness of `φ` is assumed. Pointwise
prerequisites of
Cordero-Erausquin–Klartag, arXiv:1304.0630v1, (42) (Berman–Berndtsson, arXiv:1207.6128v1, Lemma 2.7
/ Appendix 6); not the
integral first variation, the source moment map or its push-forward.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

section MaximizerGradient

open Set

/-- Identification part of the dual-differentiability argument in
Berman--Berndtsson arXiv:1207.6128v1 Lemma 2.7 / Appendix 6, needed for
CEK arXiv:1304.0630v1 first variation. Every actual maximizing affine term
equals the actual dual gradient. The primal need not be differentiable,
convex, nonnegative or finite everywhere. Existence of a maximizing point
and the envelope derivative remain separate results. -/
theorem conjugate_maximizer_eq_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    {y : E} (hy : y ∈ interior {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ
      (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) :
    ∀ z : E,
      (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y →
      z = gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y := by
    intro z hz
    let F : E → ℝ :=
      fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal
    let S : Set E :=
      {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}
    have hyS : y ∈ interior S := by
      simpa [S] using hy
    have hy_mem : y ∈ S := interior_subset hyS
    have hy_top :
        FunctionalInequalities.Analysis.legendre φ y ≠ ⊤ := by
      simpa [S] using hy_mem
    have hy_bot :
        FunctionalInequalities.Analysis.legendre φ y ≠ ⊥ :=
      FunctionalInequalities.Analysis.legendre_ne_bot φ hφ y
    have hz_top : φ z ≠ ⊤ := by
      intro hztop
      have hbot : (inner ℝ z y : EReal) - φ z = ⊥ := by
        rw [hztop, EReal.sub_top]
      rw [hbot] at hz
      exact hy_bot hz.symm
    have hz_bot : φ z ≠ ⊥ := hφ.1 z
    have hzcoe : (↑((φ z).toReal) : EReal) = φ z :=
      EReal.coe_toReal hz_top hz_bot
    have hycoe :
        (↑((FunctionalInequalities.Analysis.legendre φ y).toReal) : EReal) =
          FunctionalInequalities.Analysis.legendre φ y :=
      EReal.coe_toReal hy_top hy_bot
    have heqE :
        (↑(inner ℝ z y - (φ z).toReal) : EReal) =
          FunctionalInequalities.Analysis.legendre φ y := by
      calc
        (↑(inner ℝ z y - (φ z).toReal) : EReal) =
            (inner ℝ z y : EReal) - (↑((φ z).toReal) : EReal) :=
          EReal.coe_sub _ _
        _ = (inner ℝ z y : EReal) - φ z := by rw [hzcoe]
        _ = FunctionalInequalities.Analysis.legendre φ y := hz
    have hyreal :
        inner ℝ z y - (φ z).toReal =
          (FunctionalInequalities.Analysis.legendre φ y).toReal := by
      have h := congrArg EReal.toReal heqE
      simpa only [EReal.toReal_coe] using h
    have hS : S ∈ nhds y := by
      exact Filter.mem_of_superset (isOpen_interior.mem_nhds hyS) interior_subset
    have hineq (q : E) (hq : q ∈ S) :
        inner ℝ z q - (φ z).toReal ≤
          (FunctionalInequalities.Analysis.legendre φ q).toReal := by
      have hq_top :
          FunctionalInequalities.Analysis.legendre φ q ≠ ⊤ := by
        simpa [S] using hq
      have hq_bot :
          FunctionalInequalities.Analysis.legendre φ q ≠ ⊥ :=
        FunctionalInequalities.Analysis.legendre_ne_bot φ hφ q
      have hqcoe :
          (↑((FunctionalInequalities.Analysis.legendre φ q).toReal) : EReal) =
            FunctionalInequalities.Analysis.legendre φ q :=
        EReal.coe_toReal hq_top hq_bot
      have hfen :=
        FunctionalInequalities.Analysis.fenchel_le φ hφ z q
      have hfen' :
          (inner ℝ z q : EReal) ≤
            (↑((φ z).toReal) : EReal) +
              (↑((FunctionalInequalities.Analysis.legendre φ q).toReal) : EReal) := by
        simpa [hzcoe, hqcoe] using hfen
      have hfen'' :
          (inner ℝ z q : EReal) ≤
            (↑((φ z).toReal +
                (FunctionalInequalities.Analysis.legendre φ q).toReal) : EReal) := by
        simpa using hfen'
      have hreal :
          inner ℝ z q ≤
            (φ z).toReal +
              (FunctionalInequalities.Analysis.legendre φ q).toReal :=
        EReal.coe_le_coe_iff.mp hfen''
      linarith
    have hlocal : IsLocalMax (fun q : E => inner ℝ z q - F q) y := by
      change ∀ᶠ q in nhds y,
        inner ℝ z q - F q ≤ inner ℝ z y - F y
      filter_upwards [hS] with q hq
      dsimp [F]
      linarith [hineq q hq, hyreal]
    have hzero :
        fderiv ℝ (fun q : E => inner ℝ z q - F q) y = 0 :=
      hlocal.fderiv_eq_zero
    have hinner :
        HasFDerivAt (fun q : E => inner ℝ z q)
          (fderivInnerCLM ℝ (z, y) ∘SL
            (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) y := by
      simpa [id] using
        ((hasFDerivAt_const (𝕜 := ℝ) z y).inner ℝ
          (hasFDerivAt_id (𝕜 := ℝ) y))
    have hF : DifferentiableAt ℝ F y := by
      simpa [F] using hd
    have hsub := hinner.sub hF.hasFDerivAt
    have hsubf := hsub.fderiv
    have hder :
        (fderivInnerCLM ℝ (z, y) ∘SL
            (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) -
          fderiv ℝ F y = 0 := by
      calc
        (fderivInnerCLM ℝ (z, y) ∘SL
            (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) -
            fderiv ℝ F y =
            fderiv ℝ (fun q : E => inner ℝ z q - F q) y := by
              symm
              simpa only [Pi.sub_def] using hsubf
        _ = 0 := hzero
    have hrel (v : E) : inner ℝ z v = fderiv ℝ F y v := by
      have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) hder
      have hv' : inner ℝ z v - fderiv ℝ F y v = 0 := by
        simpa [fderivInnerCLM] using hv
      linarith
    have hrel' (v : E) :
        inner ℝ z v = inner ℝ (gradient F y) v := by
      calc
        inner ℝ z v = fderiv ℝ F y v := hrel v
        _ = inner ℝ (gradient F y) v :=
          (inner_gradient_left (f := F) (x := y) (y := v)).symm
    have hz0 : z - gradient F y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      calc
        inner ℝ (z - gradient F y) (z - gradient F y) =
            inner ℝ z (z - gradient F y) -
              inner ℝ (gradient F y) (z - gradient F y) := by
                rw [inner_sub_left]
        _ = 0 := by rw [hrel' (z - gradient F y)]; ring
    change z = gradient F y
    exact sub_eq_zero.mp hz0

end MaximizerGradient

section Attainment

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite dual neighborhood forces linear growth of the actual tilted
primal, without convexity, differentiability, nonnegativity or global
finiteness of the primal. Dimension zero is included. -/
theorem exists_coercive_tilt_of_mem_interior_legendre_domain
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    ∃ (a b : ℝ), 0 < a ∧ ∀ z : E,
      ((a * ‖z‖ - b : ℝ) : EReal) ≤ φ z - (inner ℝ z y : EReal) := by
    let K : Set E := (fun w : E => y + w) ⁻¹' interior {q : E | legendre φ q ≠ ⊤}
    have hK : IsOpen K := by
      dsimp [K]
      exact isOpen_interior.preimage (continuous_const.add continuous_id)
    have h0K : 0 ∈ K := by
      dsimp [K]
      simpa using hy
    obtain ⟨s, hs, hsK, h0⟩ := exists_finite_hull_neighborhood hK h0K
    let d : E → ℝ := fun w => (legendre φ (y + w)).toReal
    let M : ℝ := s.sup' hs d
    have hbound : ∀ w ∈ s, d w ≤ M := by
      intro w hw
      exact Finset.le_sup' d hw
    obtain ⟨c, hc, hcoercive⟩ :=
      affineMaximum_coercive s hs h0
    refine ⟨c, M, hc, ?_⟩
    intro z
    have hlower :
        ((c * ‖z‖ - M : ℝ) : EReal) ≤
          (affineMaximum s hs d z : EReal) := by
      exact EReal.coe_le_coe_iff.mpr (hcoercive d M hbound z)
    obtain ⟨w, hw, hw_eq⟩ :=
      Finset.exists_mem_eq_sup' hs (fun w => inner ℝ w z - d w)
    have hwD : y + w ∈ interior {q : E | legendre φ q ≠ ⊤} := hsK hw
    have htop : legendre φ (y + w) ≠ ⊤ := interior_subset hwD
    have hbot : legendre φ (y + w) ≠ ⊥ :=
      legendre_ne_bot φ hφ (y + w)
    have hleg : legendre φ (y + w) = (d w : EReal) := by
      dsimp [d]
      symm
      exact EReal.coe_toReal htop hbot
    have hfen := fenchel_le φ hφ z (y + w)
    rw [hleg] at hfen
    have hsub :
        ((inner ℝ z (y + w) : ℝ) : EReal) - (d w : EReal) ≤ φ z := by
      calc
        ((inner ℝ z (y + w) : ℝ) : EReal) - (d w : EReal) ≤
            (φ z + (d w : EReal)) - (d w : EReal) :=
          EReal.sub_le_sub hfen (le_refl _)
        _ = φ z := EReal.add_sub_cancel_right
    have hvertex :
        ((inner ℝ w z - d w : ℝ) : EReal) ≤
          φ z - (inner ℝ z y : EReal) := by
      apply
        (EReal.le_sub_iff_add_le
          (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))).2
      calc
        ((inner ℝ w z - d w : ℝ) : EReal) + (inner ℝ z y : EReal) =
            ((inner ℝ z (y + w) : ℝ) : EReal) - (d w : EReal) := by
              rw [EReal.coe_sub, inner_add_right, EReal.coe_add,
                real_inner_comm w z]
              simp only [sub_eq_add_neg]
              ac_rfl
        _ ≤ φ z := hsub
    have hupper :
        (affineMaximum s hs d z : EReal) ≤
          φ z - (inner ℝ z y : EReal) := by
      rw [affineMaximum, hw_eq]
      exact hvertex
    exact hlower.trans hupper

/-- The actual tilted objective has the regularity, nondegeneracy, and linear
upper decay data needed by a separate generic upper-semicontinuous attainment
theorem. No maximizer or desired decay is assumed. -/
theorem tiltedObjective_data
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    let G : E → EReal := fun z => (inner ℝ z y : EReal) - φ z
    UpperSemicontinuous G ∧
      (∀ z, G z ≠ ⊤) ∧
      (∃ z, G z ≠ ⊥) ∧
      ∃ (a b : ℝ), 0 < a ∧ ∀ z,
        G z ≤ ((b - a * ‖z‖ : ℝ) : EReal) := by
    dsimp
    have hc : Continuous (fun z : E => (inner ℝ z y : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)
    have hneg : UpperSemicontinuous (fun z : E => -φ z) :=
      Continuous.comp_lowerSemicontinuous_antitone
        continuous_neg hlsc EReal.neg_strictAnti.antitone
    have hadd :
        UpperSemicontinuous
          (fun z : E => (inner ℝ z y : EReal) + -φ z) :=
      hc.upperSemicontinuous.add' hneg (by
        intro z
        apply EReal.continuousAt_add
        · left
          exact EReal.coe_ne_top _
        · left
          exact EReal.coe_ne_bot _)
    have hupper : UpperSemicontinuous (fun z : E => (inner ℝ z y : EReal) - φ z) := by
      simpa [sub_eq_add_neg, Function.comp_def] using hadd
    refine ⟨hupper, ?_, ?_, ?_⟩
    · intro z
      change (inner ℝ z y : EReal) + -φ z ≠ ⊤
      apply EReal.add_ne_top (EReal.coe_ne_top _)
      exact fun h => hφ.1 z (EReal.neg_eq_top_iff.mp h)
    · rcases hφ.2 with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      change (inner ℝ z y : EReal) + -φ z ≠ ⊥
      apply EReal.add_ne_bot_iff.mpr
      exact ⟨EReal.coe_ne_bot _, by intro h; exact hz (EReal.neg_eq_bot_iff.mp h)⟩
    · rcases
        exists_coercive_tilt_of_mem_interior_legendre_domain φ hφ y hy with
        ⟨a, b, ha, hab⟩
      refine ⟨a, b, ha, fun z => ?_⟩
      have hn := EReal.neg_le_neg_iff.mpr (hab z)
      calc
        (inner ℝ z y : EReal) - φ z =
            -(φ z - (inner ℝ z y : EReal)) := by
              rw [EReal.neg_sub (Or.inr (EReal.coe_ne_bot _))
                (Or.inr (EReal.coe_ne_top _)), sub_eq_add_neg, add_comm]
        _ ≤ -((a * ‖z‖ - b : ℝ) : EReal) := hn
        _ = ((b - a * ‖z‖ : ℝ) : EReal) := by
          rw [← EReal.coe_neg]
          congr 1
          ring

/-- Every interior point of the actual finite Legendre domain has an actual
primal maximizer. If the real-valued dual is differentiable there, the same
maximizer is its actual gradient. -/
theorem exists_legendre_maximizer_with_gradient_identity
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    ∃ z : E,
      (inner ℝ z y : EReal) - φ z = legendre φ y ∧
      (DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y →
        z = gradient (fun q : E => (legendre φ q).toReal) y) := by
    rcases tiltedObjective_data φ hφ hlsc y hy with
      ⟨husc, hnotTop, hfinite, a, b, ha, hdecay⟩
    rcases exists_finite_maximum_of_upperSemicontinuous_linear_decay
        (fun x : E => (inner ℝ x y : EReal) - φ x)
        husc hnotTop hfinite a b ha hdecay with
      ⟨z, hzbot, hztop, hmax⟩
    have hle :
        (inner ℝ z y : EReal) - φ z ≤ legendre φ y := by
      change
        (inner ℝ z y : EReal) - φ z ≤
          ⨆ x : E, (inner ℝ x y : EReal) - φ x
      exact le_iSup (fun x : E => (inner ℝ x y : EReal) - φ x) z
    have hge :
        legendre φ y ≤ (inner ℝ z y : EReal) - φ z := by
      change
        (⨆ x : E, (inner ℝ x y : EReal) - φ x) ≤
          (inner ℝ z y : EReal) - φ z
      exact iSup_le (fun x => hmax x)
    have heq :
        (inner ℝ z y : EReal) - φ z = legendre φ y :=
      le_antisymm hle hge
    refine ⟨z, heq, ?_⟩
    intro hd
    exact
      conjugate_maximizer_eq_gradient
        φ hφ hy hd z heq

end Attainment

end FunctionalInequalities.Analysis
