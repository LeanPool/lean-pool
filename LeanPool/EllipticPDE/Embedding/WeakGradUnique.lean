/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.WeakGradient
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff


/-!
# Uniqueness of the weak gradient on an open set

Two weak gradients of one function differ by a function orthogonal to every test function, and
on an open set the fundamental lemma of the calculus of variations kills it. Mathlib has the
lemma as `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

Uniqueness is what lets separate structures be assembled into one family. Higher interior
regularity is proved order by order, so a solution with derivatives of every order arrives as one
family per order, with nothing relating them; uniqueness identifies the entries they share, and
a single family closed under differentiation follows.

## Main declarations

* `EllipticPdes.Embedding.hasWeakGradOn_unique_ae`: two weak gradients of one function agree
  almost everywhere on an open set.
-/

@[expose] public section

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Uniqueness of the weak gradient on an open set.** Two weak gradients of the same function
agree almost everywhere, given integrability on the set, which is what the fundamental lemma of
the calculus of variations asks of the difference.

Integrability rather than local integrability is asked for because the only sets this is applied
to are balls, where an `L²` class supplies it, and because the splitting of the test integral
needs it anyway. -/
theorem hasWeakGradOn_unique_ae {B : Set (EuclideanSpace ℝ (Fin d))} (hBo : IsOpen B)
    (hBm : MeasurableSet B) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ∀ k, IntegrableOn (g k) B volume) (hg' : ∀ k, IntegrableOn (g' k) B volume)
    (h : HasWeakGradOn B u g) (h' : HasWeakGradOn B u g') (k : Fin d) :
    g k =ᵐ[volume.restrict B] g' k := by
  have hloc : LocallyIntegrableOn (fun x => g k x - g' k x) B volume :=
    ((hg k).sub (hg' k)).locallyIntegrableOn
  have key : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ B → ∫ x, φ x • (g k x - g' k x) ∂volume = 0 := by
    intro φ hφc hφcs hφB
    obtain ⟨C, hC⟩ := hφcs.exists_bound_of_continuous hφc.continuous
    have hφm : AEStronglyMeasurable φ (volume.restrict B) :=
      hφc.continuous.aestronglyMeasurable
    have e1 : IntegrableOn (fun x => g k x * φ x) B volume :=
      (hg k).mul_bdd hφm (Filter.Eventually.of_forall hC)
    have e2 : IntegrableOn (fun x => g' k x * φ x) B volume :=
      (hg' k).mul_bdd hφm (Filter.Eventually.of_forall hC)
    -- The test integral collapses to the set integral, since `φ` lives inside `B`.
    have hcompl : ∀ x ∉ B, φ x • (g k x - g' k x) = 0 := by
      intro x hx
      rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport fun hc => hx (hφB hc), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    -- Both gradients test to the same number against `φ`.
    have hgg' : ∫ x in B, g k x * φ x = ∫ x in B, g' k x * φ x := by
      have h1 := h φ hφc hφcs hφB k
      have h2 := h' φ hφc hφcs hφB k
      linarith [h1, h2]
    have hsplit : ∫ x in B, φ x • (g k x - g' k x)
        = (∫ x in B, g k x * φ x) - ∫ x in B, g' k x * φ x := by
      rw [← integral_sub e1 e2]
      exact setIntegral_congr_fun hBm fun x _ => by simp only [smul_eq_mul]; ring
    rw [hsplit, hgg', sub_self]
  have hzero := hBo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    fun φ hφc hφcs hφB => key φ (by exact_mod_cast hφc) hφcs hφB
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hBm] with x hx hxB
  have := hx hxB
  linarith

end EllipticPdes.Embedding
