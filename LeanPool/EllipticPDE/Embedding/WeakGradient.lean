/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Sobolev.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average


/-!
# Pointwise weak gradients on a set

The `Lᵖ`-scale, pointwise-function analogue of `HasWeakDerivOn`: a function `u` has weak
gradient `g = (gₖ)` on `B` when the integration by parts identity is satisfied against every
smooth test function supported in `B`. This is the interface the Morrey embedding consumes; it is
stated for functions (not `Lp` classes) and for a full gradient tuple so that a
general exponent `p > d` is expressible, which the `L²`-only `HasWeakDerivOn` cannot do.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Integrability against a bounded factor.** An integrable class stays integrable when
multiplied by a bounded measurable one, which is how every test function and every cutoff of
this development enters an integral. -/
theorem integrableOn_mul_bounded {B : Set (EuclideanSpace ℝ (Fin d))}
    {w h : EuclideanSpace ℝ (Fin d) → ℝ} (hw : IntegrableOn w B volume) (hc : Continuous h)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) : IntegrableOn (fun x => w x * h x) B volume := by
  have hbd := hw.bdd_mul (f := h) hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  exact hbd.congr (Filter.Eventually.of_forall fun x => mul_comm (h x) (w x))

/-- `g` is the pointwise weak gradient of `u` on `B`: integration by parts holds
against every smooth compactly supported test function whose support lies in `B`. This
mirrors `EllipticPdes.Regularity.HasWeakDerivOn` component-wise but for pointwise
functions `u, gₖ : EuclideanSpace ℝ (Fin d) → ℝ`. -/
def HasWeakGradOn (B : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ B → ∀ k : Fin d,
      ∫ x in B, u x * partialD k φ x = - ∫ x in B, g k x * φ x

/-- **Scalar multiple of a weak gradient.** A constant multiple of a class with a weak gradient
has the same multiple of the gradient. -/
theorem HasWeakGradOn.const_mul {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (c : ℝ)
    (h : HasWeakGradOn B u g) :
    HasWeakGradOn B (fun x => c * u x) (fun k x => c * g k x) := by
  intro φ hφc hφcs hφs k
  have e := h φ hφc hφcs hφs k
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, e, mul_neg]

/-- **Additivity of a weak gradient.** Two classes with weak gradients on the same set add, and
so do their gradients. The finite sum of local pieces the extension operator glues is built by
iterating this. -/
theorem HasWeakGradOn.add {B : Set (EuclideanSpace ℝ (Fin d))}
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hv : IntegrableOn v B volume)
    (hg : ∀ k, IntegrableOn (g k) B volume) (hh : ∀ k, IntegrableOn (h k) B volume)
    (hU : HasWeakGradOn B u g) (hV : HasWeakGradOn B v h) :
    HasWeakGradOn B (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  obtain ⟨N, hN⟩ := hφpcs.exists_bound_of_continuous hφpc
  obtain ⟨P, hP⟩ := hφcs.exists_bound_of_continuous hφcont
  have hL : ∫ x in B, (u x + v x) * partialD k φ x
      = (∫ x in B, u x * partialD k φ x) + ∫ x in B, v x * partialD k φ x := by
    rw [← integral_add (integrableOn_mul_bounded hu hφpc hN)
      (integrableOn_mul_bounded hv hφpc hN)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hR : ∫ x in B, (g k x + h k x) * φ x
      = (∫ x in B, g k x * φ x) + ∫ x in B, h k x * φ x := by
    rw [← integral_add (integrableOn_mul_bounded (hg k) hφcont hP)
      (integrableOn_mul_bounded (hh k) hφcont hP)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring

/-- **Zero as its own weak gradient.** -/
theorem hasWeakGradOn_zero {B : Set (EuclideanSpace ℝ (Fin d))} :
    HasWeakGradOn B (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  intro φ _ _ _ k
  simp

/-- **Finite sum of classes with weak gradients**, whose gradient is the sum. This is
what glues the local pieces of the extension operator. -/
theorem hasWeakGradOn_finsetSum {ι : Type*} (s : Finset ι)
    {B : Set (EuclideanSpace ℝ (Fin d))} {U : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    {G : ι → Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : ∀ i ∈ s, IntegrableOn (U i) B volume)
    (hG : ∀ i ∈ s, ∀ k, IntegrableOn (G i k) B volume)
    (h : ∀ i ∈ s, HasWeakGradOn B (U i) (G i)) :
    HasWeakGradOn B (fun y => ∑ i ∈ s, U i y) (fun k y => ∑ i ∈ s, G i k y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasWeakGradOn_zero (B := B)
  | insert a t ha ih =>
    have hUt : ∀ i ∈ t, IntegrableOn (U i) B volume := fun i hi =>
      hU i (Finset.mem_insert_of_mem hi)
    have hGt : ∀ i ∈ t, ∀ k, IntegrableOn (G i k) B volume := fun i hi =>
      hG i (Finset.mem_insert_of_mem hi)
    have hht : ∀ i ∈ t, HasWeakGradOn B (U i) (G i) := fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    have hsum : HasWeakGradOn B (fun y => U a y + ∑ i ∈ t, U i y)
        (fun k y => G a k y + ∑ i ∈ t, G i k y) :=
      (h a (Finset.mem_insert_self a t)).add
        (hU a (Finset.mem_insert_self a t))
        (MeasureTheory.integrable_finsetSum _ fun i hi => hUt i hi)
        (fun k => hG a (Finset.mem_insert_self a t) k)
        (fun k => MeasureTheory.integrable_finsetSum _ fun i hi => hGt i hi k)
        (ih hUt hGt hht)
    simpa [Finset.sum_insert ha] using hsum

/-- The Morrey/Hölder exponent `γ = 1 - d/p`, as a `ℝ≥0` (faithful when `p > d`). -/
def morreyExponent (d : ℕ) (p : ℝ) : ℝ≥0 := Real.toNNReal (1 - (d : ℝ) / p)

/-- When `p > d`, the Morrey exponent coerces back to `1 - d/p`. -/
theorem coe_morreyExponent {p : ℝ} (hp : (d : ℝ) < p) (hd : 0 < d) :
    (morreyExponent d p : ℝ) = 1 - (d : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hp
  have : 0 ≤ 1 - (d : ℝ) / p := by
    rw [sub_nonneg, div_le_one hp0]; exact hp.le
  simp [morreyExponent, Real.coe_toNNReal _ this]

end EllipticPdes.Embedding
