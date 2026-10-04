/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.DifferentiatedWkInfty
public import LeanPool.EllipticPDE.Regularity.HigherWeakDeriv


/-!
# Multiplying an iterated weak derivative by a `W^{k,∞}` weight

The datum of the differentiated equation is a sum of products, each a coefficient against a
derivative of the solution. Feeding that datum back into the induction of Guo, *Partial
Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65) needs weak
derivatives of the product up to order `k`, with a bound. This file supplies them.

## Recursion

`HasWeakDerivOn.mul_isWkInfty_left` gives one derivative of `a·g`, namely `(∂_ℓ a)·g + a·(∂_ℓ
g)`. Both summands are again products of a `W^{k,∞}` weight with a function with `k` weak
derivatives, so the statement recurses on its own conclusion. The family for `a·g` at order `k +
1` is therefore assembled rather than written down: the empty list is the product itself, and a
list `ℓ :: α` reads the order-`k` family built for the `ℓ`-derivative.

No Leibniz formula over subsets of the index list appears, and none is needed. Naming the
derivative of each order through the recursion avoids the combinatorial statement altogether,
with a constant that is existentially quantified rather than computed. The estimate
of Theorem VIII.3.2 quantifies its constant before the solution and the datum and says nothing
about its size, so nothing is lost.

## Main declarations

* `HasWeakDerivOn.add`, `HasIteratedWeakDerivOn.add`: sums.
* `mulL2`: a bounded measurable weight acting on an `L²(V)` class.
* `exists_iteratedWeakDeriv_mul`: the product has `k` weak derivatives, with a bound linear in
  the bound on the family of `g`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Sums -/

/-- A weak derivative of a sum is the sum of the weak derivatives. -/
theorem HasWeakDerivOn.add {V : Set (EuclideanSpace ℝ (Fin d))} {ℓ : Fin d}
    {g g' h h' : L2D V} (hg : HasWeakDerivOn V ℓ g g') (hh : HasWeakDerivOn V ℓ h h') :
    HasWeakDerivOn V ℓ (g + h) (g' + h') := by
  intro φ hφc hφcs hφV
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hdφ : MemLp (partialD ℓ φ) 2 (volume.restrict V) :=
    ((contDiff_partialD hφc ℓ).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume)
      (hasCompactSupport_partialD hφcs ℓ)).restrict V
  have hφL : MemLp φ 2 (volume.restrict V) :=
    (hφc.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hφcs).restrict V
  have i1 : ∀ p : L2D V, Integrable (fun x => (p x : ℝ) * partialD ℓ φ x) (volume.restrict V) :=
    fun p => (Lp.memLp p).integrable_mul hdφ
  have i2 : ∀ p : L2D V, Integrable (fun x => (p x : ℝ) * φ x) (volume.restrict V) :=
    fun p => (Lp.memLp p).integrable_mul hφL
  have e1 : (∫ x in V, ((g + h) x : ℝ) * partialD ℓ φ x)
      = (∫ x in V, (g x : ℝ) * partialD ℓ φ x) + ∫ x in V, (h x : ℝ) * partialD ℓ φ x := by
    rw [← integral_add (i1 g) (i1 h)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add g h] with x hx
    rw [hx, Pi.add_apply]; ring
  have e2 : (∫ x in V, ((g' + h') x : ℝ) * φ x)
      = (∫ x in V, (g' x : ℝ) * φ x) + ∫ x in V, (h' x : ℝ) * φ x := by
    rw [← integral_add (i2 g') (i2 h')]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add g' h'] with x hx
    rw [hx, Pi.add_apply]; ring
  rw [e1, e2, hg φ hφc hφcs hφV, hh φ hφc hφcs hφV]
  ring

/-- The order-`k` family of a sum, entry by entry. -/
def HasIteratedWeakDerivOn.add {V : Set (EuclideanSpace ℝ (Fin d))} {k : ℕ} {g h : L2D V}
    (hg : HasIteratedWeakDerivOn V k g) (hh : HasIteratedWeakDerivOn V k h) :
    HasIteratedWeakDerivOn V k (g + h) where
  D α := hg.D α + hh.D α
  D_nil := by rw [hg.D_nil, hh.D_nil]
  D_step m α hα := (hg.D_step m α hα).add (hh.D_step m α hα)

/-! ### Bounded weight acting on an `L²` class -/

/-- **Bounded measurable weight acting on `L²(V)`.** The bound is asked on the whole space
rather than on `V`, which is the form every `W^{k,∞}` bundle has. -/
def mulL2 {V : Set (EuclideanSpace ℝ (Fin d))} {a : EuclideanSpace ℝ (Fin d) → ℝ}
    (ham : Measurable a) {M : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M) (g : L2D V) :
    L2D V :=
  mulCoeffL ham (ae_restrict_of_ae haM) g

/-- The pointwise a.e. representative of the weighted class. -/
theorem mulL2_coeFn {V : Set (EuclideanSpace ℝ (Fin d))} {a : EuclideanSpace ℝ (Fin d) → ℝ}
    (ham : Measurable a) {M : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M) (g : L2D V) :
    mulL2 ham haM g =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ) :=
  mulCoeffL_coeFn ham (ae_restrict_of_ae haM) g

/-- **Any class representing the product is bounded by the weight's bound.** Stated for an
arbitrary representative rather than for `mulL2` itself, because the consumers of the product
rule name their own class. -/
theorem norm_le_of_ae_mul {V : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ham : Measurable a) {M : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M) {g ag : L2D V}
    (hag : ag =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ)) :
    ‖ag‖ ≤ M * ‖g‖ := by
  have hrw : ag = mulL2 ham haM g := by
    refine Lp.ext ?_
    filter_upwards [hag, mulL2_coeFn ham haM g] with x h1 h2
    rw [h1, h2]
  rw [hrw]
  exact norm_mulCoeffL_le ham (ae_restrict_of_ae haM) g

/-! ### Product rule at every order -/

/-- **Preservation of `k` weak derivatives by a `W^{k,∞}` weight.** For `a ∈ W^{k,∞}` there is a
constant `K`, depending on the bundle alone, such that whenever `g` has weak derivatives to order
`k` on `V` bounded by `M`, every class representing `a·g` has weak derivatives to order `k`
bounded by `K·M`.

The induction is on `k`. The step applies `HasWeakDerivOn.mul_isWkInfty_left` once to obtain
`∂_ℓ(a·g) = (∂_ℓ a)·g + a·(∂_ℓ g)`, then the induction hypothesis to each summand, the first with
the weight `∂_ℓ a ∈ W^{k,∞}` and the second with the function `∂_ℓ g`, whose order-`k` family is
`HasIteratedWeakDerivOn.deriv`. -/
theorem exists_iteratedWeakDeriv_mul :
    ∀ (k : ℕ) {a : EuclideanSpace ℝ (Fin d) → ℝ}, IsWkInfty a k →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ {V : Set (EuclideanSpace ℝ (Fin d))} {g ag : L2D V}
        (hg : HasIteratedWeakDerivOn V k g),
        (ag =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ)) → ∀ {M : ℝ},
        IteratedL2Bound hg M →
        ∃ H : HasIteratedWeakDerivOn V k ag, IteratedL2Bound H (K * M) := by
  intro k
  induction k with
  | zero =>
    intro a ha
    refine ⟨ha.bound 0, ha.bound_nonneg 0, ?_⟩
    intro V g ag hg hag M hM
    refine ⟨HasIteratedWeakDerivOn.zero ag, fun α _ => ?_⟩
    exact (norm_le_of_ae_mul ha.measurable_self ha.ae_abs_le hag).trans
      (mul_le_mul_of_nonneg_left hM.norm_le (ha.bound_nonneg 0))
  | succ k ih =>
    intro a ha
    obtain ⟨K0, hK0, hP0⟩ := ih (ha.mono (Nat.le_succ k))
    choose K1 hK1 hP1 using fun ℓ : Fin d => ih (ha.deriv ℓ)
    have hKsum : 0 ≤ ∑ ℓ : Fin d, K1 ℓ := Finset.sum_nonneg fun ℓ _ => hK1 ℓ
    refine ⟨ha.bound 0 + K0 + ∑ ℓ, K1 ℓ, by linarith [ha.bound_nonneg 0], ?_⟩
    intro V g ag hg hag M hM
    set K := ha.bound 0 + K0 + ∑ ℓ : Fin d, K1 ℓ with hKdef
    have hM0 : 0 ≤ M := le_trans (norm_nonneg g) hM.norm_le
    -- The order-`k` family of the `ℓ`-derivative of the product, direction by direction.
    have hstep : ∀ ℓ : Fin d, ∃ (dag : L2D V) (F : HasIteratedWeakDerivOn V k dag),
        HasWeakDerivOn V ℓ ag dag ∧ IteratedL2Bound F (K * M) := by
      intro ℓ
      -- The two summands, each a product the induction hypothesis covers.
      have hMderiv : IteratedL2Bound (hg.deriv ℓ) M := by
        intro α hα
        exact hM (α ++ [ℓ]) (by simpa [List.length_append] using Nat.succ_le_succ hα)
      obtain ⟨H1, hH1⟩ := hP1 ℓ (hg.mono (Nat.le_succ k))
        (mulL2_coeFn (ha.measurable_D_singleton ℓ) (ha.ae_abs_D_singleton_le ℓ) g)
        (hM.mono_order (Nat.le_succ k))
      obtain ⟨H2, hH2⟩ := hP0 (hg.deriv ℓ)
        (mulL2_coeFn ha.measurable_self ha.ae_abs_le (hg.D [ℓ])) hMderiv
      have hsum : (mulL2 (ha.measurable_D_singleton ℓ) (ha.ae_abs_D_singleton_le ℓ) g
            + mulL2 ha.measurable_self ha.ae_abs_le (hg.D [ℓ]))
          =ᵐ[volume.restrict V]
            fun x => ha.D [ℓ] x * (g x : ℝ) + a x * ((hg.D [ℓ]) x : ℝ) := by
        filter_upwards [Lp.coeFn_add
            (mulL2 (ha.measurable_D_singleton ℓ) (ha.ae_abs_D_singleton_le ℓ) g)
            (mulL2 ha.measurable_self ha.ae_abs_le (hg.D [ℓ])),
          mulL2_coeFn (ha.measurable_D_singleton ℓ) (ha.ae_abs_D_singleton_le ℓ) g,
          mulL2_coeFn ha.measurable_self ha.ae_abs_le (hg.D [ℓ])] with x hadd h1 h2
        simp only [hadd, Pi.add_apply, h1, h2]
      refine ⟨_, H1.add H2, ?_, ?_⟩
      · -- One derivative of the product, from the order-one Leibniz rule.
        exact HasWeakDerivOn.mul_isWkInfty_left ℓ (hg.hasWeakDerivOn_D_singleton ℓ)
          ha.measurable_self (ha.measurable_D_singleton ℓ) (ha.hasWeakPartial_D ℓ)
          ha.ae_abs_le (ha.ae_abs_D_singleton_le ℓ) ag hag _ hsum
      · intro α hα
        have hle : K1 ℓ ≤ ∑ ℓ' : Fin d, K1 ℓ' :=
          Finset.single_le_sum (fun i _ => hK1 i) (Finset.mem_univ ℓ)
        calc ‖(H1.add H2).D α‖ = ‖H1.D α + H2.D α‖ := rfl
          _ ≤ ‖H1.D α‖ + ‖H2.D α‖ := norm_add_le _ _
          _ ≤ K1 ℓ * M + K0 * M := add_le_add (hH1 α hα) (hH2 α hα)
          _ ≤ K * M := by
              rw [hKdef, ← add_mul]
              exact mul_le_mul_of_nonneg_right (by linarith [ha.bound_nonneg 0]) hM0
    choose dag F hleib hbnd using hstep
    -- The families of the first derivatives reassemble into an order-`k + 1` family.
    have hag0 : ‖ag‖ ≤ K * M := by
      refine (norm_le_of_ae_mul ha.measurable_self ha.ae_abs_le hag).trans ?_
      calc ha.bound 0 * ‖g‖ ≤ ha.bound 0 * M :=
            mul_le_mul_of_nonneg_left hM.norm_le (ha.bound_nonneg 0)
        _ ≤ K * M := by
            rw [hKdef]
            exact mul_le_mul_of_nonneg_right (by linarith) hM0
    exact ⟨HasIteratedWeakDerivOn.ofDeriv hleib F, IteratedL2Bound.ofDeriv hag0 hbnd⟩

end EllipticPdes.Regularity
