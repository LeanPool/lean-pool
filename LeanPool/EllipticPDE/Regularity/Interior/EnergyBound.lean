/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.CoeffLip
public import LeanPool.EllipticPDE.Regularity.Interior.Support

/-!
# Master interior difference-quotient energy estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) proceeds by testing
the weak formulation of `L u = f` with the difference-quotient test element
`v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, using discrete integration by parts to move the outer difference
quotient onto the coefficient factor, uniform ellipticity from below to control the leading
term, and Cauchy-Schwarz together with the Peter-Paul (Young) inequality to absorb the
commutator, cross, zeroth-order, and right-hand terms.

## Main declarations

* `evansTest`: the admissible test element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`, whose
  membership is two applications of `cutoffMul_diffQuotG_mem_H01`.
* `interior_diffQuot_energy_bound`: the master energy estimate the sections below assemble.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ξ θ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Admissible Evans test element -/

/-- **Admissible Evans test element** `v_h = -Dₖ^{-h}(ξ² Dₖ^h u) ∈ H₀¹(Ω)`. The inner
cutoff `ξ²` and the outer cutoff `θ` (which is `≡ 1` on `tsupport ξ`) localise the two
difference quotients so that the composite stays inside `H₀¹(Ω)`; membership is two
applications of the crux admissibility lemma `cutoffMul_diffQuotG_mem_H01`, together with
closure of the submodule under negation. This is the single admissible test vector that the
weak formulation consumes in the difference-quotient energy method (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
noncomputable def evansTest (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) : H01 Ω :=
  ⟨-(cutoffMul hθ (diffQuotG k (-h) hΩm
      (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))),
    Submodule.neg_mem _
      (cutoffMul_diffQuotG_mem_H01 hθ k hΩm hsm_out
        (cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hsm_in u.2))⟩

/-- The ambient-graph value of `evansTest` is the negated cutoff of the outer difference
quotient of `ξ² Dₖ^h u`. -/
theorem evansTest_coe (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω)
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm
          (cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))))) :=
  rfl

/-! ### Support control and θ-invisibility -/

/-- **Support of the interior difference quotient.** If a class `g` has whole-space extension
a.e. supported in a measurable set `S`, then its interior difference quotient `diffQuotD k h g`
vanishes (a.e. on `Ω`) outside `S ∪ (S - h eₖ)`: the numerator
`extendL2 g (x + h eₖ) - g x` can be nonzero only when `x ∈ S` (through `g x`) or
`x + h eₖ ∈ S` (through the translate). -/
private lemma diffQuotD_ae_eq_zero_off (hΩm : MeasurableSet Ω) (k : Fin d) {h : ℝ}
    (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S) :
    ∀ᵐ x ∂(volume.restrict Ω),
      x ∉ S → x + hshift k h ∉ S → (diffQuotD k h hΩm g x : ℝ) = 0 := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  have hgS_shift : ∀ᵐ x ∂volume,
      (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) ≠ 0 →
        x + hshift k h ∈ S := hqmp.ae hgS
  filter_upwards [coeFn_diffQuotD k h hΩm g, ae_restrict_of_ae hgS,
    ae_restrict_of_ae hgS_shift, ae_restrict_of_ae (coeFn_extendL2 hΩm g),
    ae_restrict_mem hΩm] with x hdq hgx hgxs hext hmem hxS hxsS
  rw [hdq]
  have h1 : (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h) = 0 := by
    by_contra hne; exact hxsS (hgxs hne)
  have h2 : (g x : ℝ) = 0 := by
    by_contra hne
    refine hxS (hgx ?_)
    rw [hext, Set.indicator_of_mem hmem]; exact hne
  rw [h1, h2, sub_zero, zero_div]

/-- **θ-chop invisibility.** If `g`'s extension is a.e. supported in `S` and the outer cutoff
`θ ≡ 1` on the part of `Ω` reachable into `S` by the shift, then multiplying `θ` onto the
interior difference quotient of `g` is invisible: `θ · Dₖʰ g = Dₖʰ g`. This is what lets the
outer cutoff of the Evans test element drop out of the energy identity (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
private lemma mulTest_theta_diffQuotD (hΩm : MeasurableSet Ω) (hθ : IsTestFn Ω θ)
    (k : Fin d) {h : ℝ} (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S)
    (hθ1 : ∀ x ∈ Ω, x ∈ S ∨ x + hshift k h ∈ S → θ x = 1) :
    mulTest hθ (diffQuotD k h hΩm g) = diffQuotD k h hΩm g := by
  apply Lp.ext
  filter_upwards [mulTest_coeFn hθ (diffQuotD k h hΩm g),
    diffQuotD_ae_eq_zero_off hΩm k g hgS, ae_restrict_mem hΩm] with x hmt hzero hmem
  rw [hmt]
  by_cases hd : (diffQuotD k h hΩm g x : ℝ) = 0
  · rw [hd, mul_zero]
  · have hmemS : x ∈ S ∨ x + hshift k h ∈ S := by
      by_contra hc; exact hd (hzero (not_or.mp hc).1 (not_or.mp hc).2)
    rw [hθ1 x hmem hmemS, one_mul]

/-- **θ-cross-term vanishing.** Under the same support and `θ ≡ 1` conditions (so that
`∂ⱼθ = 0` on the reachable part of `Ω`), the partial-cutoff multiplier annihilates the
interior difference quotient: `(∂ⱼθ) · Dₖʰ g = 0`. This kills the outer-cutoff cross term of
the Evans test element, which would otherwise be a second-order (double difference-quotient)
object beyond the reach of the data bound (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1). -/
private lemma mulTestPartial_theta_diffQuotD (hΩm : MeasurableSet Ω) (hθ : IsTestFn Ω θ)
    (j k : Fin d) {h : ℝ} (g : L2D Ω) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hgS : ∀ᵐ x ∂volume, (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0 → x ∈ S)
    (hθ0 : ∀ x ∈ Ω, x ∈ S ∨ x + hshift k h ∈ S → partialD j θ x = 0) :
    mulTestPartial hθ j (diffQuotD k h hΩm g) = 0 := by
  apply Lp.ext
  filter_upwards [mulTestPartial_coeFn hθ j (diffQuotD k h hΩm g),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict Ω),
    diffQuotD_ae_eq_zero_off hΩm k g hgS, ae_restrict_mem hΩm] with x hmtp hz hzero hmem
  rw [hmtp, hz, Pi.zero_apply]
  by_cases hd : (diffQuotD k h hΩm g x : ℝ) = 0
  · rw [hd, mul_zero]
  · have hmemS : x ∈ S ∨ x + hshift k h ∈ S := by
      by_contra hc; exact hd (hzero (not_or.mp hc).1 (not_or.mp hc).2)
    rw [hθ0 x hmem hmemS, zero_mul]

/-! ### Discrete integration by parts -/

/-- **Discrete integration by parts on the principal term.** For a class `p` whose whole-space
extension stays supported inside `Ω` after the backward shift, the restricted-domain pairing
of the coefficient action against the backward interior difference quotient of `p` transfers,
via the extension isometry and the whole-space adjoint relation `diffQuot_inner_adjoint`,
into minus the whole-space pairing of the *forward* difference quotient of the coefficient
action against `extendL2 p`. This is the discrete analogue of moving the derivative off the
test factor onto the coefficient factor (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, proof of Theorem 1). -/
private lemma actL_diffQuotD_ibp (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (i j k : Fin d) {h : ℝ} (g p : L2D Ω)
    (hsupp : ∀ᵐ x ∂volume,
      (extendL2 hΩm p : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0 → x ∈ Ω) :
    ⟪A.actL i j g, diffQuotD k (-h) hΩm p⟫
      = -⟪diffQuot k h (extendL2 hΩm (A.actL i j g)), extendL2 hΩm p⟫ := by
  rw [← (extendL2 hΩm).inner_map_map (A.actL i j g) (diffQuotD k (-h) hΩm p),
    extendL2_diffQuotD_eq k (-h) hΩm p hsupp,
    diffQuot_inner_adjoint k h (extendL2 hΩm (A.actL i j g)) (extendL2 hΩm p)]
  exact (neg_neg _).symm

/-! ### Support of the inner cutoff data and the Evans coordinate reduction -/

/-- **Support of the inner cutoff data.** Every ambient coordinate of the inner block `ξ² · Dₖ^h
u` has whole-space extension a.e. supported in `tsupport ξ²`: the zeroth coordinate is `ξ² ·
Dₖ^h u₀`, and the `i+1` coordinate is `ξ² · Dₖ^h ∂ᵢu + (∂ᵢξ²) · Dₖ^h u₀`, both of which have the
factor `ξ²` (or its partial, whose support is smaller). -/
private lemma diffQuotG_cutoffSq_supp (hξ : IsTestFn Ω ξ) (hΩm : MeasurableSet Ω)
    (k : Fin d) (h : ℝ) (u : H1amb Ω) (j : Fin (d + 1)) :
    ∀ᵐ x ∂volume,
      (extendL2 hΩm ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm u)) j)
          : EuclideanSpace ℝ (Fin d) → ℝ) x ≠ 0
        → x ∈ tsupport (fun y => ξ y * ξ y) := by
  apply extendL2_supp_of_ae_restrict
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [cutoffMul_apply_zero, diffQuotG_apply]
    exact mulTest_ae_eq_zero_off_tsupport (isTestFn_mul hξ hξ) _
  · rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
    filter_upwards [Lp.coeFn_add
        (mulTest (isTestFn_mul hξ hξ) (diffQuotD k h hΩm (u i.succ)))
        (mulTestPartial (isTestFn_mul hξ hξ) i (diffQuotD k h hΩm (u 0))),
      mulTest_coeFn (isTestFn_mul hξ hξ) (diffQuotD k h hΩm (u i.succ)),
      mulTestPartial_coeFn (isTestFn_mul hξ hξ) i (diffQuotD k h hΩm (u 0))]
      with x hadd hmt hmtp hxS
    have hsq : ξ x * ξ x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => ξ y * ξ y) hxS
    have hpsq : partialD i (fun y => ξ y * ξ y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := partialD i (fun y => ξ y * ξ y))
        (fun hc => hxS (tsupport_partialD_subset i _ hc))
    rw [hadd, Pi.add_apply, hmt, hmtp, hsq, hpsq, zero_mul, zero_mul, add_zero]

/-- **Evans test element at the successor coordinate.** Under the outer-cutoff reachability
conditions (`θ ≡ 1`, hence `∂θ = 0`, on the shift-reachable part of `tsupport ξ²`), the
`j+1` coordinate of the admissible test element reduces to a single backward difference
quotient of the inner block: `(v_h)_{j+1} = -Dₖ^{-h}((ξ²·Dₖ^h u)_{j+1})`. This is the
θ-chop invisibility together with the vanishing of the outer-cutoff cross term (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma evansTest_succ_eq (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω) (j : Fin d)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) j.succ
      = -diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ) := by
  let Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))
  have hZ : Z = cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) := rfl
  have hcoe : (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) j.succ
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm Z)) j.succ := by
    rw [evansTest_coe]; rfl
  rw [hcoe, cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
  have hvis : mulTest hθ (diffQuotD k (-h) hΩm (Z j.succ)) = diffQuotD k (-h) hΩm (Z j.succ) :=
    mulTest_theta_diffQuotD hΩm hθ k (Z j.succ)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) j.succ) hθ1
  have hcross : mulTestPartial hθ j (diffQuotD k (-h) hΩm (Z 0)) = 0 :=
    mulTestPartial_theta_diffQuotD hΩm hθ j k (Z 0)
      (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) 0) hθ0
  rw [hvis, hcross, add_zero]

/-- **Evans bilinear identity after discrete integration by parts.** Testing the principal
bilinear form with the Evans test element, the coordinate reduction `evansTest_succ_eq`
followed by the discrete integration-by-parts identity `actL_diffQuotD_ibp` moves the
backward difference quotient off the test factor onto the coefficient action, yielding the
whole-space pairing of the forward difference quotient of the coefficient-weighted gradient
against the inner cutoff block (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma evansTest_bilin_ibp (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0) (u : H01 Ω) :
    A.bilin Ω u (evansTest hΩm hξ hθ k h hsm_in hsm_out u)
      = ∑ i : Fin d, ∑ j : Fin d,
        ⟪diffQuot k h (extendL2 hΩm (A.actL i j ((u : H1amb Ω) i.succ))),
          extendL2 hΩm
            ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ)⟫ := by
  rw [EllipticCoeff.bilin_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  let Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))
  have hZ : Z = cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) := rfl
  have hsupp_j : ∀ᵐ x ∂volume,
      (extendL2 hΩm (Z j.succ) : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k (-h)) ≠ 0
        → x ∈ Ω := by
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
        (· + hshift k (-h)) volume volume :=
      (measurePreserving_add_right volume (hshift k (-h))).quasiMeasurePreserving
    filter_upwards [hqmp.ae (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) j.succ)]
      with x hx hne
    have hxS : x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y) := hx hne
    have hxeq : x = (x + hshift k (-h)) + hshift k h := by rw [hshift_neg]; abel
    rw [hxeq]; exact hsm_in _ hxS
  rw [show ((evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) j.succ)
        = -diffQuotD k (-h) hΩm (Z j.succ) from
      evansTest_succ_eq hΩm hξ hθ k h hsm_in hsm_out u j hθ1 (hθ0 j),
    inner_neg_right, actL_diffQuotD_ibp A hΩm i j k ((u : H1amb Ω) i.succ) (Z j.succ) hsupp_j,
    neg_neg]

/-- The interior difference quotient is the restriction of the whole-space difference
quotient of the extension: `Dₖʰ g = restrict (Dₖʰ (extendL2 g))`. -/
private lemma diffQuotD_eq_restrictL2_diffQuot (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ)
    (g : L2D Ω) :
    diffQuotD k h hΩm g = restrictL2 (diffQuot k h (extendL2 hΩm g)) := by
  apply Lp.ext
  filter_upwards [coeFn_diffQuotD k h hΩm g,
    coeFn_restrictL2 (diffQuot k h (extendL2 hΩm g)),
    ae_restrict_of_ae (coeFn_diffQuot k h (extendL2 hΩm g)),
    ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, hx2, hx3, hx4, Set.indicator_of_mem hx5]

/-- **Evans test element at the zeroth coordinate.** The function value of the test element is a
single backward difference quotient of the inner block, `(v_h)₀ = -Dₖ^{-h}((ξ²·Dₖ^h u)₀)`,
by θ-chop invisibility (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma evansTest_zero_eq (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ)
    (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) (u : H01 Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1) :
    (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) 0
      = -diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0) := by
  let Z : H1amb Ω := cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))
  have hZ : Z = cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω)) := rfl
  have hcoe : (evansTest hΩm hξ hθ k h hsm_in hsm_out u : H1amb Ω) 0
      = -(cutoffMul hθ (diffQuotG k (-h) hΩm Z)) 0 := by rw [evansTest_coe]; rfl
  rw [hcoe, cutoffMul_apply_zero, diffQuotG_apply]
  rw [mulTest_theta_diffQuotD hΩm hθ k (Z 0)
    (diffQuotG_cutoffSq_supp hξ hΩm k h (u : H1amb Ω) 0) hθ1]

/-- **Evans bilinear identity in restricted-domain form.** Bringing the whole-space pairing of
`evansTest_bilin_ibp` back to `L²(Ω)` through the extension adjoint and the identity
`diffQuotD = restrict ∘ diffQuot ∘ extendL2`, the principal form testing against the Evans
element is the restricted-domain pairing of the inner cutoff block against the interior
difference quotient of the coefficient action (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1). -/
private lemma evansTest_bilin_L2D (A : EllipticCoeff d) (hΩm : MeasurableSet Ω)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) (h : ℝ)
    (hsm_in : ∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω)
    (hsm_out : ∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω)
    (hθ1 : ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → θ x = 1)
    (hθ0 : ∀ (j : Fin d), ∀ x ∈ Ω,
      x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
        → partialD j θ x = 0) (u : H01 Ω) :
    A.bilin Ω u (evansTest hΩm hξ hθ k h hsm_in hsm_out u)
      = ∑ i : Fin d, ∑ j : Fin d,
        ⟪(cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) j.succ,
          diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))⟫ := by
  rw [evansTest_bilin_ibp A hΩm hξ hθ k h hsm_in hsm_out hθ1 hθ0 u]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [real_inner_comm, extendL2_inner_restrictL2, ← diffQuotD_eq_restrictL2_diffQuot]

/-! ### Extension-by-zero weak derivative and the first-order global energy -/

/-- **Extension by zero of an `H₀¹` element preserves the weak gradient.** For `u ∈ H₀¹(Ω)`, the
whole-space extension by zero of the function value `u₀` has whole-space `L²` weak
`k`-derivative equal to the extension by zero of the gradient component `u_{k+1}`. Because `u`
vanishes at the boundary (it lies in the closure of the compactly supported test functions), no
boundary term appears when integrating against an arbitrary whole-space test function `φ`: the
identity `∫ (extendL2 u₀) ∂ₖφ = -∫ (extendL2 u_{k+1}) φ` is closed under `L²` limits and holds
on every test-function graph by classical integration by parts, hence on all of `H₀¹(Ω)` (Evans,
*Partial Differential Equations* (2nd ed.), §5.8.2). -/
theorem hasWeakDeriv_extendL2_of_mem_H01 (hΩm : MeasurableSet Ω) (k : Fin d)
    {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    HasWeakDeriv k (extendL2 hΩm (U 0)) (extendL2 hΩm (U k.succ)) := by
  intro φ hφcd hφcs
  have hφL2 : MemLp φ 2 volume := hφcd.continuous.memLp_of_hasCompactSupport hφcs
  have hφpc : Continuous (partialD k φ) :=
    (hφcd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hφpL2 : MemLp (partialD k φ) 2 volume := hφpc.memLp_of_hasCompactSupport hφpcs
  let a : EucL2 d := hφpL2.toLp (partialD k φ)
  have ha : a = hφpL2.toLp (partialD k φ) := rfl
  let b : EucL2 d := hφL2.toLp φ
  have hb : b = hφL2.toLp φ := rfl
  let w₀ : H1amb Ω := PiLp.single 2 (0 : Fin (d + 1)) (restrictL2 a)
      + PiLp.single 2 k.succ (restrictL2 b)
  have hw₀ : w₀ = PiLp.single 2 (0 : Fin (d + 1)) (restrictL2 a)
      + PiLp.single 2 k.succ (restrictL2 b) := rfl
  -- The inner product against `w₀` extracts the two extension-by-zero pairings.
  have hΦ : ∀ V : H1amb Ω, ⟪w₀, V⟫
      = ⟪extendL2 hΩm (V 0), a⟫ + ⟪extendL2 hΩm (V k.succ), b⟫ := by
    intro V
    rw [extendL2_inner_restrictL2 hΩm (V 0) a, extendL2_inner_restrictL2 hΩm (V k.succ) b,
      hw₀, inner_add_left, inner_single_left, inner_single_left]
    congr 1 <;> exact real_inner_comm _ _
  -- On a test-function graph `w₀` is orthogonal: classical integration by parts.
  have hbase : ∀ V ∈ testGraphSet Ω, ⟪w₀, V⟫ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [hΦ, IsTestFn.testGraph_zero, IsTestFn.testGraph_succ]
    have hext0 : (extendL2 hΩm hψ.testCls : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] ψ := by
      filter_upwards [coeFn_extendL2 hΩm hψ.testCls,
        ae_imp_of_ae_restrict hψ.mem_lp.coeFn_toLp] with x hx himp
      rw [hx]
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]; exact himp hxΩ
      · rw [Set.indicator_of_notMem hxΩ,
          image_eq_zero_of_notMem_tsupport (fun hc => hxΩ (hψ.2.2 hc))]
    have hextk : (extendL2 hΩm (hψ.partialCls k) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume] partialD k ψ := by
      filter_upwards [coeFn_extendL2 hΩm (hψ.partialCls k),
        ae_imp_of_ae_restrict (hψ.memLp_partialD k).coeFn_toLp] with x hx himp
      rw [hx]
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]; exact himp hxΩ
      · rw [Set.indicator_of_notMem hxΩ,
          image_eq_zero_of_notMem_tsupport
            (fun hc => hxΩ (hψ.2.2 (tsupport_partialD_subset k ψ hc)))]
    have hI0 : ⟪extendL2 hΩm hψ.testCls, a⟫ = ∫ x, ψ x * partialD k φ x := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [hext0, hφpL2.coeFn_toLp] with x hx hax
      rw [Real.inner_apply, hx, hax]
    have hIk : ⟪extendL2 hΩm (hψ.partialCls k), b⟫ = ∫ x, partialD k ψ x * φ x := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [hextk, hφL2.coeFn_toLp] with x hx hbx
      rw [Real.inner_apply, hx, hbx]
    rw [hI0, hIk]
    have hIBP : (∫ x, φ x * partialD k ψ x) = -∫ x, partialD k φ x * ψ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (f := φ) (g := ψ) (v := EuclideanSpace.single k (1 : ℝ))
        ((hφpc.mul hψ.continuous).integrable_of_hasCompactSupport hφpcs.mul_right)
        ((hφcd.continuous.mul (hψ.continuous_partialD k)).integrable_of_hasCompactSupport
          hφcs.mul_right)
        ((hφcd.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hφcs.mul_right)
        (fun x _ => (hφcd.differentiable (by simp)).differentiableAt)
        (fun x _ => (hψ.1.differentiable (by simp)).differentiableAt)
    rw [show (∫ x, ψ x * partialD k φ x) = ∫ x, partialD k φ x * ψ x from
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _),
      show (∫ x, partialD k ψ x * φ x) = ∫ x, φ x * partialD k ψ x from
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _),
      hIBP]
    ring
  -- `w₀` is orthogonal to the span, hence to its closure `H₀¹(Ω)`.
  have hUperp : U ∈ (Submodule.span ℝ {w₀})ᗮ := by
    have hle : Submodule.span ℝ (testGraphSet Ω) ≤ (Submodule.span ℝ {w₀})ᗮ := by
      rw [Submodule.span_le]
      intro V hV
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]
      intro u hu
      rw [Submodule.mem_span_singleton] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [inner_smul_left, hbase V hV, mul_zero]
    exact (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure_minimal hle
      (Submodule.isClosed_orthogonal _) hU
  rw [Submodule.mem_orthogonal] at hUperp
  have hzero := hUperp w₀ (Submodule.mem_span_singleton_self w₀)
  rw [hΦ] at hzero
  -- Convert the two extension pairings back to integrals to match `HasWeakDeriv`.
  have hLconv : ⟪extendL2 hΩm (U 0), a⟫
      = ∫ x, ((extendL2 hΩm (U 0)) x : ℝ) * partialD k φ x := by
    rw [L2.inner_def]; refine integral_congr_ae ?_
    filter_upwards [hφpL2.coeFn_toLp] with x hax
    rw [Real.inner_apply, hax]
  have hRconv : ⟪extendL2 hΩm (U k.succ), b⟫
      = ∫ x, ((extendL2 hΩm (U k.succ)) x : ℝ) * φ x := by
    rw [L2.inner_def]; refine integral_congr_ae ?_
    filter_upwards [hφL2.coeFn_toLp] with x hbx
    rw [Real.inner_apply, hbx]
  rw [hLconv, hRconv] at hzero
  linarith [hzero]

/-- **First-order global energy estimate.** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f` whose transport field `b` vanishes and whose zeroth-order coefficient `c` is
nonnegative (a.e. on `Ω`), the full gradient energy is bounded by the data:
`λ ∑ᵢ ‖u_{i+1}‖² ≤ ‖f‖ · ‖u₀‖`. Testing the weak formulation with `u` itself, ellipticity
bounds the principal part from below, the transport term drops (`b = 0`) and the
zeroth-order term has a sign (`c ≥ 0`), so only the right-hand pairing `⟪f, u₀⟫` survives
(Evans, *Partial Differential Equations* (2nd ed.), §6.2.2). -/
theorem firstOrder_energy_le (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) :
    Op.lam / 2 * ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2
      ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ + Op.gardingγ * ‖(u : H1amb Ω) 0‖ ^ 2 := by
  have hg := Op.garding Ω u
  have hnorm : ‖u‖ ^ 2
      = ‖(u : H1amb Ω) 0‖ ^ 2 + ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := by
    rw [show ‖u‖ = ‖(u : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  have hfu : Op.fullBilin Ω u u ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ := by
    rw [hu u]
    have heq : (∫ x in Ω, (f x : ℝ) * ((u : H1amb Ω) 0 x : ℝ))
        = ⟪f, (u : H1amb Ω) 0⟫ := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards with x; rw [Real.inner_apply]
    rw [heq]; exact real_inner_le_norm _ _
  rw [hnorm] at hg
  have hsplit : Op.lam / 2 * (‖(u : H1amb Ω) 0‖ ^ 2
        + ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2)
      = Op.lam / 2 * ‖(u : H1amb Ω) 0‖ ^ 2
        + Op.lam / 2 * ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := by ring
  rw [hsplit] at hg
  have hdrop : (0 : ℝ) ≤ Op.lam / 2 * ‖(u : H1amb Ω) 0‖ ^ 2 :=
    mul_nonneg (by have := Op.lam_pos; linarith) (sq_nonneg _)
  linarith [hg, hfu, hdrop]

/-- **Gradient control of the difference quotient of `u₀`.** For `u ∈ H₀¹(Ω)`,
the interior difference quotient of the function value is bounded in `L²` by the `k`-th
gradient component, uniformly in the step `h`: `‖Dₖ^h u₀‖ ≤ ‖u_{k+1}‖`. This composes the
weak-derivative difference-quotient bound `norm_diffQuot_le_of_hasWeakDeriv` with the
extension-by-zero weak gradient `hasWeakDeriv_extendL2_of_mem_H01`, through the non-expansive
restriction (Evans, *Partial Differential Equations* (2nd ed.), §5.8.2). -/
private lemma norm_diffQuotD_u0_le (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) (u : H01 Ω) :
    ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ≤ ‖(u : H1amb Ω) k.succ‖ :=
  calc ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖
      = ‖restrictL2 (Ω := Ω) (diffQuot k h (extendL2 hΩm ((u : H1amb Ω) 0)))‖ := by
        rw [diffQuotD_eq_restrictL2_diffQuot]
    _ ≤ ‖diffQuot k h (extendL2 hΩm ((u : H1amb Ω) 0))‖ := norm_restrictL2_le _
    _ ≤ ‖extendL2 hΩm ((u : H1amb Ω) k.succ)‖ :=
        norm_diffQuot_le_of_hasWeakDeriv k (extendL2 hΩm ((u : H1amb Ω) 0))
          (extendL2 hΩm ((u : H1amb Ω) k.succ))
          (hasWeakDeriv_extendL2_of_mem_H01 hΩm k u.2) h
    _ = ‖(u : H1amb Ω) k.succ‖ := norm_extendL2 hΩm _

/-- **Ambient-space generalisation of `norm_diffQuotD_u0_le` (proof of concept).** `H01` is not
needed for this inequality itself: it is needed only to manufacture the one whole-space
weak-derivative fact `hasWeakDeriv_extendL2_of_mem_H01` supplies. Factoring that fact out as a
hypothesis `hW` shows the rest of `norm_diffQuotD_u0_le`'s proof (the identity `diffQuotD =
restrict ∘ diffQuot ∘ extendL2`, the non-expansive restriction, and the
difference-quotient/weak-derivative bound `norm_diffQuot_le_of_hasWeakDeriv`) survives unchanged
for an arbitrary ambient graph `U : H1amb Ω`, with no reference to `H01` at all. Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1, Remark (i), states that the zero-trace hypothesis
this lemma's `H01`-typed sibling states is not required for the interior estimate; this
declaration isolates that the only place it was doing work in this particular step was in
supplying `hW`, not in the inequality.

Kept as that record. The chain runs on the `H01`-typed sibling, so nothing consumes this
one. -/
theorem norm_diffQuotD_u0_le_ambient (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ)
    (U : H1amb Ω)
    (hW : HasWeakDeriv k (extendL2 hΩm (U 0)) (extendL2 hΩm (U k.succ))) :
    ‖diffQuotD k h hΩm (U 0)‖ ≤ ‖U k.succ‖ :=
  calc ‖diffQuotD k h hΩm (U 0)‖
      = ‖restrictL2 (Ω := Ω) (diffQuot k h (extendL2 hΩm (U 0)))‖ := by
        rw [diffQuotD_eq_restrictL2_diffQuot]
    _ ≤ ‖diffQuot k h (extendL2 hΩm (U 0))‖ := norm_restrictL2_le _
    _ ≤ ‖extendL2 hΩm (U k.succ)‖ :=
        norm_diffQuot_le_of_hasWeakDeriv k (extendL2 hΩm (U 0)) (extendL2 hΩm (U k.succ)) hW h
    _ = ‖U k.succ‖ := norm_extendL2 hΩm _

/-! ### Master assembly toolkit -/

/-- Multiplying by `ξ²` is multiplying by `ξ` twice: `[ξ² · g] = [ξ · (ξ · g)]`. -/
private lemma mulTest_mul_eq (hξ : IsTestFn Ω ξ) (g : L2D Ω) :
    mulTest (isTestFn_mul hξ hξ) g = mulTest hξ (mulTest hξ g) := by
  apply Lp.ext
  filter_upwards [mulTest_coeFn (isTestFn_mul hξ hξ) g,
    mulTest_coeFn hξ (mulTest hξ g), mulTest_coeFn hξ g] with x h1 h2 h3
  rw [h1, h2, h3]; ring

/-- The `ξ²`-cutoff of a class is controlled by `‖ξ‖∞` times its `ξ`-cutoff:
`‖ξ² · g‖ ≤ ‖ξ‖∞ · ‖ξ · g‖`. -/
private lemma norm_mulTest_sq_le (hξ : IsTestFn Ω ξ) (g : L2D Ω) :
    ‖mulTest (isTestFn_mul hξ hξ) g‖ ≤ (exists_abs_bound hξ).choose * ‖mulTest hξ g‖ := by
  rw [mulTest_mul_eq hξ g]; exact norm_mulTest_le hξ _

/-- **`L²(Ω)` norm bound on the coefficient difference-quotient commutator.** The interior
difference quotient of a coefficient-multiplied field splits into the translated coefficient
acting on the field's difference quotient plus a commutator whose `L²(Ω)` norm is controlled
by the Lipschitz constant `A₁`: `‖Dₖʰ(aᵢⱼ g) − (τ_{h eₖ}aᵢⱼ) Dₖʰ g‖ ≤ A₁ ‖g‖`. This is the
discrete Leibniz split `coeFn_diffQuot_mul_coeff` measured at the restricted-domain level,
its commutator coefficient bounded pointwise by `IsLipCoeff.abs_diffQuot_coeff_le` (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1). -/
private lemma norm_diffQuotD_actL_sub_le {A : EllipticCoeff d} (hA : IsLipCoeff A)
    (hΩm : MeasurableSet Ω) (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (g : L2D Ω) :
    ‖diffQuotD k h hΩm (A.actL i j g)
        - (A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)‖ ≤ hA.A1 * ‖g‖ := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (· + hshift k h) volume volume :=
    (measurePreserving_add_right volume (hshift k h)).quasiMeasurePreserving
  let cf : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (A.a (x + hshift k h) i j - A.a x i j) / h
  have hcf : cf = fun x => (A.a (x + hshift k h) i j - A.a x i j) / h := rfl
  have hmeas : Measurable cf :=
    (((A.measurable i j).comp (measurable_add_const _)).sub (A.measurable i j)).div_const h
  have hbdd : ∀ᵐ x ∂(volume.restrict Ω), |cf x| ≤ hA.A1 :=
    ae_of_all _ (fun x => hA.abs_diffQuot_coeff_le i j k hh x)
  have hkey : diffQuotD k h hΩm (A.actL i j g)
        - (A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)
      = mulCoeffL hmeas hbdd g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (diffQuotD k h hΩm (A.actL i j g))
        ((A.translate (hshift k h)).actL i j (diffQuotD k h hΩm g)),
      coeFn_diffQuotD k h hΩm (A.actL i j g),
      (A.translate (hshift k h)).actL_coeFn i j (diffQuotD k h hΩm g),
      coeFn_diffQuotD k h hΩm g, mulCoeffL_coeFn hmeas hbdd g,
      ae_restrict_of_ae (hqmp.ae (extendL2_actL hΩm A i j g)),
      A.actL_coeFn i j g] with x hsub hdq1 hact' hdq0 hmul hsha hact0
    rw [hsub, Pi.sub_apply, hdq1, hact', EllipticCoeff.translate_a, hdq0, hmul, hact0, hsha]
    simp only [hcf]
    field_simp
    ring
  rw [hkey]; exact norm_mulCoeffL_le hmeas hbdd g

/-! ### Master interior difference-quotient energy estimate -/

/-- The squared interior difference quotient of `u₀` is bounded by the full gradient energy:
`‖Dₖ^h u₀‖² ≤ ∑ᵢ ‖u_{i+1}‖²`. Squaring `norm_diffQuotD_u0_le` (via `gcongr`) and dominating the
single `k`-th term by the sum; kept as its own declaration, proved in tactic mode with explicit
types, so the difference-quotient definition is never forced to unfold. -/
private lemma sq_norm_diffQuotD_u0_le (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) (u : H01 Ω) :
    ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ^ 2 ≤ ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := by
  have hsum : ‖(u : H1amb Ω) k.succ‖ ^ 2 ≤ ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 :=
    single_le_sum_fin (fun i => ‖(u : H1amb Ω) i.succ‖ ^ 2) (fun i => sq_nonneg _) k
  have key : ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ≤ ‖(u : H1amb Ω) k.succ‖ :=
    norm_diffQuotD_u0_le hΩm k h u
  have key2 : ‖diffQuotD k h hΩm ((u : H1amb Ω) 0)‖ ^ 2 ≤ ‖(u : H1amb Ω) k.succ‖ ^ 2 := by
    gcongr
  exact le_trans key2 hsum


private lemma energy_rhs_bound {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {ξ : EuclideanSpace ℝ
  (Fin d) → ℝ}
  (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (k : Fin d) :
  let A := Op.toEllipticCoeff;
  0 ≤ Op.gardingγ →
    ∀ (u : ↥(H01 Ω)) (f : L2D Ω) (h : ℝ),
      let Dg := fun i => (diffQuotD k h hΩm) ((u : H1amb Ω) i.succ);
      let D0 := (diffQuotD k h hΩm) ((u : H1amb Ω) 0);
      ∀ (v : ↥(H01 Ω)) (E P : ℝ),
        P = (2 + 4 * Op.gardingγ) * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) →
          0 < A.lam →
            ‖D0‖ ^ 2 ≤ P / (2 * A.lam) →
              ‖(mulTest hξ) (Dg k)‖ ^ 2 ≤ E →
                0 ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose →
                  ‖(v : H1amb Ω) 0‖ ≤
                      (exists_abs_bound hξ).choose * ‖(mulTest hξ) (Dg k)‖ +
                        (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖ →
                    ⟪f, (v : H1amb Ω) 0⟫ ≤
                      A.lam / 8 * E +
                        (2 * (exists_abs_bound hξ).choose ^ 2 / A.lam +
                              (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2 +
                            (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 *
                              A.lam)) *
                          P := by
  classical
  intro A hγnn u f h Dg D0 v E P hPdef hlam hD0P hmk hWknn hv0
  have hfP : ‖f‖ ^ 2 ≤ P := by
    rw [hPdef]
    nlinarith only [sq_nonneg ‖(u : H1amb Ω) 0‖, hγnn, sq_nonneg ‖f‖]
  have hfv1 : ⟪f, (v : H1amb Ω) 0⟫
      ≤ ‖f‖ * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) :=
    le_trans (real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left hv0 (norm_nonneg f))
  have hb1 := young_peterPaul (lam := A.lam / 4) (B := (exists_abs_bound hξ).choose)
    (x := ‖mulTest hξ (Dg k)‖) (y := ‖f‖) (by positivity)
  have hb2 : (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖f‖ * ‖D0‖
      ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          * (‖f‖ ^ 2 + ‖D0‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖f‖ - ‖D0‖), hWknn, norm_nonneg f, norm_nonneg D0]
  have hmkE : A.lam / 8 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E :=
    mul_le_mul_of_nonneg_left hmk (by linarith only [hlam])
  have hK : (0 : ℝ) ≤ (exists_abs_bound hξ).choose ^ 2 / (2 * (A.lam / 4)) :=
    div_nonneg (sq_nonneg _) (by linarith only [hlam])
  have hW2 : (0 : ℝ) ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2 := by
    linarith only [hWknn]
  have hln : A.lam ≠ 0 := hlam.ne'
  calc ⟪f, (v : H1amb Ω) 0⟫
      ≤ ‖f‖ * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) := hfv1
    _ = (exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖ * ‖f‖
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖f‖ * ‖D0‖ := by ring
    _ ≤ (A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2
            + (exists_abs_bound hξ).choose ^ 2 / (2 * (A.lam / 4)) * ‖f‖ ^ 2)
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
              * (‖f‖ ^ 2 + ‖D0‖ ^ 2) := by linarith only [hb1, hb2]
    _ ≤ (A.lam / 8 * E
            + (exists_abs_bound hξ).choose ^ 2 / (2 * (A.lam / 4)) * P)
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
              * (P + P / (2 * A.lam)) := by
        have t1 : A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E := by
          rw [show A.lam / 4 / 2 = A.lam / 8 by ring]; exact hmkE
        have t2 := mul_le_mul_of_nonneg_left hfP hK
        have t3 := mul_le_mul_of_nonneg_left (add_le_add hfP hD0P) hW2
        linarith only [t1, t2, t3]
    _ = A.lam / 8 * E + (2 * (exists_abs_bound hξ).choose ^ 2 / A.lam
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam)) * P := by
        field_simp
        ring


private lemma energy_transport_bound {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {ξ :
  EuclideanSpace ℝ (Fin d) → ℝ}
  (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (k : Fin d) (hd : d > 0) :
  let A := Op.toEllipticCoeff;
  ∀ (u : ↥(H01 Ω)) (h : ℝ),
    let Dg := fun i => (diffQuotD k h hΩm) ((u : H1amb Ω) i.succ);
    let D0 := (diffQuotD k h hΩm) ((u : H1amb Ω) 0);
    ∀ (v : ↥(H01 Ω)) (E P U1 : ℝ),
      U1 = ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 →
        0 < A.lam →
          U1 ≤ P / (2 * A.lam) →
            ‖D0‖ ^ 2 ≤ P / (2 * A.lam) →
              ‖(mulTest hξ) (Dg k)‖ ^ 2 ≤ E →
                0 ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose →
                  ‖(v : H1amb Ω) 0‖ ≤
                      (exists_abs_bound hξ).choose * ‖(mulTest hξ) (Dg k)‖ +
                        (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖ →
                    -∑ i, ⟪(Op.bAct i) ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫ ≤
                      A.lam / 8 * E +
                        ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / (4 * ↑d))) +
                                Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ)
                                  k).choose / 2 +
                              ↑d * (Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ)
                                k).choose / 2)) /
                            (2 * A.lam) *
                          P := by
  classical
  intro A u h Dg D0 v E P U1 hU1def hlam hU1P2 hD0P hmk hWknn hv0
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlam4d : (0 : ℝ) < A.lam / (4 * (d : ℝ)) := by positivity
  have hper : ∀ i : Fin d,
      -⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫
        ≤ (A.lam / (4 * (d : ℝ)) / 2 * ‖mulTest hξ (Dg k)‖ ^ 2
            + (Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
                / (2 * (A.lam / (4 * (d : ℝ)))) * ‖(u : H1amb Ω) i.succ‖ ^ 2)
          + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
              * (‖(u : H1amb Ω) i.succ‖ ^ 2 + ‖D0‖ ^ 2) := by
    intro i
    have h1 : -⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫
        ≤ ‖Op.bAct i ((u : H1amb Ω) i.succ)‖ * ‖(v : H1amb Ω) 0‖ :=
      le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
    have h2 : -⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫
        ≤ Op.Bsup * ‖(u : H1amb Ω) i.succ‖
            * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
              + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) :=
      le_trans h1 (mul_le_mul (Op.norm_bAct_le i _) hv0 (norm_nonneg _)
        (mul_nonneg Op.Bsup_nonneg (norm_nonneg _)))
    have hy1 := young_peterPaul (lam := A.lam / (4 * (d : ℝ)))
      (B := Op.Bsup * (exists_abs_bound hξ).choose)
      (x := ‖mulTest hξ (Dg k)‖) (y := ‖(u : H1amb Ω) i.succ‖) hlam4d
    have hy2 : Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
          * ‖(u : H1amb Ω) i.succ‖ * ‖D0‖
        ≤ Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
            * (‖(u : H1amb Ω) i.succ‖ ^ 2 + ‖D0‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖(u : H1amb Ω) i.succ‖ - ‖D0‖),
        mul_nonneg Op.Bsup_nonneg hWknn, norm_nonneg ((u : H1amb Ω) i.succ),
        norm_nonneg D0]
    nlinarith only [h2, hy1, hy2]
  have hK2nn : (0 : ℝ) ≤ Op.Bsup
      * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2 :=
    div_nonneg (mul_nonneg Op.Bsup_nonneg hWknn) (by norm_num)
  have hK1nn : (0 : ℝ) ≤ (Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
      / (2 * (A.lam / (4 * (d : ℝ)))) := div_nonneg (sq_nonneg _) (by positivity)
  rw [← Finset.sum_neg_distrib]
  refine le_trans (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)) ?_
  have hexp : ∑ _i : Fin d, ((A.lam / (4 * (d : ℝ)) / 2 * ‖mulTest hξ (Dg k)‖ ^ 2
        + (Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
            / (2 * (A.lam / (4 * (d : ℝ)))) * ‖(u : H1amb Ω) _i.succ‖ ^ 2)
      + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          * (‖(u : H1amb Ω) _i.succ‖ ^ 2 + ‖D0‖ ^ 2))
    = (d : ℝ) * (A.lam / (4 * (d : ℝ)) / 2) * ‖mulTest hξ (Dg k)‖ ^ 2
      + ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
            / (2 * (A.lam / (4 * (d : ℝ))))
          + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2) * U1
      + (d : ℝ) * (Op.Bsup
          * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2) * ‖D0‖ ^ 2 := by
    rw [hU1def]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hexp]
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hcoef : (d : ℝ) * (A.lam / (4 * (d : ℝ)) / 2) = A.lam / 8 := by
    field_simp; ring
  rw [hcoef]
  have hmkE : A.lam / 8 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E :=
    mul_le_mul_of_nonneg_left hmk (by linarith only [hlam])
  have hUP : U1 ≤ P / (2 * A.lam) := hU1P2
  have hDP : ‖D0‖ ^ 2 ≤ P / (2 * A.lam) := hD0P
  have hdK2nn : (0 : ℝ) ≤ (d : ℝ) * (Op.Bsup
      * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2) :=
    mul_nonneg (le_of_lt hdpos) hK2nn
  have e1 : ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
          / (2 * (A.lam / (4 * (d : ℝ))))
        + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2) * U1
      ≤ ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
          / (2 * (A.lam / (4 * (d : ℝ))))
        + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2)
        * (P / (2 * A.lam)) :=
    mul_le_mul_of_nonneg_left hUP (by linarith only [hK1nn, hK2nn])
  have e2 : (d : ℝ) * (Op.Bsup
        * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2) * ‖D0‖ ^ 2
      ≤ (d : ℝ) * (Op.Bsup
        * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2)
        * (P / (2 * A.lam)) :=
    mul_le_mul_of_nonneg_left hDP hdK2nn
  have hfinal : ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
            / (2 * (A.lam / (4 * (d : ℝ))))
          + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          + (d : ℝ) * (Op.Bsup
              * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2))
        / (2 * A.lam) * P
      = ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
            / (2 * (A.lam / (4 * (d : ℝ))))
          + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2)
          * (P / (2 * A.lam))
        + (d : ℝ) * (Op.Bsup
            * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2)
            * (P / (2 * A.lam)) := by
    field_simp
  rw [hfinal]
  linarith only [hmkE, e1, e2]


private lemma energy_zeroth_bound {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {ξ : EuclideanSpace
  ℝ (Fin d) → ℝ}
  (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (k : Fin d) :
  let A := Op.toEllipticCoeff;
  0 ≤ Op.gardingγ →
    ∀ (u : ↥(H01 Ω)) (f : L2D Ω) (h : ℝ),
      let Dg := fun i => (diffQuotD k h hΩm) ((u : H1amb Ω) i.succ);
      let D0 := (diffQuotD k h hΩm) ((u : H1amb Ω) 0);
      ∀ (v : ↥(H01 Ω)) (E P : ℝ),
        P = (2 + 4 * Op.gardingγ) * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) →
          0 < A.lam →
            ‖D0‖ ^ 2 ≤ P / (2 * A.lam) →
              ‖(mulTest hξ) (Dg k)‖ ^ 2 ≤ E →
                0 ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose →
                  ‖(v : H1amb Ω) 0‖ ≤
                      (exists_abs_bound hξ).choose * ‖(mulTest hξ) (Dg k)‖ +
                        (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖ →
                    -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ ≤
                      A.lam / 8 * E +
                        (2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam +
                              Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
                                / 2 +
                            Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose /
                              (4 * A.lam)) *
                          P := by
  classical
  intro A hγnn u f h Dg D0 v E P hPdef hlam hD0P hmk hWknn hv0
  have hu0P : ‖(u : H1amb Ω) 0‖ ^ 2 ≤ P := by
    rw [hPdef]
    nlinarith only [sq_nonneg ‖f‖, hγnn, sq_nonneg ‖(u : H1amb Ω) 0‖]
  have hcv1 : -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫
      ≤ Op.Csup * ‖(u : H1amb Ω) 0‖
          * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) := by
    have h1 : -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫
        ≤ ‖Op.cAct ((u : H1amb Ω) 0)‖ * ‖(v : H1amb Ω) 0‖ :=
      le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
    refine le_trans h1 (mul_le_mul (Op.norm_cAct_le _) hv0 (norm_nonneg _)
      (mul_nonneg Op.Csup_nonneg (norm_nonneg _)))
  have hb1 := young_peterPaul (lam := A.lam / 4)
    (B := Op.Csup * (exists_abs_bound hξ).choose)
    (x := ‖mulTest hξ (Dg k)‖) (y := ‖(u : H1amb Ω) 0‖) (by positivity)
  have hb2 : Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
        * ‖(u : H1amb Ω) 0‖ * ‖D0‖
      ≤ Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          * (‖(u : H1amb Ω) 0‖ ^ 2 + ‖D0‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖(u : H1amb Ω) 0‖ - ‖D0‖),
      mul_nonneg Op.Csup_nonneg hWknn, norm_nonneg ((u : H1amb Ω) 0), norm_nonneg D0]
  have hmkE : A.lam / 8 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E :=
    mul_le_mul_of_nonneg_left hmk (by linarith only [hlam])
  have hK : (0 : ℝ) ≤ (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / 4)) :=
    div_nonneg (sq_nonneg _) (by linarith only [hlam])
  have hW2 : (0 : ℝ) ≤ Op.Csup
      * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2 :=
    div_nonneg (mul_nonneg Op.Csup_nonneg hWknn) (by norm_num)
  have hln : A.lam ≠ 0 := hlam.ne'
  calc -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫
      ≤ Op.Csup * ‖(u : H1amb Ω) 0‖
          * ((exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
            + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖) := hcv1
    _ = Op.Csup * (exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖ * ‖(u : H1amb Ω) 0‖
          + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
              * ‖(u : H1amb Ω) 0‖ * ‖D0‖ := by ring
    _ ≤ (A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2
            + (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / 4))
                * ‖(u : H1amb Ω) 0‖ ^ 2)
          + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
              * (‖(u : H1amb Ω) 0‖ ^ 2 + ‖D0‖ ^ 2) := by linarith only [hb1, hb2]
    _ ≤ (A.lam / 8 * E
            + (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / (2 * (A.lam / 4)) * P)
          + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
              * (P + P / (2 * A.lam)) := by
        have t1 : A.lam / 4 / 2 * ‖mulTest hξ (Dg k)‖ ^ 2 ≤ A.lam / 8 * E := by
          rw [show A.lam / 4 / 2 = A.lam / 8 by ring]; exact hmkE
        have t2 := mul_le_mul_of_nonneg_left hu0P hK
        have t3 := mul_le_mul_of_nonneg_left (add_le_add hu0P hD0P) hW2
        linarith only [t1, t2, t3]
    _ = A.lam / 8 * E + (2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam
          + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose
              / (4 * A.lam)) * P := by
        field_simp
        ring


private lemma energy_cross_bound {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {ξ : EuclideanSpace
  ℝ (Fin d) → ℝ}
  (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω) (hξ : IsTestFn Ω ξ) (k : Fin d) :
  let A := Op.toEllipticCoeff;
  ∀ (u : ↥(H01 Ω)) (h : ℝ),
    let A' := A.translate (hshift k h);
    let Dg := fun i => (diffQuotD k h hΩm) ((u : H1amb Ω) i.succ);
    let D0 := (diffQuotD k h hΩm) ((u : H1amb Ω) 0);
    ∀ (E : ℝ),
      E = ∑ i, ‖(mulTest hξ) (Dg i)‖ ^ 2 →
        ∀ (P CROSS : ℝ),
          CROSS = ∑ i, ∑ j, 2 * ⟪(A'.actL i j) ((mulTest hξ) (Dg i)), (mulTestPartial hξ j) D0⟫ →
            ‖D0‖ ^ 2 ≤ P / (2 * A.lam) →
              -CROSS ≤
                A.lam / 8 * E +
                  ↑d * ((2 * A.Λ * ∑ j, (exists_abs_bound_partialD hξ j).choose) ^ 2 / (2 * (A.lam
                    / 4))) /
                      (2 * A.lam) *
                    P := by
  classical
  intro A u h A' Dg D0 E hEdef P CROSS hCROSSdef hD0P
  have hlam : 0 < A.lam := A.lam_pos
  let SW : ℝ := ∑ j : Fin d, (exists_abs_bound_partialD hξ j).choose
  have hSWdef : SW = ∑ j : Fin d, (exists_abs_bound_partialD hξ j).choose := rfl
  let C : ℝ := (2 * A.Λ * SW) ^ 2 / (2 * (A.lam / 4))
  have hCdef : C = (2 * A.Λ * SW) ^ 2 / (2 * (A.lam / 4)) := rfl
  have hCnn : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  -- Per-index bound (sum over `j` inside), then Young.
  have hper : ∀ i : Fin d,
      |∑ j : Fin d, 2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
        ≤ A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2 + C * ‖D0‖ ^ 2 := by
    intro i
    have hj : ∀ j : Fin d,
        |2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
          ≤ 2 * A.Λ * (exists_abs_bound_partialD hξ j).choose
              * ‖mulTest hξ (Dg i)‖ * ‖D0‖ := by
      intro j
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      have h1 := abs_real_inner_le_norm (A'.actL i j (mulTest hξ (Dg i)))
        (mulTestPartial hξ j D0)
      have h2 : ‖A'.actL i j (mulTest hξ (Dg i))‖ ≤ A.Λ * ‖mulTest hξ (Dg i)‖ :=
        A'.norm_actL_le i j _
      have h3 : ‖mulTestPartial hξ j D0‖
          ≤ (exists_abs_bound_partialD hξ j).choose * ‖D0‖ := norm_mulTestPartial_le hξ j D0
      have h4 : |⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
          ≤ (A.Λ * ‖mulTest hξ (Dg i)‖)
              * ((exists_abs_bound_partialD hξ j).choose * ‖D0‖) :=
        le_trans h1 (mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg A.Λ_nonneg (norm_nonneg _)))
      nlinarith only [h4]
    have habs :
        |∑ j : Fin d, 2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
          ≤ ∑ j : Fin d, 2 * A.Λ * (exists_abs_bound_partialD hξ j).choose
              * ‖mulTest hξ (Dg i)‖ * ‖D0‖ :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => hj j))
    have hsumj : ∑ j : Fin d, 2 * A.Λ * (exists_abs_bound_partialD hξ j).choose
            * ‖mulTest hξ (Dg i)‖ * ‖D0‖
        = 2 * A.Λ * ‖mulTest hξ (Dg i)‖ * ‖D0‖ * SW := by
      rw [hSWdef, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have hyoung := young_peterPaul (lam := A.lam / 4) (B := 2 * A.Λ * SW)
      (x := ‖mulTest hξ (Dg i)‖) (y := ‖D0‖) (by positivity)
    rw [hCdef]
    calc |∑ j : Fin d, 2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
        ≤ 2 * A.Λ * ‖mulTest hξ (Dg i)‖ * ‖D0‖ * SW := by rw [← hsumj]; exact habs
      _ = 2 * A.Λ * SW * ‖mulTest hξ (Dg i)‖ * ‖D0‖ := by ring
      _ ≤ A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2
            + (2 * A.Λ * SW) ^ 2 / (2 * (A.lam / 4)) * ‖D0‖ ^ 2 := by
          have : A.lam / 4 / 2 = A.lam / 8 := by ring
          linarith only [hyoung, this]
  -- Sum the per-index bound.
  have hCROSSabs : -CROSS ≤ A.lam / 8 * E + (d : ℝ) * (C * ‖D0‖ ^ 2) := by
    rw [hCROSSdef]
    have hle : |∑ i : Fin d, ∑ j : Fin d,
          2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫|
        ≤ ∑ i : Fin d, (A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2 + C * ‖D0‖ ^ 2) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => hper i))
    have hsplit : ∑ i : Fin d, (A.lam / 8 * ‖mulTest hξ (Dg i)‖ ^ 2 + C * ‖D0‖ ^ 2)
        = A.lam / 8 * E + (d : ℝ) * (C * ‖D0‖ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hEdef, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hneg : -(∑ i : Fin d, ∑ j : Fin d,
        2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫)
        ≤ |∑ i : Fin d, ∑ j : Fin d,
          2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫| := neg_le_abs _
    linarith only [hle, hsplit, hneg]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) * C := mul_nonneg (by positivity) hCnn
  have hDC : (d : ℝ) * (C * ‖D0‖ ^ 2) ≤ (d : ℝ) * C / (2 * A.lam) * P :=
    calc (d : ℝ) * (C * ‖D0‖ ^ 2) = (d : ℝ) * C * ‖D0‖ ^ 2 := by ring
      _ ≤ (d : ℝ) * C * (P / (2 * A.lam)) := mul_le_mul_of_nonneg_left hD0P hd0
      _ = (d : ℝ) * C / (2 * A.lam) * P := by ring
  linarith only [hCROSSabs, hDC]


private lemma energy_commutator_bound {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {ξ :
  EuclideanSpace ℝ (Fin d) → ℝ}
  (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω) (hA : IsLipCoeff Op.toEllipticCoeff) (hξ :
    IsTestFn Ω ξ) (k : Fin d) (hd : 0 < d) :
  let A := Op.toEllipticCoeff;
  ∀ (u : ↥(H01 Ω)) (h : ℝ),
    h ≠ 0 →
      let A' := A.translate (hshift k h);
      let Dg := fun i => (diffQuotD k h hΩm) ((u : H1amb Ω) i.succ);
      let D0 := (diffQuotD k h hΩm) ((u : H1amb Ω) 0);
      ∀ (E : ℝ),
        E = ∑ i, ‖(mulTest hξ) (Dg i)‖ ^ 2 →
          ∀ (P U1 : ℝ),
            U1 = ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 →
              let Sr := fun i j => (diffQuotD k h hΩm) ((A.actL i j) ((u : H1amb Ω) i.succ)) -
                (A'.actL i j) (Dg i);
              (Sr = fun i j => (diffQuotD k h hΩm) ((A.actL i j) ((u : H1amb Ω) i.succ)) -
                (A'.actL i j) (Dg i)) →
                ∀ (REST : ℝ),
                  REST =
                      ∑ i,
                        ∑ j,
                          ⟪(mulTest (isTestFn_mul hξ hξ)) (Dg j) + (mulTestPartial (isTestFn_mul
                            hξ hξ) j) D0, Sr i j⟫ →
                    U1 ≤ P / (2 * A.lam) →
                      ‖D0‖ ^ 2 ≤ P / (2 * A.lam) →
                        -REST ≤
                          A.lam / 8 * E +
                            (∑ j,
                                    (((exists_abs_bound hξ).choose * hA.A1) ^ 2 * (2 * ↑d / A.lam) +
                                      hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ)
                                        j).choose) +
                                  ↑d * ∑ j, hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul
                                    hξ hξ) j).choose) /
                                (2 * A.lam) *
                              P := by
  classical
  intro A u h hh A' Dg D0 E hEdef P U1 hU1def Sr hSrdef REST hRESTdef hU1P2 hD0P
  have hlam : 0 < A.lam := A.lam_pos
  have hXi : (0 : ℝ) ≤ (exists_abs_bound hξ).choose :=
    le_trans (abs_nonneg _) ((exists_abs_bound hξ).choose_spec 0)
  have hA1 : (0 : ℝ) ≤ hA.A1 := hA.A1_nonneg
  let Xi : ℝ := (exists_abs_bound hξ).choose
  have hXidef : Xi = (exists_abs_bound hξ).choose := rfl
  let Wq : Fin d → ℝ := fun j => (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose

  have hWqdef : Wq = fun j => (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose
    := rfl
  have hWqnn : ∀ j, (0 : ℝ) ≤ Wq j := fun j =>
    le_trans (abs_nonneg _) ((exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose_spec 0)
  -- coefficients of the per-(i,j) upper bound
  let a : Fin d → ℝ := fun j =>
    (Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) + hA.A1 / 2 * Wq j
  have hadef : a = fun j =>
    (Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) + hA.A1 / 2 * Wq j := rfl
  let b : Fin d → ℝ := fun j => hA.A1 / 2 * Wq j
  have hbdef : b = fun j => hA.A1 / 2 * Wq j := rfl
  have hanN : ∀ j, (0 : ℝ) ≤ a j := fun j => by
    rw [hadef]; have := hWqnn j; positivity
  have hbnN : ∀ j, (0 : ℝ) ≤ b j := fun j => by rw [hbdef]; have := hWqnn j; positivity
  -- per (i,j) bound
  have hij : ∀ i j : Fin d,
      |⟪mulTest (isTestFn_mul hξ hξ) (Dg j) + mulTestPartial (isTestFn_mul hξ hξ) j D0,
          Sr i j⟫|
        ≤ A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
          + a j * ‖(u : H1amb Ω) i.succ‖ ^ 2 + b j * ‖D0‖ ^ 2 := by
    intro i j
    have hSrn : ‖Sr i j‖ ≤ hA.A1 * ‖(u : H1amb Ω) i.succ‖ := by
      rw [hSrdef]; exact norm_diffQuotD_actL_sub_le hA hΩm i j k hh ((u : H1amb Ω) i.succ)
    have hFn : ‖mulTest (isTestFn_mul hξ hξ) (Dg j)
          + mulTestPartial (isTestFn_mul hξ hξ) j D0‖
        ≤ Xi * ‖mulTest hξ (Dg j)‖ + Wq j * ‖D0‖ := by
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · exact norm_mulTest_sq_le hξ (Dg j)
      · exact norm_mulTestPartial_le (isTestFn_mul hξ hξ) j D0
    have hCS : |⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
          + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫|
        ≤ (Xi * ‖mulTest hξ (Dg j)‖ + Wq j * ‖D0‖) * (hA.A1 * ‖(u : H1amb Ω) i.succ‖) := by
      refine le_trans (abs_real_inner_le_norm _ _) (mul_le_mul hFn hSrn (norm_nonneg _) ?_)
      exact add_nonneg (mul_nonneg hXi (norm_nonneg _)) (mul_nonneg (hWqnn j) (norm_nonneg _))
    have hyoung := young_peterPaul (lam := A.lam / (4 * (d : ℝ))) (B := Xi * hA.A1)
      (x := ‖mulTest hξ (Dg j)‖) (y := ‖(u : H1amb Ω) i.succ‖)
      (by positivity)
    have hAM : Wq j * ‖D0‖ * (hA.A1 * ‖(u : H1amb Ω) i.succ‖)
        ≤ hA.A1 / 2 * Wq j * (‖D0‖ ^ 2 + ‖(u : H1amb Ω) i.succ‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖D0‖ - ‖(u : H1amb Ω) i.succ‖), mul_nonneg (hWqnn j) hA1,
        norm_nonneg D0, norm_nonneg ((u : H1amb Ω) i.succ)]
    have hlamsplit : A.lam / (4 * (d : ℝ)) / 2 = A.lam / (8 * (d : ℝ)) := by ring
    have hBsplit : (Xi * hA.A1) ^ 2 / (2 * (A.lam / (4 * (d : ℝ))))
        = (Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) := by
      rw [div_eq_iff (by positivity)]; field_simp; ring
    rw [hadef, hbdef]
    calc |⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
            + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫|
        ≤ (Xi * ‖mulTest hξ (Dg j)‖ + Wq j * ‖D0‖) * (hA.A1 * ‖(u : H1amb Ω) i.succ‖) := hCS
      _ = Xi * hA.A1 * ‖mulTest hξ (Dg j)‖ * ‖(u : H1amb Ω) i.succ‖
            + Wq j * ‖D0‖ * (hA.A1 * ‖(u : H1amb Ω) i.succ‖) := by ring
      _ ≤ A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
            + ((Xi * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam) + hA.A1 / 2 * Wq j)
                * ‖(u : H1amb Ω) i.succ‖ ^ 2 + hA.A1 / 2 * Wq j * ‖D0‖ ^ 2 := by
          rw [← hlamsplit, ← hBsplit]; nlinarith only [hyoung, hAM]
  -- sum the per-(i,j) bound
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hs1 : ∑ i : Fin d, ∑ j : Fin d,
        A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2 = A.lam / 8 * E := by
    rw [hEdef]
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hs2 : ∑ i : Fin d, ∑ j : Fin d, a j * ‖(u : H1amb Ω) i.succ‖ ^ 2
      = (∑ j : Fin d, a j) * U1 := by
    rw [hU1def, Finset.sum_mul_sum]
    exact Finset.sum_comm
  have hs3 : ∑ i : Fin d, ∑ j : Fin d, b j * ‖D0‖ ^ 2
      = (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2 := by
    simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hsum : ∑ i : Fin d, ∑ j : Fin d,
        (A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
          + a j * ‖(u : H1amb Ω) i.succ‖ ^ 2 + b j * ‖D0‖ ^ 2)
      = A.lam / 8 * E
        + ((∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2) := by
    simp only [Finset.sum_add_distrib]
    rw [hs1, hs2, hs3]
    ring
  -- assemble
  have hREST : -REST ≤ A.lam / 8 * E
      + ((∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2) := by
    rw [hRESTdef]
    have hle : |∑ i : Fin d, ∑ j : Fin d, ⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
          + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫|
        ≤ ∑ i : Fin d, ∑ j : Fin d,
            (A.lam / (8 * (d : ℝ)) * ‖mulTest hξ (Dg j)‖ ^ 2
              + a j * ‖(u : H1amb Ω) i.succ‖ ^ 2 + b j * ‖D0‖ ^ 2) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) (Finset.sum_le_sum ?_)
      intro i _
      exact le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ)
        (Finset.sum_le_sum (fun j _ => hij i j))
    rw [hsum] at hle
    exact le_trans (neg_le_abs _) hle
  -- data factors are ≤ P
  have hAsumnn : (0 : ℝ) ≤ ∑ j : Fin d, a j := Finset.sum_nonneg (fun j _ => hanN j)
  have hBsumnn : (0 : ℝ) ≤ (d : ℝ) * ∑ j : Fin d, b j :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hbnN j))
  change -REST ≤ A.lam / 8 * E
      + ((∑ j : Fin d, a j) + (d : ℝ) * ∑ j : Fin d, b j) / (2 * A.lam) * P
  have hdata : (∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2
      ≤ ((∑ j : Fin d, a j) + (d : ℝ) * ∑ j : Fin d, b j) / (2 * A.lam) * P := by
    have h1 : (∑ j : Fin d, a j) * U1 ≤ (∑ j : Fin d, a j) * (P / (2 * A.lam)) :=
      mul_le_mul_of_nonneg_left hU1P2 hAsumnn
    have h2 : (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2
        ≤ (d : ℝ) * (∑ j : Fin d, b j) * (P / (2 * A.lam)) :=
      mul_le_mul_of_nonneg_left hD0P hBsumnn
    calc (∑ j : Fin d, a j) * U1 + (d : ℝ) * (∑ j : Fin d, b j) * ‖D0‖ ^ 2
        ≤ (∑ j : Fin d, a j) * (P / (2 * A.lam))
            + (d : ℝ) * (∑ j : Fin d, b j) * (P / (2 * A.lam)) := add_le_add h1 h2
      _ = ((∑ j : Fin d, a j) + (d : ℝ) * ∑ j : Fin d, b j) / (2 * A.lam) * P := by ring
  linarith only [hREST, hdata]

private def interiorEnergyConstant (Op : FullEllipticOp d)
    (hA : IsLipCoeff Op.toEllipticCoeff) (hξ : IsTestFn Ω ξ) (k : Fin d) : ℝ :=
  let A := Op.toEllipticCoeff
  max 0 (4 / 3 * ((2 * (exists_abs_bound hξ).choose ^ 2 / A.lam
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam))
      + (((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
            / (2 * (A.lam / (4 * (d : ℝ))))
          + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
          + (d : ℝ) * (Op.Bsup
              * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2))
        / (2 * A.lam))
      + (2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam
        + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
        + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam))
      + ((d : ℝ) * ((2 * A.Λ * ∑ j : Fin d, (exists_abs_bound_partialD hξ j).choose) ^ 2
          / (2 * (A.lam / 4))) / (2 * A.lam))
      + (((∑ j : Fin d, (((exists_abs_bound hξ).choose * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam)
            + hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose))
          + (d : ℝ) * ∑ j : Fin d,
              hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose)
          / (2 * A.lam)))) * (2 + 4 * Op.gardingγ)

private lemma interiorEnergyConstant_nonneg (Op : FullEllipticOp d)
    (hA : IsLipCoeff Op.toEllipticCoeff) (hξ : IsTestFn Ω ξ) (k : Fin d) :
    0 ≤ interiorEnergyConstant Op hA hξ k := by
  dsimp only [interiorEnergyConstant]
  exact mul_nonneg (le_max_left _ _) (by nlinarith only [Op.gardingγ_nonneg])

/-- **First-order gradient bound.** Each gradient component of a weak solution is bounded in
`L²` by the data: `‖∂ᵢu‖ ≤ √((1 + 4γ) / (2λ)) (‖f‖ + ‖u₀‖)`, where `γ` is the Gårding shift
constant, through which the transport and zeroth-order coefficients enter. This is the
first-order energy estimate `firstOrder_energy_le` combined with the arithmetic-geometric
mean inequality. -/
lemma firstOrder_gradNorm_le (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (i : Fin d) :
    ‖(u : H1amb Ω) i.succ‖
      ≤ Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  have hlam : (0 : ℝ) < Op.lam := Op.toEllipticCoeff.lam_pos
  have hγnn : (0 : ℝ) ≤ Op.gardingγ := Op.gardingγ_nonneg
  let P: ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖
  have hPdef : P = ‖f‖ + ‖(u : H1amb Ω) 0‖ := rfl
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  have hfo : Op.lam / 2 * ∑ j : Fin d, ‖(u : H1amb Ω) j.succ‖ ^ 2
      ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ + Op.gardingγ * ‖(u : H1amb Ω) 0‖ ^ 2 :=
    firstOrder_energy_le Op u f hu
  have hdisqm : ‖(u : H1amb Ω) i.succ‖ ^ 2 * (Op.lam / 2)
      ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ + Op.gardingγ * ‖(u : H1amb Ω) 0‖ ^ 2 := by
    have hle : ‖(u : H1amb Ω) i.succ‖ ^ 2 ≤ ∑ j : Fin d, ‖(u : H1amb Ω) j.succ‖ ^ 2 :=
      single_le_sum_fin (fun j => ‖(u : H1amb Ω) j.succ‖ ^ 2) (fun j => sq_nonneg _) i
    nlinarith only [mul_le_mul_of_nonneg_left hle (by linarith only [hlam] :
      (0 : ℝ) ≤ Op.lam / 2), hfo]
  have hamgm : ‖f‖ * ‖(u : H1amb Ω) 0‖ ≤ P ^ 2 / 4 := by
    rw [hPdef]; nlinarith only [sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖)]
  have hu0P : ‖(u : H1amb Ω) 0‖ ^ 2 ≤ P ^ 2 := by
    rw [hPdef]; nlinarith only [norm_nonneg f, norm_nonneg ((u : H1amb Ω) 0)]
  have hrad : (0 : ℝ) ≤ (1 + 4 * Op.gardingγ) / (2 * Op.lam) := by positivity
  have hdiP : ‖(u : H1amb Ω) i.succ‖ ^ 2
      ≤ (1 + 4 * Op.gardingγ) / (2 * Op.lam) * P ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Op.lam)]
    have hprod : Op.gardingγ * ‖(u : H1amb Ω) 0‖ ^ 2 ≤ Op.gardingγ * P ^ 2 :=
      mul_le_mul_of_nonneg_left hu0P hγnn
    linarith only [hdisqm, hamgm, hprod]
  have hsq : (Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) * P) ^ 2
      = (1 + 4 * Op.gardingγ) / (2 * Op.lam) * P ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
  have hval : Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam) * P ^ 2)
      = Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) * P := by
    rw [← hsq]; exact Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hP0)
  rw [show ‖(u : H1amb Ω) i.succ‖ = Real.sqrt (‖(u : H1amb Ω) i.succ‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm, ← hval]
  exact Real.sqrt_le_sqrt hdiP

private theorem absorb_five_terms {lam E P x₁ x₂ x₃ x₄ x₅ C₁ C₂ C₃ C₄ C₅ : ℝ}
    (hP : 0 ≤ P) (h : lam * E ≤ x₁ - x₂ - x₃ - x₄ - x₅)
    (h₁ : x₁ ≤ lam / 8 * E + C₁ * P) (h₂ : -x₂ ≤ lam / 8 * E + C₂ * P)
    (h₃ : -x₃ ≤ lam / 8 * E + C₃ * P) (h₄ : -x₄ ≤ lam / 8 * E + C₄ * P)
    (h₅ : -x₅ ≤ lam / 8 * E + C₅ * P) :
    lam / 2 * E ≤ max 0 (4 / 3 * (C₁ + C₂ + C₃ + C₄ + C₅)) * P := by
  have hsum : lam / 2 * E ≤ (4 / 3 * (C₁ + C₂ + C₃ + C₄ + C₅)) * P := by
    have hdist : (4 / 3 * (C₁ + C₂ + C₃ + C₄ + C₅)) * P
        = 4 / 3 * (C₁ * P) + 4 / 3 * (C₂ * P) + 4 / 3 * (C₃ * P)
          + 4 / 3 * (C₄ * P) + 4 / 3 * (C₅ * P) := by ring
    rw [hdist]
    linarith only [h, h₁, h₂, h₃, h₄, h₅]
  exact hsum.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP)

/-- **Master interior difference-quotient energy estimate.** For a `W^{1,∞}`-coefficient
weak solution `u ∈ H₀¹(Ω)` of `L u = f`, an inner cutoff `ξ` and an
outer cutoff `θ ≡ 1` on the shift-reachable part of `tsupport ξ²`, the cutoff-weighted energy
of the interior difference quotient of the gradient is bounded by the data, uniformly in the
step `h`: `(λ/2) ∑ᵢ ‖ξ · Dₖ^h ∂ᵢu‖² ≤ C (‖f‖² + ‖u₀‖²)`. The constant is quantified before
the solution and the datum, so it depends only on
`λ, Λ, A₁, d, γ, ‖b‖∞, ‖c‖∞, ‖ξ‖∞, ‖∂ξ‖∞`, and on none of `u`, `f`, `h`. Testing the weak
formulation with the
admissible Evans element `v_h = -Dₖ^{-h}(ξ² Dₖ^h u)`, discrete integration by parts
(`evansTest_bilin_L2D`) moves the outer difference quotient onto the coefficient action; the
discrete Leibniz split (`norm_diffQuotD_actL_sub_le`) exposes the translated-coefficient
leading term, controlled from below by ellipticity (`energy_ge` for the translate, same `λ`);
Cauchy-Schwarz and the Peter-Paul inequality absorb the commutator, cross, transport,
zeroth-order and right-hand terms, five families each spending an eighth of the ellipticity
lower bound, with the first-order energy bound `firstOrder_energy_le` supplying all gradient
data
(Evans, *Partial Differential Equations* (2nd ed.), §6.3.1; Gilbarg-Trudinger, *Elliptic
PDE of Second Order*, Theorem 8.8). -/
theorem interior_diffQuot_energy_bound (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    (hξ : IsTestFn Ω ξ) (hθ : IsTestFn Ω θ) (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ (h : ℝ), h ≠ 0 →
      (∀ x ∈ tsupport (fun y => ξ y * ξ y), x + hshift k h ∈ Ω) →
      (∀ x ∈ tsupport θ, x + hshift k (-h) ∈ Ω) →
      (∀ x ∈ Ω,
        x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
          → θ x = 1) →
      (∀ (j : Fin d), ∀ x ∈ Ω,
        x ∈ tsupport (fun y => ξ y * ξ y) ∨ x + hshift k (-h) ∈ tsupport (fun y => ξ y * ξ y)
          → partialD j θ x = 0) →
      Op.lam / 2 * ∑ i : Fin d,
        ‖extendL2 hΩm (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0; exact ⟨0, le_refl 0, fun _ _ _ _ _ _ _ _ _ => k.elim0⟩
  let A := Op.toEllipticCoeff
  have hγnn : (0 : ℝ) ≤ Op.gardingγ := Op.gardingγ_nonneg
  refine ⟨interiorEnergyConstant Op hA hξ k,
    interiorEnergyConstant_nonneg Op hA hξ k, ?_⟩
  dsimp only [interiorEnergyConstant]
  intro u f hu h hh hsm_in hsm_out hθ1 hθ0
  let A' := A.translate (hshift k h)
  let Dg : Fin d → L2D Ω := fun i => diffQuotD k h hΩm ((u : H1amb Ω) i.succ)
  let D0 : L2D Ω := diffQuotD k h hΩm ((u : H1amb Ω) 0)
  let v : H01 Ω := evansTest hΩm hξ hθ k h hsm_in hsm_out u
  have hvdef : v = evansTest hΩm hξ hθ k h hsm_in hsm_out u := rfl
  let E : ℝ := ∑ i : Fin d, ‖mulTest hξ (Dg i)‖ ^ 2
  have hEdef : E = ∑ i : Fin d, ‖mulTest hξ (Dg i)‖ ^ 2 := rfl
  let P : ℝ := (2 + 4 * Op.gardingγ) * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2)
  have hPdef : P = (2 + 4 * Op.gardingγ) * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := rfl
  let U1 : ℝ := ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2
  have hU1def : U1 = ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 := rfl
  -- Commutator remainder classes.
  let Sr : Fin d → Fin d → L2D Ω := fun i j =>
    diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ)) - A'.actL i j (Dg i)
  have hSrdef : Sr = fun i j =>
    diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ)) - A'.actL i j (Dg i) := rfl
  -- The three families of the bilinear form.
  let LEAD : ℝ := ∑ i : Fin d, ∑ j : Fin d, ⟪A'.actL i j (mulTest hξ (Dg i)),
      mulTest hξ (Dg j)⟫
  have hLEADdef : LEAD = ∑ i : Fin d, ∑ j : Fin d, ⟪A'.actL i j (mulTest hξ (Dg i)),
      mulTest hξ (Dg j)⟫ := rfl
  let CROSS : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫
  have hCROSSdef : CROSS = ∑ i : Fin d, ∑ j : Fin d,
      2 * ⟪A'.actL i j (mulTest hξ (Dg i)), mulTestPartial hξ j D0⟫ := rfl
  let REST : ℝ := ∑ i : Fin d, ∑ j : Fin d,
      ⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
        + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫
  have hRESTdef : REST = ∑ i : Fin d, ∑ j : Fin d,
      ⟪mulTest (isTestFn_mul hξ hξ) (Dg j)
        + mulTestPartial (isTestFn_mul hξ hξ) j D0, Sr i j⟫ := rfl
  -- Keep the enormous Evans-test term and the real aggregates opaque so downstream
  -- `isDefEq`/`linarith` stay cheap, while `Dg`/`D0`/`Sr` remain definitionally foldable.
  clear_value v E P U1 LEAD CROSS REST
  -- nonnegativity facts
  have hlam : (0 : ℝ) < A.lam := A.lam_pos
  have hEnn : (0 : ℝ) ≤ E := by rw [hEdef]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- LHS reduction via the extension isometry.
  have hLHS : ∑ i : Fin d,
      ‖extendL2 hΩm (mulTest hξ (diffQuotD k h hΩm ((u : H1amb Ω) i.succ)))‖ ^ 2 = E := by
    rw [hEdef]; simp only [Dg]; simp_rw [norm_extendL2]
  rw [hLHS]
  -- The bilinear identity, expanded into the three families.
  have hbil : A.bilin Ω u v = LEAD + CROSS + REST := by
    rw [hLEADdef, hCROSSdef, hRESTdef, hvdef,
      evansTest_bilin_L2D A hΩm hξ hθ k h hsm_in hsm_out hθ1 hθ0 u]
    simp only [Dg, D0, hSrdef]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hSreq : diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
        = A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))
          + (diffQuotD k h hΩm (A.actL i j ((u : H1amb Ω) i.succ))
              - A'.actL i j (diffQuotD k h hΩm ((u : H1amb Ω) i.succ))) := by abel
    have key_lead : ∀ p q : L2D Ω,
        ⟪mulTest (isTestFn_mul hξ hξ) q, A'.actL i j p⟫
          = ⟪A'.actL i j (mulTest hξ p), mulTest hξ q⟫ := fun p q => by
      rw [real_inner_comm, ← actL_mulTest_regroup A' hξ i j p q]
    have key_cross : ∀ p q : L2D Ω,
        ⟪mulTestPartial (isTestFn_mul hξ hξ) j q, A'.actL i j p⟫
          = 2 * ⟪A'.actL i j (mulTest hξ p), mulTestPartial hξ j q⟫ := fun p q => by
      rw [real_inner_comm, actL_cross_regroup A' hξ i j p q]
    conv_lhs =>
      rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply, hSreq, inner_add_right,
        inner_add_left, key_lead, key_cross]
  have hRHSeq : (∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) = ⟪f, (v : H1amb Ω) 0⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.inner_apply]
  have hweak : A.bilin Ω u v = ⟪f, (v : H1amb Ω) 0⟫
      - (∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫)
      - ⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ := by
    have hfull := hu v
    rw [Op.fullBilin_apply, Op.lowerBilin_apply, hRHSeq] at hfull
    linarith [hfull]
  -- LEAD lower bound from ellipticity of the translated coefficients.
  have hLE : A.lam * E ≤ LEAD := by
    have h := energy_ge A' (fun i => mulTest hξ (Dg i))
    rw [hLEADdef, hEdef]
    exact h
  -- first-order energy: U1 ≤ P/(2λ).
  have hU1half : A.lam / 2 * U1
      ≤ ‖f‖ * ‖(u : H1amb Ω) 0‖ + Op.gardingγ * ‖(u : H1amb Ω) 0‖ ^ 2 := by
    rw [hU1def]; exact firstOrder_energy_le Op u f hu
  have hfu2 : ‖f‖ * ‖(u : H1amb Ω) 0‖ ≤ P / 2 := by
    have hsq := sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖)
    rw [hPdef]; nlinarith only [hsq, hγnn, sq_nonneg ‖f‖, sq_nonneg ‖(u : H1amb Ω) 0‖]
  have hU1P : A.lam * U1 ≤ P / 2 := by
    have hsq := sq_nonneg (‖f‖ - ‖(u : H1amb Ω) 0‖)
    rw [hPdef]
    nlinarith only [hU1half, hsq, hγnn, sq_nonneg ‖(u : H1amb Ω) 0‖, sq_nonneg ‖f‖]
  have hU1nn : (0 : ℝ) ≤ U1 := by rw [hU1def]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnD0 : ‖D0‖ ^ 2 ≤ U1 := by
    dsimp only [D0]
    rw [ hU1def]; exact sq_norm_diffQuotD_u0_le hΩm k h u
  have hU1P2 : U1 ≤ P / (2 * A.lam) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A.lam)]; nlinarith only [hU1P]
  have hD0P : ‖D0‖ ^ 2 ≤ P / (2 * A.lam) := le_trans hnD0 hU1P2
  have hPnn : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
  -- Shared: the function value of the Evans element is a `√E`-factor plus data.
  have hmk : ‖mulTest hξ (Dg k)‖ ^ 2 ≤ E := by
    rw [hEdef]
    exact single_le_sum_fin (fun i => ‖mulTest hξ (Dg i)‖ ^ 2) (fun i => sq_nonneg _) k
  have hXinn : (0 : ℝ) ≤ (exists_abs_bound hξ).choose :=
    le_trans (abs_nonneg _) ((exists_abs_bound hξ).choose_spec 0)
  have hWknn : (0 : ℝ) ≤ (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose :=
    le_trans (abs_nonneg _)
      ((exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose_spec 0)
  have hv0 : ‖(v : H1amb Ω) 0‖
      ≤ (exists_abs_bound hξ).choose * ‖mulTest hξ (Dg k)‖
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose * ‖D0‖ := by
    have hz0 : (v : H1amb Ω) 0 = -diffQuotD k (-h) hΩm
        ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0) := by
      rw [hvdef]; exact evansTest_zero_eq hΩm hξ hθ k h hsm_in hsm_out u hθ1
    have hbnd : ‖diffQuotD k (-h) hΩm
          ((cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) 0)‖
        ≤ ‖(cutoffMul (isTestFn_mul hξ hξ) (diffQuotG k h hΩm (u : H1amb Ω))) k.succ‖ :=
      norm_diffQuotD_u0_le hΩm k (-h)
        ⟨_, cutoffMul_diffQuotG_mem_H01 (isTestFn_mul hξ hξ) k hΩm hsm_in u.2⟩
    rw [hz0, norm_neg]
    refine le_trans hbnd ?_
    rw [cutoffMul_apply_succ, diffQuotG_apply, diffQuotG_apply]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact norm_mulTest_sq_le hξ (diffQuotD k h hΩm ((u : H1amb Ω) k.succ))
    · exact norm_mulTestPartial_le (isTestFn_mul hξ hξ) k (diffQuotD k h hΩm ((u : H1amb Ω) 0))
  -- The four family bounds (each `≤ (λ/8) E + Cᵢ P`).
  have hfv : ⟪f, (v : H1amb Ω) 0⟫ ≤ A.lam / 8 * E
      + (2 * (exists_abs_bound hξ).choose ^ 2 / A.lam
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
        + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam)) * P := by
    exact energy_rhs_bound Op hΩm hξ k hγnn u f h v E P hPdef hlam hD0P hmk hWknn hv0
  have hbv : -(∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫)
      ≤ A.lam / 8 * E
        + (((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
              / (2 * (A.lam / (4 * (d : ℝ))))
            + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
            + (d : ℝ) * (Op.Bsup
                * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2))
          / (2 * A.lam)) * P := by
    exact energy_transport_bound Op hΩm hξ k hd u h v E P U1 hU1def hlam hU1P2 hD0P hmk hWknn hv0
  have hcv : -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ ≤ A.lam / 8 * E
      + (2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam
        + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
        + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam))
        * P := by
    exact energy_zeroth_bound Op hΩm hξ k hγnn u f h v E P hPdef hlam hD0P hmk hWknn hv0
  have hcr : -CROSS ≤ A.lam / 8 * E
      + ((d : ℝ) * ((2 * A.Λ * ∑ j : Fin d, (exists_abs_bound_partialD hξ j).choose) ^ 2
          / (2 * (A.lam / 4))) / (2 * A.lam)) * P := by
    exact energy_cross_bound Op hΩm hξ k u h E hEdef P CROSS hCROSSdef hD0P
  have hre : -REST ≤ A.lam / 8 * E
      + (((∑ j : Fin d, (((exists_abs_bound hξ).choose * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam)
            + hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose))
          + (d : ℝ) * ∑ j : Fin d,
              hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose)
          / (2 * A.lam)) * P := by
    exact energy_commutator_bound Op hΩm hA hξ k hd u h hh E hEdef P U1 hU1def hSrdef REST
      hRESTdef hU1P2 hD0P
  -- Fold the five (data-only, `h`-independent) constant expressions.
  let Cf : ℝ := 2 * (exists_abs_bound hξ).choose ^ 2 / A.lam
      + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
      + (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam)
  let Cb : ℝ := ((Op.Bsup * (exists_abs_bound hξ).choose) ^ 2
        / (2 * (A.lam / (4 * (d : ℝ))))
      + Op.Bsup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
      + (d : ℝ) * (Op.Bsup
          * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2))
    / (2 * A.lam)
  let Cc : ℝ := 2 * (Op.Csup * (exists_abs_bound hξ).choose) ^ 2 / A.lam
      + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / 2
      + Op.Csup * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) k).choose / (4 * A.lam)

  let Ccr : ℝ := (d : ℝ) * ((2 * A.Λ * ∑ j : Fin d, (exists_abs_bound_partialD hξ j).choose) ^ 2
        / (2 * (A.lam / 4))) / (2 * A.lam)
  let Cre : ℝ := ((∑ j : Fin d, (((exists_abs_bound hξ).choose * hA.A1) ^ 2 * (2 * (d : ℝ) / A.lam)
          + hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose))
        + (d : ℝ) * ∑ j : Fin d,
            hA.A1 / 2 * (exists_abs_bound_partialD (isTestFn_mul hξ hξ) j).choose)
        / (2 * A.lam)
  have hcomb : A.lam * E ≤ ⟪f, (v : H1amb Ω) 0⟫
      - (∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫)
      - ⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ - CROSS - REST := by
    rw [← hweak]; linarith only [hLE, hbil]
  change A.lam / 2 * E
      ≤ max 0 (4 / 3 * (Cf + Cb + Cc + Ccr + Cre)) * (2 + 4 * Op.gardingγ)
          * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2)
  rw [show max 0 (4 / 3 * (Cf + Cb + Cc + Ccr + Cre)) * (2 + 4 * Op.gardingγ)
        * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2)
      = max 0 (4 / 3 * (Cf + Cb + Cc + Ccr + Cre)) * P from by rw [hPdef]; ring]
  -- Five Peter-Paul families each spend `λ/8` of the ellipticity lower bound `λ E`,
  -- leaving `3λ/8 E`, so the target `λ/2 E` needs a factor `4/3` on the constant.
  change ⟪f, (v : H1amb Ω) 0⟫ ≤ A.lam / 8 * E + Cf * P at hfv
  change -(∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ), (v : H1amb Ω) 0⟫) ≤ A.lam / 8 * E +
    Cb * P at hbv
  change -⟪Op.cAct ((u : H1amb Ω) 0), (v : H1amb Ω) 0⟫ ≤ A.lam / 8 * E + Cc * P at hcv
  change -CROSS ≤ A.lam / 8 * E + Ccr * P at hcr
  change -REST ≤ A.lam / 8 * E + Cre * P at hre
  exact absorb_five_terms hPnn hcomb hfv hbv hcv hcr hre

end EllipticPdes.Regularity
