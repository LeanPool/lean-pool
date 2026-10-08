/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.PartialVec

/-!
# The second-order elliptic identity `‖∇²v‖² = ‖∇ curl v‖² + ‖∇ div v‖²`

This file proves the second-order form of `eq:aniso:closure:elliptic` of
*Regularity of asymptotically axisymmetric solutions to the 3D Navier–Stokes equations with
analytic forcing*, arXiv:2609.20803: for a smooth, compactly supported vector field
`v : Vec3 → Vec3`, the Hessian energy `∫ ∑ᵢⱼₖ (∂ₖ∂ⱼvᵢ)²` splits as `∫ ‖∇ curl v‖²` plus
`∫ ‖∇ div v‖²`.

The proof differentiates the first-order identity `integral_sq_fderiv_eq_curl_add_div` of
`CIV.Analysis.DivCurl`. Applying it to the field `∂ₖv = partialVec v k`, which is again smooth
with compact support, and using that `∂ₖ` commutes with both `curl` and `div`
(`curlVec_partialVec`, `div_partialVec`), gives for each direction `k`

`∫ ‖∇ ∂ₖv‖² = ∫ ‖∂ₖ curl v‖² + ∫ (∂ₖ div v)²`.

Summing the three identities and using `sum_sq_partialVec_eq` to recognise the left-hand side as
the Hessian energy of `v` gives the statement. No new integration by parts is performed here: the
one that matters is already inside the first-order identity.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



/-! ### Regularity of the curl -/

/-- Off the support of `v`, every first derivative of every component of `v` vanishes. -/
private lemma fderiv_comp_eq_zero_of_notMem_tsupport (v : Vec3 → Vec3) {x : Vec3}
    (hx : x ∉ tsupport v) (a : Fin 3) : fderiv ℝ (fun y : Vec3 => v y a) x = 0 := by
  have hnhds : ∀ᶠ y in nhds x, v y = 0 := by
    filter_upwards [(isClosed_tsupport v).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hEq : (fun y : Vec3 => v y a) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [hnhds] with y hy
    rw [hy]
    rfl
  rw [hEq.fderiv_eq]
  simp

/-- The curl of a smooth vector field is smooth. -/
theorem contDiff_curlVec (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (curlVec v) := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i
  · exact (contDiff_fderiv_comp v hv 2 1).sub (contDiff_fderiv_comp v hv 1 2)
  · exact (contDiff_fderiv_comp v hv 0 2).sub (contDiff_fderiv_comp v hv 2 0)
  · exact (contDiff_fderiv_comp v hv 1 0).sub (contDiff_fderiv_comp v hv 0 1)

/-- The curl of a compactly supported vector field has compact support. -/
theorem hasCompactSupport_curlVec (v : Vec3 → Vec3) (hsupp : HasCompactSupport v) :
    HasCompactSupport (curlVec v) := by
  refine HasCompactSupport.intro hsupp fun x hx => ?_
  have hzero : ∀ a : Fin 3, fderiv ℝ (fun y : Vec3 => v y a) x = 0 := fun a =>
    fderiv_comp_eq_zero_of_notMem_tsupport v hx a
  funext i
  fin_cases i <;> simp [curlVec, hzero]

/-- The gradient energy of the curl is integrable for a smooth compactly supported field. -/
theorem integrable_sum_sq_fderiv_curlVec (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun k _ =>
      integrable_sq_fderiv_comp (curlVec v) (hasCompactSupport_curlVec v hsupp)
        (contDiff_curlVec v hv) i k

/-! ### Regularity of the divergence -/

/-- The divergence of a smooth vector field is a smooth scalar. -/
private lemma contDiff_divergence (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) :=
  ContDiff.sum fun j _ => contDiff_fderiv_comp v hv j j

/-- The divergence of a compactly supported vector field has compact support. -/
private lemma hasCompactSupport_divergence (v : Vec3 → Vec3) (hsupp : HasCompactSupport v) :
    HasCompactSupport (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) := by
  refine HasCompactSupport.intro hsupp fun x hx => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [fderiv_comp_eq_zero_of_notMem_tsupport v hx j]
  rfl

/-- A coordinate derivative of the divergence is continuous. -/
private lemma continuous_fderiv_divergence (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (k : Fin 3) :
    Continuous (fun x : Vec3 => fderiv ℝ (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec k)) := by
  have h_cont : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) p.1) p.2) :=
    (contDiff_divergence v hv).continuous_fderiv_apply (by simp)
  exact h_cont.comp (continuous_id.prodMk continuous_const)

/-- The square of a coordinate derivative of the divergence is integrable. -/
private lemma integrable_sq_fderiv_divergence (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) (k : Fin 3) :
    Integrable (fun x : Vec3 => (fderiv ℝ (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec k)) ^ 2) := by
  have hcs : HasCompactSupport (fun x : Vec3 => fderiv ℝ (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec k)) :=
    (hasCompactSupport_divergence v hsupp).fderiv_apply (𝕜 := ℝ) (basisVec k)
  have h := integrable_mul_of_continuous_of_hasCompactSupport
    (continuous_fderiv_divergence v hv k) (continuous_fderiv_divergence v hv k) hcs
  simpa [sq] using h

/-! ### The integrability of the three energies, direction by direction -/

/-- The gradient energy of `∂ₖv` is integrable. -/
private lemma integrable_sum_sq_fderiv_partialVec (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hsupp : HasCompactSupport v) (k : Fin 3) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => partialVec v k y i) x (basisVec j)) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_sq_fderiv_comp (partialVec v k) (hasCompactSupport_partialVec v hsupp k)
        (contDiff_partialVec v hv k) i j

/-- The energy of `∂ₖ curl v` is integrable. -/
private lemma integrable_sum_sq_fderiv_curlVec_dir (v : Vec3 → Vec3)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hsupp : HasCompactSupport v) (k : Fin 3) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ =>
    integrable_sq_fderiv_comp (curlVec v) (hasCompactSupport_curlVec v hsupp)
      (contDiff_curlVec v hv) i k

/-! ### The second-order identity -/

/-- **The second-order elliptic identity** `‖∇²v‖² = ‖∇ curl v‖² + ‖∇ div v‖²` for a smooth
compactly supported vector field on `ℝ³`. It is the first-order identity
`integral_sq_fderiv_eq_curl_add_div` applied to each directional derivative `∂ₖv` and summed
over the three directions. -/
theorem integral_sq_fderiv_fderiv_eq_curl_add_div (v : Vec3 → Vec3)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hsupp : HasCompactSupport v) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) x
          (basisVec k)) ^ 2
      = (∫ x : Vec3, ∑ i : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2)
        + ∫ x : Vec3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
                (basisVec k)) ^ 2 := by
  have hdir : ∀ k : Fin 3,
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => partialVec v k y i) x (basisVec j)) ^ 2)
        = (∫ x : Vec3, ∑ i : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2)
          + ∫ x : Vec3, (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
                (basisVec k)) ^ 2 := by
    intro k
    have hbase := integral_sq_fderiv_eq_curl_add_div (partialVec v k)
      (contDiff_partialVec v hv k) (hasCompactSupport_partialVec v hsupp k)
    have hcurl : (∫ x : Vec3, ∑ i : Fin 3, (curlVec (partialVec v k) x i) ^ 2)
        = ∫ x : Vec3, ∑ i : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [congrFun (curlVec_partialVec v hv k x) i]
    have hdiv : (∫ x : Vec3, (∑ j : Fin 3,
          fderiv ℝ (fun y : Vec3 => partialVec v k y j) x (basisVec j)) ^ 2)
        = ∫ x : Vec3, (fderiv ℝ (fun y : Vec3 =>
            ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
              (basisVec k)) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact congrArg (fun s : ℝ => s ^ 2) (div_partialVec v hv k x)
    rw [← hcurl, ← hdiv]
    exact hbase
  calc
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) x
          (basisVec k)) ^ 2
        = ∫ x : Vec3, ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => partialVec v k y i) x (basisVec j)) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (sum_sq_partialVec_eq v hv x).symm)
    _ = ∑ k : Fin 3, ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => partialVec v k y i) x (basisVec j)) ^ 2 :=
      integral_finsetSum Finset.univ fun k _ =>
        integrable_sum_sq_fderiv_partialVec v hv hsupp k
    _ = ∑ k : Fin 3, ((∫ x : Vec3, ∑ i : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2)
          + ∫ x : Vec3, (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
                (basisVec k)) ^ 2) :=
      Finset.sum_congr rfl fun k _ => hdir k
    _ = (∑ k : Fin 3, ∫ x : Vec3, ∑ i : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2)
          + ∑ k : Fin 3, ∫ x : Vec3, (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
                (basisVec k)) ^ 2 := Finset.sum_add_distrib
    _ = (∫ x : Vec3, ∑ k : Fin 3, ∑ i : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2)
          + ∫ x : Vec3, ∑ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
                (basisVec k)) ^ 2 := by
      rw [integral_finsetSum Finset.univ fun k _ =>
          integrable_sum_sq_fderiv_curlVec_dir v hv hsupp k,
        integral_finsetSum Finset.univ fun k _ => integrable_sq_fderiv_divergence v hv hsupp k]
    _ = (∫ x : Vec3, ∑ i : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k)) ^ 2)
          + ∫ x : Vec3, ∑ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
                (basisVec k)) ^ 2 := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => Finset.sum_comm)

end CIV
