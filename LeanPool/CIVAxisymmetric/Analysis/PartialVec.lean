/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.DivCurl

/-!
# The directional derivative of a vector field as a vector field

For a vector field `v : Vec3 → Vec3` and a coordinate direction `k`, the field `partialVec v k`
is `∂_k v`, again a vector field on `Vec3`. It is introduced as a named definition, not as an
inline nest of `fderiv`s, because every second-order statement of the elliptic identity
`eq:aniso:closure:elliptic` differentiates twice: written out, such a term is a lambda inside a
lambda with no head symbol for the unifier to key on, and terms of that shape elaborate very
badly. With the definition in place the unifier sees `partialVec` applied to arguments.

The file records that `∂_k v` inherits smoothness and compact support from `v`, and that `∂_k`
commutes with both first-order differential operators of the identity:

* `curlVec_partialVec` — `curl (∂_k v) = ∂_k (curl v)`;
* `div_partialVec` — `div (∂_k v) = ∂_k (div v)`;
* `sum_sq_partialVec_eq` — summing `|∇(∂_k v)|²` over `k` recovers the full Hessian energy
  `|∇²v|²`.

All three rest on the symmetry of the second derivative, which is the `fderiv_fderiv_comp_symm`
of `CIV.Analysis.DivCurl`.
-/

public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



/-- The derivative of the vector field `v` in the coordinate direction `k`, as a vector field:
`partialVec v k x i = ∂_k v_i (x)`. -/
@[expose] def partialVec (v : Vec3 → Vec3) (k : Fin 3) (x : Vec3) : Vec3 :=
  fun i => fderiv ℝ (fun y : Vec3 => v y i) x (basisVec k)

/-- The controlled unfolding channel for `partialVec`: its `i`-th component is the `k`-th partial
derivative of the `i`-th component of `v`. -/
theorem partialVec_apply (v : Vec3 → Vec3) (k : Fin 3) (x : Vec3) (i : Fin 3) :
    partialVec v k x i = fderiv ℝ (fun y : Vec3 => v y i) x (basisVec k) := by
  rfl

/-- `∂_k v` is smooth whenever `v` is. -/
theorem contDiff_partialVec (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (partialVec v k) := by
  refine contDiff_pi.mpr fun i => ?_
  exact contDiff_fderiv_comp v hv i k

/-- `∂_k v` has compact support whenever `v` does: off the support of `v` the field vanishes on a
whole neighbourhood, so all of its derivatives vanish there. -/
theorem hasCompactSupport_partialVec (v : Vec3 → Vec3) (hsupp : HasCompactSupport v) (k : Fin 3) :
    HasCompactSupport (partialVec v k) := by
  refine HasCompactSupport.intro hsupp fun x hx => ?_
  have hnhds : ∀ᶠ y in nhds x, v y = 0 := by
    filter_upwards [(isClosed_tsupport v).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  funext i
  have hEq : (fun y : Vec3 => v y i) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [hnhds] with y hy
    rw [hy]
    rfl
  have hzero : fderiv ℝ (fun y : Vec3 => v y i) x = 0 := by
    rw [hEq.fderiv_eq]
    simp
  simp [partialVec, hzero]

/-- Reading one partial derivative of `∂_k v` as a mixed second derivative of `v`, with the two
directions already swapped by the symmetry of the second derivative. -/
private lemma fderiv_partialVec_comp (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (k a b : Fin 3) (x : Vec3) :
    fderiv ℝ (fun y : Vec3 => partialVec v k y a) x (basisVec b)
      = fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z a) y (basisVec b)) x
          (basisVec k) := by
  have hdef : (fun y : Vec3 => partialVec v k y a)
      = fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z a) y (basisVec k) := rfl
  rw [hdef]
  exact fderiv_fderiv_comp_symm (fun z : Vec3 => v z a) (contDiff_comp v hv a) k b x

/-- One entry of the curl of `∂_k v` is the `k`-th derivative of the corresponding entry of the
curl of `v`. -/
private lemma curlVec_partialVec_entry (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (k a b : Fin 3) (x : Vec3) :
    fderiv ℝ (fun y : Vec3 => partialVec v k y a) x (basisVec b)
        - fderiv ℝ (fun y : Vec3 => partialVec v k y b) x (basisVec a)
      = fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z a) y (basisVec b)
          - fderiv ℝ (fun z : Vec3 => v z b) y (basisVec a)) x (basisVec k) := by
  have hsub : fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z a) y (basisVec b)
        - fderiv ℝ (fun z : Vec3 => v z b) y (basisVec a)) x
      = fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z a) y (basisVec b)) x
        - fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z b) y (basisVec a)) x :=
    fderiv_fun_sub (differentiableAt_fderiv_comp v hv a b x)
      (differentiableAt_fderiv_comp v hv b a x)
  rw [fderiv_partialVec_comp v hv k a b x, fderiv_partialVec_comp v hv k b a x, hsub, sub_apply]

/-- **`curl` commutes with `∂_k`.** -/
theorem curlVec_partialVec (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin 3) (x : Vec3) :
    curlVec (partialVec v k) x
      = fun i : Fin 3 => fderiv ℝ (fun y : Vec3 => curlVec v y i) x (basisVec k) := by
  funext i
  fin_cases i <;> simp only [curlVec]
  · exact curlVec_partialVec_entry v hv k 2 1 x
  · exact curlVec_partialVec_entry v hv k 0 2 x
  · exact curlVec_partialVec_entry v hv k 1 0 x

/-- **`div` commutes with `∂_k`.** -/
theorem div_partialVec (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin 3) (x : Vec3) :
    (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => partialVec v k y j) x (basisVec j))
      = fderiv ℝ (fun y : Vec3 =>
          ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x (basisVec k) := by
  have hsum : fderiv ℝ (fun y : Vec3 =>
        ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x
      = ∑ j : Fin 3,
          fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z j) y (basisVec j)) x :=
    fderiv_fun_sum fun j _ => differentiableAt_fderiv_comp v hv j j x
  rw [hsum, sum_apply]
  exact Finset.sum_congr rfl fun j _ => fderiv_partialVec_comp v hv k j j x

/-- Summing the gradient energy of `∂_k v` over the three directions `k` recovers the full
Hessian energy of `v`. -/
theorem sum_sq_partialVec_eq (v : Vec3 → Vec3) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec3) :
    ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => partialVec v k y i) x (basisVec j)) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z i) y (basisVec j)) x
            (basisVec k)) ^ 2 := by
  have hentry : ∀ k a b : Fin 3,
      (fderiv ℝ (fun y : Vec3 => partialVec v k y a) x (basisVec b)) ^ 2
        = (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => v z a) y (basisVec b)) x
            (basisVec k)) ^ 2 := by
    intro k a b
    rw [fderiv_partialVec_comp v hv k a b x]
  simp only [hentry, Fin.sum_univ_three]
  ring

end CIV
