/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EllipticBounds

/-!
# Moving a cutoff across two derivatives

The mixed-term estimate of `lem:aniso:closure` controls `χ ∇²v`, while the elliptic bounds of
`eq:aniso:closure:elliptic` control `∇²(χ v)`. This file is the bridge between the two: for a
cutoff `χ` that is smooth and compactly supported inside an open set `U` and a field `v` smooth
on `U`,

`∫ χ² |∇²v|² ≤ 4 ∫ |∇²(χ v)|² + 16 N² ∫ |∇χ|² + 16 N² ∫ |∇²χ|²`,

where `N` bounds the full first-order jet `|v|² + |∇v|²` of `v` on the support of `∇χ`.

The proof is pointwise plus one monotonicity step. Twice applying the Leibniz rule on `U` gives

`χ ∂_k∂_j v_i = ∂_k∂_j(χ v_i) - (∂_kχ)(∂_j v_i) - (∂_jχ)(∂_k v_i) - (∂_k∂_jχ) v_i`,

and `(a - b - c - d)² ≤ 4(a² + b² + c² + d²)` turns this into a pointwise bound whose three error
terms carry a derivative of `χ`, hence are supported where the jet bound applies. Off `U` the
cutoff vanishes, so the left-hand side is zero there and the pointwise bound is trivial.

Only the majorant has to be integrable: the bound is applied through `integral_mono_of_nonneg`,
whose left-hand function need not be assumed integrable.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### Vanishing near a point outside the support -/

/-- A function vanishes on a whole neighbourhood of any point outside its support. -/
theorem eventuallyEq_zero_nhds_of_notMem_tsupport {M : Type*} [Zero M] (f : Vec3 → M)
    {x : Vec3} (hx : x ∉ tsupport f) : f =ᶠ[nhds x] fun _ : Vec3 => (0 : M) := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

/-! ### Smoothness of the first derivatives -/

/-- A coordinate derivative of a component of a field smooth on an open set is smooth there. -/
theorem contDiffOn_fderiv_comp_apply {V : Vec3 → Vec3} {U : Set Vec3} (hU : IsOpen U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) (i j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) U := by
  have hVi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 => V z i) U := (contDiffOn_pi.mp hV) i
  exact (hVi.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- A coordinate derivative of a smooth scalar is smooth. -/
theorem contDiff_fderiv_apply_scalar (G : Vec3 → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ G x (basisVec j)) :=
  (hG.fderiv_right (by simp)).clm_apply contDiff_const

/-- A coordinate derivative of a smooth scalar is continuous. -/
theorem continuous_fderiv_apply_scalar (G : Vec3 → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (j : Fin 3) : Continuous (fun x : Vec3 => fderiv ℝ G x (basisVec j)) :=
  (contDiff_fderiv_apply_scalar G hG j).continuous

/-! ### The Leibniz rule, once and twice -/

/-- One derivative of a cutoff product, componentwise. -/
private lemma fderiv_smul_comp_apply (w : Vec3 → ℝ) (V : Vec3 → Vec3) (i j : Fin 3) {x : Vec3}
    (hw : DifferentiableAt ℝ w x) (hV : DifferentiableAt ℝ (fun z : Vec3 => V z i) x) :
    fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)
      = w x * fderiv ℝ (fun z : Vec3 => V z i) x (basisVec j) + gradVec w x j * V x i := by
  have hfun : (fun y : Vec3 => (w y • V y) i) = fun y : Vec3 => w y * V y i := rfl
  rw [hfun, fderiv_fun_mul hw hV]
  simp only [add_apply, smul_apply, smul_eq_mul, gradVec]
  ring

/-- **The second-order Leibniz rule for a cutoff product.** On the open set where the field is
smooth, `χ ∂_k∂_j v_i` differs from `∂_k∂_j(χ v_i)` by three terms, each carrying a derivative
of the cutoff. -/
private lemma fderiv_fderiv_smul_comp_apply (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (i j k : Fin 3) {x : Vec3} (hx : x ∈ U) :
    w x * fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x
        (basisVec k)
      = fderiv ℝ (fun y : Vec3 =>
            fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)
        - gradVec w x k * fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)
        - gradVec w x j * fderiv ℝ (fun y : Vec3 => V y i) x (basisVec k)
        - fderiv ℝ (fun y : Vec3 => gradVec w y j) x (basisVec k) * V x i := by
  have hVi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 => V z i) U := (contDiffOn_pi.mp hV) i
  have hVdiff : ∀ y ∈ U, DifferentiableAt ℝ (fun z : Vec3 => V z i) y := fun y hy =>
    (hVi.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have hwdiff : ∀ y : Vec3, DifferentiableAt ℝ w y := fun y => hw.differentiable (by simp) y
  have hAdiff : DifferentiableAt ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x :=
    ((contDiffOn_fderiv_comp_apply hU hV i j).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hx)
  have hBdiff : DifferentiableAt ℝ (fun y : Vec3 => gradVec w y j) x :=
    (contDiff_fderiv_apply_scalar w hw j).differentiable (by simp) x
  have hEq : (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j))
      =ᶠ[nhds x] fun y : Vec3 =>
        w y * fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j) + gradVec w y j * V y i := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_smul_comp_apply w V i j (hwdiff y) (hVdiff y hy)
  rw [hEq.fderiv_eq,
    fderiv_fun_add ((hwdiff x).fun_mul hAdiff) (hBdiff.fun_mul (hVdiff x hx)),
    fderiv_fun_mul (hwdiff x) hAdiff, fderiv_fun_mul hBdiff (hVdiff x hx)]
  simp only [add_apply, smul_apply, smul_eq_mul, gradVec]
  ring

/-! ### The pointwise commutator inequality -/

/-- The algebraic core: from the three-index Leibniz identity, the cutoff-weighted Hessian
energy is bounded by the Hessian energy of the product plus two cutoff error terms. -/
private lemma sum_sq_commutator_le (c : ℝ) (D2V D2WV : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (D1V : Fin 3 → Fin 3 → ℝ) (Vx gw : Fin 3 → ℝ) (hess : Fin 3 → Fin 3 → ℝ)
    (hleib : ∀ i j k : Fin 3,
      c * D2V i j k
        = D2WV i j k - gw k * D1V i j - gw j * D1V i k - hess j k * Vx i) :
    c ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2V i j k) ^ 2)
      ≤ 4 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2WV i j k) ^ 2)
        + 8 * ((∑ i : Fin 3, (gw i) ^ 2) * ∑ i : Fin 3, ∑ j : Fin 3, (D1V i j) ^ 2)
        + 4 * ((∑ i : Fin 3, ∑ j : Fin 3, (hess i j) ^ 2) * ∑ i : Fin 3, (Vx i) ^ 2) := by
  have hstep : ∀ i j k : Fin 3,
      (c * D2V i j k) ^ 2 ≤ 4 * (D2WV i j k) ^ 2
        + 4 * ((gw k) ^ 2 * (D1V i j) ^ 2) + 4 * ((gw j) ^ 2 * (D1V i k) ^ 2)
        + 4 * ((hess j k) ^ 2 * (Vx i) ^ 2) := by
    intro i j k
    rw [hleib i j k]
    nlinarith only [sq_nonneg (D2WV i j k + gw k * D1V i j),
      sq_nonneg (D2WV i j k + gw j * D1V i k),
      sq_nonneg (D2WV i j k + hess j k * Vx i),
      sq_nonneg (gw k * D1V i j - gw j * D1V i k),
      sq_nonneg (gw k * D1V i j - hess j k * Vx i),
      sq_nonneg (gw j * D1V i k - hess j k * Vx i)]
  calc c ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2V i j k) ^ 2)
      = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (c * D2V i j k) ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (4 * (D2WV i j k) ^ 2
          + 4 * ((gw k) ^ 2 * (D1V i j) ^ 2) + 4 * ((gw j) ^ 2 * (D1V i k) ^ 2)
          + 4 * ((hess j k) ^ 2 * (Vx i) ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => hstep i j k
    _ = 4 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2WV i j k) ^ 2)
          + 8 * ((∑ i : Fin 3, (gw i) ^ 2) * ∑ i : Fin 3, ∑ j : Fin 3, (D1V i j) ^ 2)
          + 4 * ((∑ i : Fin 3, ∑ j : Fin 3, (hess i j) ^ 2) * ∑ i : Fin 3, (Vx i) ^ 2) := by
        simp only [Fin.sum_univ_three]
        ring

/-- The pointwise form of the second-order cutoff commutator bound. -/
private lemma sq_cutoff_fderiv_fderiv_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hsupp : tsupport w ⊆ U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hjet : ∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
        + ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2)
    (x : Vec3) :
    w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x
          (basisVec k)) ^ 2
      ≤ 4 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 =>
              fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2)
        + 16 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 16 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) := by
  have hTnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 =>
        fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  have hGnn : (0 : ℝ) ≤ ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hHnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hNnn : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
  have hNG : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 := mul_nonneg hNnn hGnn
  have hNH : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 := mul_nonneg hNnn hHnn
  by_cases hxU : x ∈ U
  · have hmain := sum_sq_commutator_le (w x)
      (fun i j k => fderiv ℝ (fun y : Vec3 =>
        fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x (basisVec k))
      (fun i j k => fderiv ℝ (fun y : Vec3 =>
        fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k))
      (fun i j => fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j))
      (fun i => V x i) (fun i => gradVec w x i)
      (fun i j => fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j))
      fun i j k => fderiv_fderiv_smul_comp_apply w V U hU hw hV i j k hxU
    by_cases hxs : x ∈ tsupport (gradVec w)
    · have hjx := hjet x hxs
      have hPnn : (0 : ℝ) ≤ ∑ i : Fin 3, (V x i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hQnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hQle : (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2) ≤ N ^ 2 := by
        linarith only [hjx, hPnn]
      have hPle : (∑ i : Fin 3, (V x i) ^ 2) ≤ N ^ 2 := by linarith only [hjx, hQnn]
      have h1 := mul_le_mul_of_nonneg_left hQle hGnn
      have h2 := mul_le_mul_of_nonneg_left hPle hHnn
      nlinarith only [hmain, h1, h2, hNG, hNH]
    · have hg : gradVec w x = 0 := image_eq_zero_of_notMem_tsupport hxs
      have hgz : ∀ i : Fin 3, fderiv ℝ (fun y : Vec3 => gradVec w y i) x = 0 := by
        intro i
        have hEq : (fun y : Vec3 => gradVec w y i) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
          filter_upwards [eventuallyEq_zero_nhds_of_notMem_tsupport (gradVec w) hxs] with y hy
          rw [hy]
          rfl
        rw [hEq.fderiv_eq]
        simp
      have hG0 : (∑ i : Fin 3, (gradVec w x i) ^ 2) = 0 := by simp [hg]
      have hH0 : (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) = 0 := by simp [hgz]
      have hGQ : (∑ i : Fin 3, (gradVec w x i) ^ 2) * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 = 0 := by rw [hG0]; ring
      have hHP : (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)
          * ∑ i : Fin 3, (V x i) ^ 2 = 0 := by rw [hH0]; ring
      have hNG0 : N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 = 0 := by rw [hG0]; ring
      have hNH0 : N ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 = 0 := by rw [hH0]; ring
      linarith only [hmain, hGQ, hHP, hNG0, hNH0]
  · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hxU (hsupp hc)
    rw [hw0]
    linarith only [hTnn, hNG, hNH]

/-! ### Integrability of the majorant -/

/-- The Hessian energy of a smooth compactly supported field is integrable. -/
private lemma integrable_sum_sq_fderiv_fderiv (W : Vec3 → Vec3) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWs : HasCompactSupport W) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => W z i) y (basisVec j)) x
        (basisVec k)) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun k _ => by
        have h := integrable_mul_of_continuous_of_hasCompactSupport
          (continuous_fderiv_fderiv_comp W hW i j k)
          (continuous_fderiv_fderiv_comp W hW i j k)
          (hasCompactSupport_fderiv_fderiv_comp W hWs i j k)
        simpa [sq] using h

/-- `|∇χ|²` is integrable for a smooth compactly supported cutoff. -/
theorem integrable_sum_sq_gradVec_cutoff (w : Vec3 → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hws : HasCompactSupport w) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, (gradVec w x i) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ => by
    have h := integrable_mul_of_continuous_of_hasCompactSupport
      (continuous_fderiv_apply_scalar w hw i) (continuous_fderiv_apply_scalar w hw i)
      (hws.fderiv_apply (𝕜 := ℝ) (basisVec i))
    simpa [sq, gradVec] using h

/-- `|∇²χ|²` is integrable for a smooth compactly supported cutoff. -/
theorem integrable_sum_sq_fderiv_gradVec_cutoff (w : Vec3 → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hws : HasCompactSupport w) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => by
      have hGs : HasCompactSupport (fun y : Vec3 => gradVec w y i) :=
        hws.fderiv_apply (𝕜 := ℝ) (basisVec i)
      have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => gradVec w y i) :=
        contDiff_fderiv_apply_scalar w hw i
      have h := integrable_mul_of_continuous_of_hasCompactSupport
        (continuous_fderiv_apply_scalar (fun y : Vec3 => gradVec w y i) hGc j)
        (continuous_fderiv_apply_scalar (fun y : Vec3 => gradVec w y i) hGc j)
        (hGs.fderiv_apply (𝕜 := ℝ) (basisVec j))
      simpa [sq] using h

/-! ### The second-order cutoff commutator bound -/

/-- **The second-order cutoff commutator bound.** For a cutoff `χ` smooth and compactly supported
inside an open set `U`, a field `v` smooth on `U`, and `N` bounding the first-order jet of `v`
on the support of `∇χ`,

`∫ χ² |∇²v|² ≤ 4 ∫ |∇²(χ v)|² + 16 N² ∫ |∇χ|² + 16 N² ∫ |∇²χ|²`.

This is the second-order counterpart of the first-order commutator step that moves the cutoff
inside one derivative, and it is what `lem:aniso:closure` needs in order to convert the elliptic
bound on `∇²(χ v)` into a bound on `χ ∇²v`. -/
theorem integral_cutoff_sq_fderiv_fderiv_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3)
    (N : ℝ) (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hws : HasCompactSupport w)
    (hsupp : tsupport w ⊆ U) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hjet : ∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
        + ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2) :
    ∫ x : Vec3, w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x
          (basisVec k)) ^ 2
      ≤ 4 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 =>
              fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2)
        + 16 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 16 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) := by
  obtain ⟨hWcd, hWcs⟩ := contDiff_smul_of_contDiffOn w V U hU hw hws hsupp hV
  have hTint : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 =>
        fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2) :=
    integrable_sum_sq_fderiv_fderiv (fun y : Vec3 => w y • V y) hWcd hWcs
  have hGint : Integrable (fun x : Vec3 => ∑ i : Fin 3, (gradVec w x i) ^ 2) :=
    integrable_sum_sq_gradVec_cutoff w hw hws
  have hHint : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) :=
    integrable_sum_sq_fderiv_gradVec_cutoff w hw hws
  have hSum₁ : Integrable (fun x : Vec3 =>
      4 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 =>
            fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2)
        + 16 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)) :=
    (hTint.const_mul 4).add (hGint.const_mul (16 * N ^ 2))
  have hSum₂ : Integrable (fun x : Vec3 =>
      4 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 =>
            fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2)
        + 16 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 16 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)) :=
    hSum₁.add (hHint.const_mul (16 * N ^ 2))
  have hnn : (0 : Vec3 → ℝ) ≤ᵐ[volume] fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      ∑ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
        fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x (basisVec k)) ^ 2 :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hle : (fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 =>
          fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x (basisVec k)) ^ 2)
      ≤ᵐ[volume] fun x : Vec3 =>
        4 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 =>
              fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2)
          + 16 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
          + 16 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) :=
    Filter.Eventually.of_forall fun x =>
      sq_cutoff_fderiv_fderiv_le w V U N hU hw hsupp hV hjet x
  have hstep := integral_mono_of_nonneg hnn hSum₂ hle
  rwa [integral_add hSum₁ (hHint.const_mul (16 * N ^ 2)),
    integral_add (hTint.const_mul 4) (hGint.const_mul (16 * N ^ 2)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hstep

/-! ### The first-order cutoff commutator bound -/

/-- The algebraic core of the first-order commutator step. -/
private lemma sum_sq_commutator_first_le (c : ℝ) (D1V D1WV : Fin 3 → Fin 3 → ℝ)
    (Vx gw : Fin 3 → ℝ)
    (hleib : ∀ i j : Fin 3, c * D1V i j = D1WV i j - gw j * Vx i) :
    c ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3, (D1V i j) ^ 2)
      ≤ 2 * (∑ i : Fin 3, ∑ j : Fin 3, (D1WV i j) ^ 2)
        + 2 * ((∑ i : Fin 3, (gw i) ^ 2) * ∑ i : Fin 3, (Vx i) ^ 2) := by
  have hstep : ∀ i j : Fin 3, (c * D1V i j) ^ 2
      ≤ 2 * (D1WV i j) ^ 2 + 2 * ((gw j) ^ 2 * (Vx i) ^ 2) := by
    intro i j
    rw [hleib i j]
    nlinarith only [sq_nonneg (D1WV i j + gw j * Vx i)]
  calc c ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3, (D1V i j) ^ 2)
      = ∑ i : Fin 3, ∑ j : Fin 3, (c * D1V i j) ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          (2 * (D1WV i j) ^ 2 + 2 * ((gw j) ^ 2 * (Vx i) ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
    _ = 2 * (∑ i : Fin 3, ∑ j : Fin 3, (D1WV i j) ^ 2)
          + 2 * ((∑ i : Fin 3, (gw i) ^ 2) * ∑ i : Fin 3, (Vx i) ^ 2) := by
        simp only [Fin.sum_univ_three]
        ring

/-- The pointwise form of the first-order cutoff commutator bound. -/
private lemma sq_cutoff_fderiv_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hsupp : tsupport w ⊆ U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hbd : ∀ x ∈ tsupport (gradVec w), ∑ i : Fin 3, (V x i) ^ 2 ≤ N ^ 2)
    (x : Vec3) :
    w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2
      ≤ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)) ^ 2)
        + 2 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2) := by
  have hWnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hGnn : (0 : ℝ) ≤ ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hNG : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    mul_nonneg (sq_nonneg N) hGnn
  by_cases hxU : x ∈ U
  · have hwdiff : ∀ y : Vec3, DifferentiableAt ℝ w y := fun y => hw.differentiable (by simp) y
    have hVd : ∀ a : Fin 3, DifferentiableAt ℝ (fun z : Vec3 => V z a) x := fun a =>
      ((((contDiffOn_pi.mp hV) a).differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds hxU))
    have hmain := sum_sq_commutator_first_le (w x)
      (fun i j => fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j))
      (fun i j => fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j))
      (fun i => V x i) (fun i => gradVec w x i) (fun i j => by
        rw [fderiv_smul_comp_apply w V i j (hwdiff x) (hVd i)]
        ring)
    by_cases hxs : x ∈ tsupport (gradVec w)
    · have hPle := hbd x hxs
      have h1 := mul_le_mul_of_nonneg_left hPle hGnn
      nlinarith only [hmain, h1, hNG]
    · have hg : gradVec w x = 0 := image_eq_zero_of_notMem_tsupport hxs
      have hG0 : (∑ i : Fin 3, (gradVec w x i) ^ 2) = 0 := by simp [hg]
      have hGP : (∑ i : Fin 3, (gradVec w x i) ^ 2) * ∑ i : Fin 3, (V x i) ^ 2 = 0 := by
        rw [hG0]; ring
      have hNG0 : N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 = 0 := by rw [hG0]; ring
      linarith only [hmain, hGP, hNG0]
  · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hxU (hsupp hc)
    rw [hw0]
    linarith only [hWnn, hNG]

/-- The gradient energy of a smooth compactly supported field is integrable. -/
private lemma integrable_sum_sq_fderiv (W : Vec3 → Vec3) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWs : HasCompactSupport W) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => W y i) x (basisVec j)) ^ 2) :=
  integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => integrable_sq_fderiv_comp W hWs hW i j

/-- **The first-order cutoff commutator bound.** For a cutoff `χ` smooth and compactly supported
inside an open set `U`, a field `v` smooth on `U`, and `N` bounding `|v|` on the support of `∇χ`,

`∫ χ² |∇v|² ≤ 2 ∫ |∇(χ v)|² + 2 N² ∫ |∇χ|²`. -/
theorem integral_cutoff_sq_fderiv_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hws : HasCompactSupport w)
    (hsupp : tsupport w ⊆ U) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hbd : ∀ x ∈ tsupport (gradVec w), ∑ i : Fin 3, (V x i) ^ 2 ≤ N ^ 2) :
    ∫ x : Vec3, w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2
      ≤ 2 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)) ^ 2)
        + 2 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2) := by
  obtain ⟨hWcd, hWcs⟩ := contDiff_smul_of_contDiffOn w V U hU hw hws hsupp hV
  have hWint : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)) ^ 2) :=
    integrable_sum_sq_fderiv (fun y : Vec3 => w y • V y) hWcd hWcs
  have hGint : Integrable (fun x : Vec3 => ∑ i : Fin 3, (gradVec w x i) ^ 2) :=
    integrable_sum_sq_gradVec_cutoff w hw hws
  have hmaj : Integrable (fun x : Vec3 =>
      2 * (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)) ^ 2)
        + 2 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)) :=
    (hWint.const_mul 2).add (hGint.const_mul (2 * N ^ 2))
  have hnn : (0 : Vec3 → ℝ) ≤ᵐ[volume] fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hstep := integral_mono_of_nonneg hnn hmaj
    (Filter.Eventually.of_forall fun x => sq_cutoff_fderiv_le w V U N hU hw hsupp hV hbd x)
  rwa [integral_add (hWint.const_mul 2) (hGint.const_mul (2 * N ^ 2)),
    integral_const_mul, integral_const_mul] at hstep

end CIV
