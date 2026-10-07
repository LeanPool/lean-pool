/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.CurlCutoff

/-!
# The gradient bound of `eq:aniso:closure:elliptic`

This file proves the first of the two elliptic bounds `eq:aniso:closure:elliptic` of
*Regularity of asymptotically axisymmetric solutions to the 3D Navier–Stokes equations with
analytic forcing*, arXiv:2609.20803, in the form in which the closure argument
`lem:aniso:closure` uses it.

Let `U` be an open set, `v : Vec3 → Vec3` smooth and divergence free on `U`, and `χ` a smooth
cutoff whose support is a compact subset of `U`. The product `χ • v` is then smooth and
compactly supported on all of `ℝ³`, so the elliptic identity
`integral_sq_fderiv_eq_curl_add_div` applies to it:
`∫ |∇(χ v)|² = ∫ |curl (χ v)|² + ∫ (div (χ v))²`.
Expanding `curl (χ v) = χ curl v + ∇χ × v` and `div (χ v) = ∇χ · v` (the term `χ div v`
vanishes on `U`, and everything vanishes off `tsupport χ`) and using
`|∇χ × v|² ≤ |∇χ|² |v|²` and `(∇χ · v)² ≤ |∇χ|² |v|²` gives

`∫ |∇(χ v)|² ≤ 2 ∫ χ² |curl v|² + 3 Mu² ∫ |∇χ|²`,

where `Mu` bounds `|v|` wherever `∇χ ≠ 0`. The first term on the right is the quantity
`Y t = ‖χ ω(·, t)‖²` of `lem:aniso:closure` with `ω = curl u`; `integral_cutoff_sq_curl_eq_curlComp`
records that shape in terms of the ambient curl `curlComp` of a space–time field.

The second elliptic bound of `eq:aniso:closure:elliptic`, the `∇²b` estimate, is not proved here.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### Vanishing off the support of the cutoff -/

/-- A function vanishes on a whole neighbourhood of any point outside its support. -/
private lemma eventuallyEq_zero_nhds_of_notMem {M : Type*} [Zero M] (f : Vec3 → M) {x : Vec3}
    (hx : x ∉ tsupport f) : f =ᶠ[nhds x] fun _ : Vec3 => (0 : M) := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

/-- The partial derivatives of a vector field vanish where the field vanishes identically
near the point. -/
private lemma fderiv_comp_eq_zero_of_eventuallyEq_zero {w : Vec3 → Vec3} {x : Vec3}
    (h : w =ᶠ[nhds x] fun _ : Vec3 => (0 : Vec3)) (i : Fin 3) :
    fderiv ℝ (fun y : Vec3 => w y i) x = 0 := by
  have heq : (fun y : Vec3 => w y i) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [h] with y hy
    simp [hy]
  simp [heq.fderiv_eq]

/-- The curl of a vector field vanishes where the field vanishes identically near the point. -/
private lemma curlVec_eq_zero_of_eventuallyEq_zero {w : Vec3 → Vec3} {x : Vec3}
    (h : w =ᶠ[nhds x] fun _ : Vec3 => (0 : Vec3)) : curlVec w x = 0 := by
  have hz : ∀ i : Fin 3, fderiv ℝ (fun y : Vec3 => w y i) x = 0 := fun i =>
    fderiv_comp_eq_zero_of_eventuallyEq_zero h i
  ext i
  fin_cases i <;> simp [curlVec, hz]

/-- The gradient of a scalar vanishes where the scalar vanishes identically near the point. -/
private lemma gradVec_eq_zero_of_eventuallyEq_zero {χ : Vec3 → ℝ} {x : Vec3}
    (h : χ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ)) : gradVec χ x = 0 := by
  ext i
  simp [gradVec, h.fderiv_eq]

/-! ### Smoothness and support of a cutoff times a locally smooth field -/

/-- A smooth compactly supported cutoff `χ` whose support sits inside an open set `U`
turns a field `v` that is smooth only on `U` into a globally smooth, compactly supported
field `χ • v`. -/
theorem contDiff_smul_of_contDiffOn (χ : Vec3 → ℝ) (v : Vec3 → Vec3) (U : Set Vec3) (hU : IsOpen U)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ) (hsupp : tsupport χ ⊆ U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • v x) ∧ HasCompactSupport (fun x => χ x • v x) := by
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hχ.contDiffAt).smul (hv.contDiffAt (hU.mem_nhds (hsupp hx)))
    · have heq : (fun y : Vec3 => χ y • v y) =ᶠ[nhds x] (fun _ : Vec3 => (0 : Vec3)) := by
        filter_upwards [eventuallyEq_zero_nhds_of_notMem χ hx] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · refine HasCompactSupport.intro hχs (fun x hx => ?_)
    simp [image_eq_zero_of_notMem_tsupport hx]

/-! ### Continuity and integrability of the cutoff quantities -/

/-- A function continuous on an open set `U` and vanishing outside a closed subset of `U`
is continuous everywhere. -/
private lemma continuous_of_continuousOn_of_zero_outside {F : Vec3 → ℝ} {U K : Set Vec3}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hF : ContinuousOn F U)
    (hzero : ∀ x : Vec3, x ∉ K → F x = 0) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ K
  · exact hF.continuousAt (hU.mem_nhds (hKU hx))
  · have heq : F =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      exact hzero y hy
    exact heq.continuousAt

/-- The squared length of the curl, written out in the three Cartesian components. -/
private lemma sum_sq_curlVec_eq (w : Vec3 → Vec3) (x : Vec3) :
    ∑ i : Fin 3, (curlVec w x i) ^ 2 =
      (fderiv ℝ (fun y : Vec3 => w y 2) x (basisVec 1)
          - fderiv ℝ (fun y : Vec3 => w y 1) x (basisVec 2)) ^ 2
      + (fderiv ℝ (fun y : Vec3 => w y 0) x (basisVec 2)
          - fderiv ℝ (fun y : Vec3 => w y 2) x (basisVec 0)) ^ 2
      + (fderiv ℝ (fun y : Vec3 => w y 1) x (basisVec 0)
          - fderiv ℝ (fun y : Vec3 => w y 0) x (basisVec 1)) ^ 2 := by
  simp only [curlVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- A directional derivative of a field that is smooth on an open set is continuous there. -/
private lemma continuousOn_fderiv_apply_of_contDiffOn {v : Vec3 → Vec3} {U : Set Vec3}
    (hU : IsOpen U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (i j : Fin 3) :
    ContinuousOn (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => v y i) x (basisVec j)) U := by
  have hvi : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => v y i) U := (contDiffOn_pi.mp hv) i
  have hfd : ContinuousOn (fderiv ℝ (fun y : Vec3 => v y i)) U :=
    hvi.continuousOn_fderiv_of_isOpen hU (by simp)
  exact hfd.clm_apply continuousOn_const

/-- The squared length of the curl is continuous where the field is smooth. -/
private lemma continuousOn_sum_sq_curlVec {v : Vec3 → Vec3} {U : Set Vec3}
    (hU : IsOpen U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, (curlVec v x i) ^ 2) U := by
  have h : ∀ a b : Fin 3,
      ContinuousOn (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => v y a) x (basisVec b)) U :=
    fun a b => continuousOn_fderiv_apply_of_contDiffOn hU hv a b
  simp only [sum_sq_curlVec_eq]
  exact ((((h 2 1).sub (h 1 2)).pow 2).add (((h 0 2).sub (h 2 0)).pow 2)).add
    (((h 1 0).sub (h 0 1)).pow 2)

/-- The square of a continuous compactly supported function is integrable. -/
private lemma integrable_sq_of_continuous_hasCompactSupport {f : Vec3 → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) : Integrable (fun x : Vec3 => f x ^ 2) := by
  simpa [sq] using integrable_mul_of_continuous_of_hasCompactSupport hf hf hs

/-- `χ² |curl v|²` is integrable when `χ` is a cutoff supported inside the smoothness set. -/
private lemma integrable_cutoff_sq_sum_sq_curlVec {χ : Vec3 → ℝ} {v : Vec3 → Vec3} {U : Set Vec3}
    (hU : IsOpen U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2) := by
  have hzero : ∀ x : Vec3, x ∉ tsupport χ →
      χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2 = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hcontOn : ContinuousOn (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2) U :=
    (hχ.continuous.continuousOn.pow 2).mul (continuousOn_sum_sq_curlVec hU hv)
  have hcont : Continuous (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2) :=
    continuous_of_continuousOn_of_zero_outside hU (isClosed_tsupport χ) hsupp hcontOn hzero
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hχs hzero)

/-- `|∇χ|²` is integrable for a smooth compactly supported cutoff. -/
private lemma integrable_sum_sq_gradVec {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, (gradVec χ x i) ^ 2) := by
  have hcomp : ∀ i : Fin 3, Continuous (fun x : Vec3 => gradVec χ x i) := by
    intro i
    have hpair : Continuous (fun p : Vec3 × Vec3 => (fderiv ℝ χ p.1) p.2) :=
      hχ.continuous_fderiv_apply (by simp)
    exact hpair.comp (continuous_id.prodMk continuous_const)
  have hcont : Continuous (fun x : Vec3 => ∑ i : Fin 3, (gradVec χ x i) ^ 2) :=
    continuous_finsetSum Finset.univ (fun i _ => (hcomp i).pow 2)
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hχs (fun x hx => ?_))
  simp [gradVec_eq_zero_of_eventuallyEq_zero (eventuallyEq_zero_nhds_of_notMem χ hx)]

/-- `|curl w|²` is integrable for a smooth compactly supported field. -/
private lemma integrable_sum_sq_curlVec {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hws : HasCompactSupport w) :
    Integrable (fun x : Vec3 => ∑ i : Fin 3, (curlVec w x i) ^ 2) := by
  have h : ∀ a b : Fin 3,
      Continuous (fun x : Vec3 => fderiv ℝ (fun y : Vec3 => w y a) x (basisVec b)) :=
    fun a b => continuous_fderiv_comp w hw a b
  have hcont : Continuous (fun x : Vec3 => ∑ i : Fin 3, (curlVec w x i) ^ 2) := by
    simp only [sum_sq_curlVec_eq]
    exact ((((h 2 1).sub (h 1 2)).pow 2).add (((h 0 2).sub (h 2 0)).pow 2)).add
      (((h 1 0).sub (h 0 1)).pow 2)
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hws (fun x hx => ?_))
  simp [curlVec_eq_zero_of_eventuallyEq_zero (eventuallyEq_zero_nhds_of_notMem w hx)]

/-- `(div w)²` is integrable for a smooth compactly supported field. -/
private lemma integrable_sq_sum_fderiv_diag {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hws : HasCompactSupport w) :
    Integrable (fun x : Vec3 =>
      (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => w y j) x (basisVec j)) ^ 2) := by
  have hcont : Continuous
      (fun x : Vec3 => ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => w y j) x (basisVec j)) :=
    continuous_finsetSum Finset.univ (fun j _ => continuous_fderiv_comp w hw j j)
  have hs : HasCompactSupport
      (fun x : Vec3 => ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => w y j) x (basisVec j)) := by
    refine HasCompactSupport.intro hws (fun x hx => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [fderiv_comp_eq_zero_of_eventuallyEq_zero (eventuallyEq_zero_nhds_of_notMem w hx) j]
    simp
  exact integrable_sq_of_continuous_hasCompactSupport hcont hs

/-! ### The Cauchy–Schwarz inequality in three components -/

/-- `(a · b)² ≤ |a|² |b|²` on `Vec3`, by the Lagrange identity. -/
private lemma sq_dot3_le (a b : Vec3) :
    (∑ i : Fin 3, a i * b i) ^ 2 ≤ (∑ i : Fin 3, a i ^ 2) * ∑ i : Fin 3, b i ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
    sq_nonneg (a 1 * b 2 - a 2 * b 1)]

/-! ### The gradient bound -/

/-- The first inequality of `eq:aniso:closure:elliptic`: for a field `v` that is smooth and
divergence free on an open set `U` and a smooth cutoff `χ` supported in `U`, with `|v| ≤ Mu`
wherever `∇χ ≠ 0`,

`∫ |∇(χ v)|² ≤ 2 ∫ χ² |curl v|² + 3 Mu² ∫ |∇χ|²`.

In `lem:aniso:closure` the field `v` is the time slice of the velocity, so that
`∫ χ² |curl v|²` is the enstrophy `Y t`, and the last term is the constant `C`. -/
theorem integral_sq_fderiv_smul_le (χ : Vec3 → ℝ) (v : Vec3 → Vec3) (U : Set Vec3) (Mu : ℝ)
    (hU : IsOpen U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hdiv : ∀ x ∈ U, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => v y j) x (basisVec j) = 0)
    (hbound : ∀ x : Vec3, gradVec χ x ≠ 0 → ∑ i : Fin 3, (v x i) ^ 2 ≤ Mu ^ 2) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => (χ y • v y) i) x (basisVec j)) ^ 2
      ≤ 2 * (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2)
        + 3 * Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by
  obtain ⟨hw, hws⟩ := contDiff_smul_of_contDiffOn χ v U hU hχ hχs hsupp hv
  -- The differentiability of `v` at the points that matter.
  have hdiffv : ∀ x : Vec3, x ∈ U → ∀ i : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => v y i) x := by
    intro x hx i
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) v x := hv.contDiffAt (hU.mem_nhds hx)
    exact ((contDiffAt_pi.mp h1) i).differentiableAt (by simp)
  have hdiffχ : ∀ x : Vec3, DifferentiableAt ℝ χ x := fun x => hχ.differentiable (by simp) x
  -- The pointwise curl and divergence of `χ v`.
  have hcurlpt : ∀ x : Vec3, curlVec (fun y : Vec3 => χ y • v y) x
      = χ x • curlVec v x + cross3 (gradVec χ x) (v x) := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact curlVec_smul (hdiffχ x) (hdiffv x (hsupp hx))
    · have hχ0 : χ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := eventuallyEq_zero_nhds_of_notMem χ hx
      have hcv : (fun y : Vec3 => χ y • v y) =ᶠ[nhds x] fun _ : Vec3 => (0 : Vec3) := by
        filter_upwards [hχ0] with y hy
        simp [hy]
      rw [curlVec_eq_zero_of_eventuallyEq_zero hcv,
        gradVec_eq_zero_of_eventuallyEq_zero hχ0, image_eq_zero_of_notMem_tsupport hx]
      ext i
      fin_cases i <;> simp [cross3]
  have hdivpt : ∀ x : Vec3,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j)
        = ∑ j : Fin 3, gradVec χ x j * v x j := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · rw [div_smul (hdiffχ x) (hdiffv x (hsupp hx)), hdiv x (hsupp hx)]
      ring
    · have hχ0 : χ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := eventuallyEq_zero_nhds_of_notMem χ hx
      have hcv : (fun y : Vec3 => χ y • v y) =ᶠ[nhds x] fun _ : Vec3 => (0 : Vec3) := by
        filter_upwards [hχ0] with y hy
        simp [hy]
      have hg : gradVec χ x = 0 := gradVec_eq_zero_of_eventuallyEq_zero hχ0
      have hl : ∀ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x = 0 := fun j =>
        fderiv_comp_eq_zero_of_eventuallyEq_zero hcv j
      have hL : ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j) = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [hl j]
        simp
      have hR : ∑ j : Fin 3, gradVec χ x j * v x j = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [hg]
        simp
      rw [hL, hR]
  -- The pointwise bound coming from `|v| ≤ Mu` on the support of `∇χ`.
  have hbnd : ∀ x : Vec3, (∑ i : Fin 3, (gradVec χ x i) ^ 2) * (∑ i : Fin 3, (v x i) ^ 2)
      ≤ Mu ^ 2 * ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by
    intro x
    by_cases hx : gradVec χ x = 0
    · simp [hx]
    · have h1 := hbound x hx
      have h2 : (0 : ℝ) ≤ ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by positivity
      calc (∑ i : Fin 3, (gradVec χ x i) ^ 2) * (∑ i : Fin 3, (v x i) ^ 2)
          ≤ (∑ i : Fin 3, (gradVec χ x i) ^ 2) * Mu ^ 2 := by
            exact mul_le_mul_of_nonneg_left h1 h2
        _ = Mu ^ 2 * ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by ring
  -- The two pointwise inequalities.
  have hcurlbd : ∀ x : Vec3, ∑ i : Fin 3, (curlVec (fun y : Vec3 => χ y • v y) x i) ^ 2
      ≤ 2 * (χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2)
        + 2 * (Mu ^ 2 * ∑ i : Fin 3, (gradVec χ x i) ^ 2) := by
    intro x
    have h1 := sum_sq_add_le_two_mul (χ x • curlVec v x) (cross3 (gradVec χ x) (v x))
    have h2 := sum_sq_smul (χ x) (curlVec v x)
    have h3 := sum_sq_cross3_le (gradVec χ x) (v x)
    have h4 := hbnd x
    rw [hcurlpt x]
    simp only [Pi.add_apply]
    linarith only [h1, h2, h3, h4]
  have hdivbd : ∀ x : Vec3,
      (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j)) ^ 2
        ≤ Mu ^ 2 * ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by
    intro x
    rw [hdivpt x]
    have h3 := sq_dot3_le (gradVec χ x) (v x)
    have h4 := hbnd x
    linarith only [h3, h4]
  -- Integrability of every term.
  have hIcurlw : Integrable (fun x : Vec3 =>
      ∑ i : Fin 3, (curlVec (fun y : Vec3 => χ y • v y) x i) ^ 2) :=
    integrable_sum_sq_curlVec hw hws
  have hIdivw : Integrable (fun x : Vec3 =>
      (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j)) ^ 2) :=
    integrable_sq_sum_fderiv_diag hw hws
  have hIcurlv : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2) :=
    integrable_cutoff_sq_sum_sq_curlVec hU hχ hχs hsupp hv
  have hIgrad : Integrable (fun x : Vec3 => ∑ i : Fin 3, (gradVec χ x i) ^ 2) :=
    integrable_sum_sq_gradVec hχ hχs
  -- The elliptic identity for the compactly supported field `χ v`.
  have key : ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => (χ y • v y) i) x (basisVec j)) ^ 2
      = (∫ x : Vec3, ∑ i : Fin 3, (curlVec (fun y : Vec3 => χ y • v y) x i) ^ 2)
        + ∫ x : Vec3,
            (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j)) ^ 2 :=
    integral_sq_fderiv_eq_curl_add_div (fun x : Vec3 => χ x • v x) hw hws
  -- Integrate the two pointwise inequalities.
  have b1 : (∫ x : Vec3, ∑ i : Fin 3, (curlVec (fun y : Vec3 => χ y • v y) x i) ^ 2)
      ≤ 2 * (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2)
        + 2 * (Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2) := by
    have hI2 : Integrable (fun x : Vec3 => 2 * (χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2)
        + 2 * (Mu ^ 2 * ∑ i : Fin 3, (gradVec χ x i) ^ 2)) :=
      (hIcurlv.const_mul 2).add ((hIgrad.const_mul (Mu ^ 2)).const_mul 2)
    have hmono := integral_mono hIcurlw hI2 hcurlbd
    rwa [integral_add (hIcurlv.const_mul 2) ((hIgrad.const_mul (Mu ^ 2)).const_mul 2),
      integral_const_mul, integral_const_mul, integral_const_mul] at hmono
  have b2 : (∫ x : Vec3,
        (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j)) ^ 2)
      ≤ Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by
    have hmono := integral_mono hIdivw (hIgrad.const_mul (Mu ^ 2)) hdivbd
    rwa [integral_const_mul] at hmono
  calc ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => (χ y • v y) i) x (basisVec j)) ^ 2
      = (∫ x : Vec3, ∑ i : Fin 3, (curlVec (fun y : Vec3 => χ y • v y) x i) ^ 2)
        + ∫ x : Vec3,
            (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => (χ y • v y) j) x (basisVec j)) ^ 2 := key
    _ ≤ (2 * (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2)
          + 2 * (Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2))
        + Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 := add_le_add b1 b2
    _ = 2 * (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2)
        + 3 * Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 := by ring

/-! ### The enstrophy shape `Y t = ‖χ ω(·, t)‖²` -/

/-- The quantity `∫ χ² |curl v|²` of `integral_sq_fderiv_smul_le`, written with the ambient
curl `curlComp` of the space–time field whose time slice is `v`. This is the enstrophy
`Y t = ‖χ ω(·, t)‖²` of `lem:aniso:closure`. -/
theorem integral_cutoff_sq_curl_eq_curlComp (χ : Vec3 → ℝ) (v : Vec3 → Vec3) (t : ℝ) :
    ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2
      = ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3,
          (curlComp (fun z : ParabolicPoint => v z.1) i (x, t)) ^ 2 := by
  have hpt : ∀ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec v x i) ^ 2
      = χ x ^ 2 * ∑ i : Fin 3,
          (curlComp (fun z : ParabolicPoint => v z.1) i (x, t)) ^ 2 := by
    intro x
    rw [curlVec_apply_eq_curlComp v x t]
    simp [Fin.sum_univ_three]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end CIV
