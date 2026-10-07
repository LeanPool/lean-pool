/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnstrophyBalanceTerms
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Reduction.LaplacianMultiPartialBridge

/-!
# `eq:aniso:closure:elliptic` in the tested quantities `Y` and `M`

This file states the two elliptic bounds of `lem:aniso:closure` in the form the mixed-term
estimate `eq:aniso:closure:mixed:bound` consumes them: with the cutoff `χ` of the closure
argument and a classical solution `u` on the unit cylinder,

`∫ χ² |∇u(·, t)|² ≤ C (Y t + 1)`  and  `∫ χ² |∇²u(·, t)|² ≤ C (M t + 1)`,

where `Y = cutoffEnstrophy χ u` and `M = cutoffEnstrophyDissipation χ u`. Both are stated in the
`spatialPartial`/`spatialSecondPartial` operators of the classical formulation and share the
hypothesis block of `energy_inequality_of_mixed_term_bound`, so the two families compose.

Following the convention of this formalization, the bounds are carried by the full velocity `u`
rather than by the meridional velocity `b = u_r e_r + u_z e_z` of the printed argument: the
pointwise dominations `|∂_r u_z| ≤ |∇u|` and `|∂_z∂_r u_z| ≤ |∇²u|` replace `|∂_r u_z| ≤ |∇b|`
and `|∂_z∂_r u_z| ≤ |∇²b|`, and the two inequalities come out with the same `Y` and `M`.

## The three inputs taken as hypotheses

The two bounds of this file take three inequalities that `lem:aniso:closure` uses as explicit,
named hypotheses. Each is stated exactly as the lemma that proves it, and
`CIV.Closure.EllipticBoundsAnnulusBound` discharges all three by one application each:
`hCommutatorFirst` by `integral_cutoff_sq_fderiv_le`, `hCommutatorSecond` by
`integral_cutoff_sq_fderiv_fderiv_le`, and `hEllipticSecond` by
`integral_sq_fderiv_fderiv_smul_le`. The closure lemma therefore carries none of them.

* `hCommutatorFirst` — the first-order cutoff commutator `‖χ∇v‖² ≤ 2‖∇(χv)‖² + 2 N²‖∇χ‖²`,
  which moves the cutoff across one derivative at the cost of a term supported where `∇χ ≠ 0`.
* `hCommutatorSecond` — its second-order counterpart
  `‖χ∇²v‖² ≤ 4‖∇²(χv)‖² + 16 N²(‖∇χ‖² + ‖∇²χ‖²)`.
* `hEllipticSecond` — the second elliptic bound
  `‖∇²(χv)‖² ≤ 4‖χ∇curl v‖² + 24 N²(‖∇χ‖² + ‖∇²χ‖²)`, the second-order analogue of the
  `integral_sq_fderiv_smul_le`, obtained from the second-order form of the div–curl identity
  `eq:aniso:closure:elliptic` applied to `χ v`.

All three carry the regularity block of `integral_sq_fderiv_smul_le` — `U` open, `χ` smooth with
compact support inside `U`, `v` smooth on `U`. That block is not decoration: without it the three
integrals on the right need not be finite, a Bochner integral of a non-integrable function is
zero, and each inequality is then false. With it all three are true, and all three are applied
below at data for which every one of those regularity hypotheses is supplied by the hypothesis
block of the theorems themselves.

The first elliptic bound is the `integral_sq_fderiv_smul_le`, and the two identifications
of the cutoff-weighted curl energies with `Y` and `M` are proved here.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-! ### Where the derivatives of the cutoff live -/

/-- The gradient of a cutoff is supported in the support of the cutoff. -/
theorem tsupport_gradVec_subset (χ : Vec3 → ℝ) : tsupport (gradVec χ) ⊆ tsupport χ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport χ)
  by_contra hxn
  refine hx ?_
  have hEq : χ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxn] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hzero : fderiv ℝ χ x = 0 := by rw [hEq.fderiv_eq]; simp
  ext i
  simp [gradVec, hzero]

/-- A closed set outside which the cutoff has vanishing derivative contains the support of the
gradient of the cutoff. This is the shape in which the closure argument records where the cutoff
error terms live. -/
theorem tsupport_gradVec_subset_of_fderiv_eq_zero {χ : Vec3 → ℝ} {A : Set Vec3}
    (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0) :
    tsupport (gradVec χ) ⊆ A := by
  refine closure_minimal (fun x hx => ?_) hAcl
  by_contra hxn
  exact hx (by ext i; simp [gradVec, hχA x hxn])

/-! ### The tested quantities as curl energies -/

/-- `Y t = ‖χ ω(·, t)‖²` is the cutoff-weighted `L²` norm of the curl of the time slice of `u`. -/
theorem cutoffEnstrophy_eq_integral_sq_curlVec (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (t : ℝ) :
    cutoffEnstrophy χ u t
      = ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine congrArg (fun s : ℝ => χ x ^ 2 * s) (Finset.sum_congr rfl fun i _ => ?_)
  have hpt : vorticityField u (x, t) i = curlVec (fun y : Vec3 => u (y, t)) x i := by
    fin_cases i <;> rfl
  rw [hpt]

/-- `M t = ‖χ ∇ω(·, t)‖²` is the cutoff-weighted `L²` norm of the gradient of the curl of the
time slice of `u`. -/
theorem cutoffEnstrophyDissipation_eq_integral_sq_fderiv_curlVec (χ : Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (t : ℝ) :
    cutoffEnstrophyDissipation χ u t
      = ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => curlVec (fun y' : Vec3 => u (y', t)) y i) x
            (basisVec k)) ^ 2 := by
  have hfun : ∀ i : Fin 3, (fun y : Vec3 => vorticityField u (y, t) i)
      = fun y : Vec3 => curlVec (fun y' : Vec3 => u (y', t)) y i := by
    intro i
    funext y
    fin_cases i <;> rfl
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine congrArg (fun s : ℝ => χ x ^ 2 * s) (Finset.sum_congr rfl fun i _ => ?_)
  exact Finset.sum_congr rfl fun k _ => by rw [show
    spatialPartial (fun w => vorticityField u w i) k (x, t)
      = fderiv ℝ (fun y : Vec3 => vorticityField u (y, t) i) x (basisVec k) from rfl, hfun i]

/-! ### Reading the classical operators off the time slice -/

/-- The first spatial partials of `u` on the slice `t` are the partials of the slice. -/
private lemma integral_cutoff_sq_spatialPartial_eq (χ : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (t : ℝ) :
    (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (spatialPartial (fun w => u w i) j (x, t)) ^ 2)
      = ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j)) ^ 2 := rfl

/-- The second spatial partials of `u` on the slice `t` are the second partials of the slice. -/
private lemma integral_cutoff_sq_spatialSecondPartial_eq (χ : Vec3 → ℝ)
    (u : ParabolicPoint → Vec3) (t : ℝ) :
    (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2)
      = ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => u (z, t) i) y (basisVec j)) x
            (basisVec k)) ^ 2 := rfl

/-! ### Elementary bounds -/

/-- A vector of three reals bounded componentwise has squared length at most `3 Mu²`. -/
private lemma sum_sq_le_of_abs_le (Mu : ℝ) (w : Fin 3 → ℝ) (h : ∀ i : Fin 3, |w i| ≤ Mu) :
    ∑ i : Fin 3, (w i) ^ 2 ≤ 3 * Mu ^ 2 := by
  have hsq : ∀ i : Fin 3, (w i) ^ 2 ≤ Mu ^ 2 := fun i =>
    sq_le_sq' (abs_le.mp (h i)).1 (abs_le.mp (h i)).2
  rw [Fin.sum_univ_three]
  linarith only [hsq 0, hsq 1, hsq 2]

/-- The arithmetic of the first elliptic bound: the commutator step and the gradient bound
compose into `C (Y + 1)`. -/
private lemma closure_elliptic_arith₁ (L P Y K N : ℝ) (hY : 0 ≤ Y) (hK : 0 ≤ K)
    (h1 : L ≤ 2 * P + 2 * N ^ 2 * K) (h2 : P ≤ 2 * Y + 3 * N ^ 2 * K) :
    L ≤ (4 + 8 * N ^ 2 * K) * (Y + 1) := by
  have hprod : 0 ≤ N ^ 2 * K * Y := mul_nonneg (mul_nonneg (sq_nonneg N) hK) hY
  linarith only [h1, h2, hprod]

/-- The arithmetic of the second elliptic bound: the second-order commutator step and the
Hessian bound compose into `C (M + 1)`. -/
private lemma closure_elliptic_arith₂ (L S Md K₁ K₂ N : ℝ) (hM : 0 ≤ Md)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h1 : L ≤ 4 * S + 16 * N ^ 2 * K₁ + 16 * N ^ 2 * K₂)
    (h2 : S ≤ 4 * Md + 24 * N ^ 2 * K₁ + 24 * N ^ 2 * K₂) :
    L ≤ (16 + 112 * N ^ 2 * (K₁ + K₂)) * (Md + 1) := by
  have hp₁ : 0 ≤ N ^ 2 * K₁ * Md := mul_nonneg (mul_nonneg (sq_nonneg N) hK₁) hM
  have hp₂ : 0 ≤ N ^ 2 * K₂ * Md := mul_nonneg (mul_nonneg (sq_nonneg N) hK₂) hM
  linarith only [h1, h2, hp₁, hp₂]

/-! ### The two bounds of `eq:aniso:closure:elliptic` -/

/-- **The gradient half of `eq:aniso:closure:elliptic`.** For a classical solution on the unit
cylinder and a cutoff supported in the unit ball, the cutoff-weighted gradient energy of the
velocity is bounded by `C (Y + 1)`, with `Y = cutoffEnstrophy χ u` the tested enstrophy. The
hypothesis block is that of `energy_inequality_of_mixed_term_bound`; `hCommutatorFirst` is the
one addition. -/
theorem integral_cutoff_sq_spatialPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mu : ℝ}
    (hubd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, |u (x, t) i| ≤ Mu)
    (hCommutatorFirst : ∀ (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ),
      IsOpen U → ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w → tsupport w ⊆ U →
      ContDiffOn ℝ (⊤ : ℕ∞) V U →
      (∀ x ∈ tsupport (gradVec w), ∑ i : Fin 3, (V x i) ^ 2 ≤ N ^ 2) →
      ∫ x : Vec3, w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2
        ≤ 2 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => (w y • V y) i) x (basisVec j)) ^ 2)
          + 2 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => u w i) j (x, t)) ^ 2)
        ≤ C * (cutoffEnstrophy χ u t + 1) := by
  obtain ⟨hu, -, -, -, hdivu⟩ := hsol
  have hUopen : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball 0 1
  have hsuppU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1 := hρU.trans hρ1
  have hgradA : tsupport (gradVec χ) ⊆ A :=
    tsupport_gradVec_subset_of_fderiv_eq_zero hAcl hχA
  have hKnn : 0 ≤ ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨4 + 8 * (2 * Mu) ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2, ?_,
    fun t ht => ?_⟩
  · have hnn : 0 ≤ 8 * (2 * Mu) ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 :=
      mul_nonneg (by positivity) hKnn
    linarith only [hnn]
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => u (y, t)) (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_spatialSlice hu htmem
  have hdivslice : ∀ x ∈ vec3Ball (0 : Vec3) 1,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0 :=
    fun x hx => hdivu (x, t) ⟨hx, htmem⟩
  have hbd : ∀ x ∈ tsupport (gradVec χ), ∑ i : Fin 3, (u (x, t) i) ^ 2 ≤ (2 * Mu) ^ 2 := by
    intro x hx
    have h3 := sum_sq_le_of_abs_le Mu (fun i : Fin 3 => u (x, t) i) (hubd x (hgradA hx) t ht)
    nlinarith only [h3, sq_nonneg Mu]
  have hYnn : 0 ≤ ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3,
      (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h1 := hCommutatorFirst χ (fun y : Vec3 => u (y, t)) (vec3Ball (0 : Vec3) 1) (2 * Mu)
    hUopen hχ hχs hsuppU hslice hbd
  have h2 := integral_sq_fderiv_smul_le χ (fun y : Vec3 => u (y, t)) (vec3Ball (0 : Vec3) 1)
    (2 * Mu) hUopen hχ hχs hsuppU hslice hdivslice
    fun x hxne => hbd x (subset_tsupport _ hxne)
  rw [integral_cutoff_sq_spatialPartial_eq, cutoffEnstrophy_eq_integral_sq_curlVec]
  exact closure_elliptic_arith₁ _ _ _ _ (2 * Mu) hYnn hKnn h1 h2

/-- **The Hessian half of `eq:aniso:closure:elliptic`.** For a classical solution on the unit
cylinder and a cutoff supported in the unit ball, the cutoff-weighted Hessian energy of the
velocity is bounded by `C (M + 1)`, with `M = cutoffEnstrophyDissipation χ u` the tested
enstrophy dissipation. The hypothesis block is that of `energy_inequality_of_mixed_term_bound`,
extended by `hubd2` — the derivative bound of `lem:aniso:annulus`, in the exact shape
`regularAnnulus` produces it — and by the two carried inequalities `hCommutatorSecond` and
`hEllipticSecond`. -/
theorem integral_cutoff_sq_spatialSecondPartial_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mu : ℝ}
    (hubd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, |u (x, t) i| ≤ Mu)
    (hubd2 : ∀ x ∈ A, ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ,
      α 0 + α 1 + α 2 ≤ 2 → |multiPartial (fun w => u w i) α (x, t)| ≤ Mu)
    (hCommutatorSecond : ∀ (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ),
      IsOpen U → ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w → tsupport w ⊆ U →
      ContDiffOn ℝ (⊤ : ℕ∞) V U →
      (∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
          + ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2) →
      ∫ x : Vec3, w x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => V z i) y (basisVec j)) x
            (basisVec k)) ^ 2
        ≤ 4 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
              (fderiv ℝ (fun y : Vec3 =>
                fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x (basisVec k)) ^ 2)
          + 16 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2)
          + 16 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2))
    (hEllipticSecond : ∀ (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ),
      IsOpen U → ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w → tsupport w ⊆ U →
      ContDiffOn ℝ (⊤ : ℕ∞) V U →
      (∀ x ∈ U, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => V y j) x (basisVec j) = 0) →
      (∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
          + ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2) →
      ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x
            (basisVec k)) ^ 2
        ≤ 4 * (∫ x : Vec3, w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
              (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
          + 24 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2)
          + 24 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2)
        ≤ C * (cutoffEnstrophyDissipation χ u t + 1) := by
  obtain ⟨hu, -, -, -, hdivu⟩ := hsol
  have hUopen : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball 0 1
  have hsuppU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1 := hρU.trans hρ1
  have hgradA : tsupport (gradVec χ) ⊆ A :=
    tsupport_gradVec_subset_of_fderiv_eq_zero hAcl hχA
  have hK₁nn : 0 ≤ ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hK₂nn : 0 ≤ ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec χ y i) x (basisVec j)) ^ 2 :=
    integral_nonneg fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨16 + 112 * (4 * Mu) ^ 2 * ((∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2)
      + ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec χ y i) x (basisVec j)) ^ 2), ?_, fun t ht => ?_⟩
  · have hnn : 0 ≤ 112 * (4 * Mu) ^ 2 * ((∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2)
        + ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec χ y i) x (basisVec j)) ^ 2) :=
      mul_nonneg (by positivity) (by linarith only [hK₁nn, hK₂nn])
    linarith only [hnn]
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => u (y, t)) (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_spatialSlice hu htmem
  have hdivslice : ∀ x ∈ vec3Ball (0 : Vec3) 1,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0 :=
    fun x hx => hdivu (x, t) ⟨hx, htmem⟩
  have hd1 : ∀ x ∈ A, ∀ i j : Fin 3,
      |fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j)| ≤ Mu := by
    intro x hx i j
    have hα : (Pi.single j 1 : Fin 3 → ℕ) 0 + (Pi.single j 1 : Fin 3 → ℕ) 1
        + (Pi.single j 1 : Fin 3 → ℕ) 2 ≤ 2 := by
      fin_cases j <;> simp
    have h := hubd2 x hx t ht i (Pi.single j 1) hα
    rwa [← spatialPartial_eq_multiPartial_single] at h
  have hjet : ∀ x ∈ tsupport (gradVec χ), (∑ i : Fin 3, (u (x, t) i) ^ 2)
      + ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j)) ^ 2 ≤ (4 * Mu) ^ 2 := by
    intro x hx
    have h0 := sum_sq_le_of_abs_le Mu (fun i : Fin 3 => u (x, t) i) (hubd x (hgradA hx) t ht)
    have hrow : ∀ i : Fin 3,
        ∑ j : Fin 3, (fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j)) ^ 2
          ≤ 3 * Mu ^ 2 := fun i =>
      sum_sq_le_of_abs_le Mu
        (fun j : Fin 3 => fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j))
        fun j => hd1 x (hgradA hx) i j
    have hsum : ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j)) ^ 2 ≤ 9 * Mu ^ 2 := by
      rw [Fin.sum_univ_three]
      linarith only [hrow 0, hrow 1, hrow 2]
    nlinarith only [h0, hsum, sq_nonneg Mu]
  have hMnn : 0 ≤ ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec (fun y' : Vec3 => u (y', t)) y i) x
        (basisVec k)) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
  have h1 := hCommutatorSecond χ (fun y : Vec3 => u (y, t)) (vec3Ball (0 : Vec3) 1) (4 * Mu)
    hUopen hχ hχs hsuppU hslice hjet
  have h2 := hEllipticSecond χ (fun y : Vec3 => u (y, t)) (vec3Ball (0 : Vec3) 1) (4 * Mu)
    hUopen hχ hχs hsuppU hslice hdivslice hjet
  rw [integral_cutoff_sq_spatialSecondPartial_eq,
    cutoffEnstrophyDissipation_eq_integral_sq_fderiv_curlVec]
  exact closure_elliptic_arith₂ _ _ _ _ _ (4 * Mu) hMnn hK₁nn hK₂nn h1 h2

end CIV
