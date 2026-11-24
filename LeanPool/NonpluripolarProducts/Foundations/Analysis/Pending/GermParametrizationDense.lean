/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationData
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RiemannExtension
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicZeroSetThin
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularPointDimension
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Density of the regular part of an irreducible germ

Blueprint `lag:canonical-defining-functions`, `lag:parametrization-dense` (Demailly,
*Complex analytic and differential geometry*, II.4.19).

Given `ParametrizationData A` and its `SetsData`, the part of `A` over the complement of the
discriminant locus is dense in `A` near `0`.  For a linear form `λ` on the fibre, the
elementary symmetric functions of the values `λ(y'')` over the `q` fibre points are
holomorphic off the discriminant locus (locally they are symmetric functions of the
holomorphic sections of `SetsData.local_graph`) and bounded, so they extend across it
(Riemann extension); the resulting `h_λ(z) = P_λ(z', λ(z''))` satisfies `δ h_λ = 0` on `A`,
hence `h_λ = 0` on `A` near `0` by primality.  With `qm + 1` forms in general position
(Vandermonde) and continuity of roots of monic polynomials, every point of `A` near `0` is a
limit of fibre points over the complement of the discriminant locus.

The conclusion is the output interface `GermParametrization.LocalParametrization A`, with
`proj` the coordinate projection.
-/

@[expose] public section

open Set Filter Metric Polynomial
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationData

open FirstPass RegularLocusDense AnalyticGermDecomposition

noncomputable section

/-! ### Monic polynomials with prescribed roots -/

/-- The coefficients of `∏ (X - f_i(x))` are holomorphic where the `f_i` are. -/
theorem differentiableAt_coeff_prod_X_sub_C {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} (T : Finset ι) {f : ι → E → ℂ} {x₀ : E}
    (hf : ∀ i ∈ T, DifferentiableAt ℂ (f i) x₀) (j : ℕ) :
    DifferentiableAt ℂ (fun x => (∏ i ∈ T, (X - C (f i x))).coeff j) x₀ := by
  classical
  induction T using Finset.induction_on generalizing j with
  | empty => simp
  | insert a T ha ih =>
    simp only [Finset.prod_insert ha]
    have hX : ∀ k, DifferentiableAt ℂ (fun x => (X - C (f a x)).coeff k) x₀ := by
      intro k
      rcases k with _ | _ | k
      · simpa using (hf a (Finset.mem_insert_self a T)).neg
      · simp
      · simp [coeff_X]
    simp only [coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ =>
      (hX p.1).mul (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) p.2)

/-- The coefficients of `∏ (X - a_i)` with `|a_i| ≤ M` are bounded by `(1 + M) ^ #T`. -/
theorem norm_coeff_prod_X_sub_C_le {ι : Type*} (T : Finset ι) {a : ι → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ i ∈ T, ‖a i‖ ≤ M) (j : ℕ) :
    ‖(∏ i ∈ T, (X - C (a i))).coeff j‖ ≤ (1 + M) ^ T.card := by
  classical
  induction T using Finset.induction_on generalizing j with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
    split_ifs <;> simp
  | insert b T hb ih =>
    have ih' := fun k => ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) k
    have hb' := ha b (Finset.mem_insert_self b T)
    have hpos : 0 ≤ (1 + M) ^ T.card := pow_nonneg (by linarith) _
    rw [Finset.prod_insert hb, Finset.card_insert_of_notMem hb, mul_comm, pow_succ]
    set Q := ∏ i ∈ T, (X - C (a i))
    rcases j with _ | j
    · have h0 : (Q * (X - C (a b))).coeff 0 = -(Q.coeff 0 * a b) := by
        simp [mul_sub]
      rw [h0, norm_neg, norm_mul]
      calc ‖Q.coeff 0‖ * ‖a b‖ ≤ (1 + M) ^ T.card * M :=
            mul_le_mul (ih' 0) hb' (norm_nonneg _) hpos
        _ ≤ (1 + M) ^ T.card * (1 + M) := by nlinarith
    · rw [coeff_mul_X_sub_C]
      calc ‖Q.coeff j - Q.coeff (j + 1) * a b‖
          ≤ ‖Q.coeff j‖ + ‖Q.coeff (j + 1)‖ * ‖a b‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ (1 + M) ^ T.card + (1 + M) ^ T.card * M :=
            add_le_add (ih' j) (mul_le_mul (ih' _) hb' (norm_nonneg _) hpos)
        _ = (1 + M) ^ T.card * (1 + M) := by ring

theorem zero_mem_polydisc {n d : ℕ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    (0 : ComplexModel n) ∈ polydisc n d r₁ r₂ :=
  ⟨by simpa using h₁, fun k _ => by simpa using h₂⟩

/-! ### Fibres and their canonical polynomials -/

variable {n : ℕ} {A : Set (ComplexModel n)} {P : ParametrizationData A}

/-- The fibre of `A ∩ Δ` over a base point `x`. -/
def fibre (S : SetsData P) (x : ComplexModel P.dim) : Set (ComplexModel n) :=
  A ∩ polydisc n P.dim S.r₁ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x}

open Classical in
/-- The polynomial `∏_{y ∈ fibre} (X - ℓ(y))` (and `1` for infinite fibres). -/
def fibrePoly (S : SetsData P) (ℓ : ComplexModel n → ℂ) (x : ComplexModel P.dim) : ℂ[X] :=
  if h : (fibre S x).Finite then ∏ y ∈ h.toFinset, (X - C (ℓ y)) else 1

theorem card_toFinset_fibre (S : SetsData P) {x : ComplexModel P.dim} (hx : ‖x‖ < S.r₁)
    (hd : P.disc x ≠ 0) : (S.finite_fibre x hx hd).toFinset.card = P.deg :=
  (Set.ncard_eq_toFinset_card _ (S.finite_fibre x hx hd)).symm.trans (S.ncard_fibre x hx hd)

theorem fibrePoly_eq (S : SetsData P) (ℓ : ComplexModel n → ℂ) {x : ComplexModel P.dim}
    (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0) :
    fibrePoly S ℓ x = ∏ y ∈ (S.finite_fibre x hx hd).toFinset, (X - C (ℓ y)) :=
  dite_eq_left _

/-- Evaluating the canonical polynomial through its first `q + 1` coefficients. -/
theorem sum_coeff_fibrePoly (S : SetsData P) (ℓ : ComplexModel n → ℂ) {x : ComplexModel P.dim}
    (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0) (t : ℂ) :
    ∑ j ∈ Finset.range (P.deg + 1), (fibrePoly S ℓ x).coeff j * t ^ j =
      ∏ y ∈ (S.finite_fibre x hx hd).toFinset, (t - ℓ y) := by
  have hdeg : (fibrePoly S ℓ x).natDegree < P.deg + 1 := by
    rw [fibrePoly_eq S ℓ hx hd, natDegree_finsetProd_X_sub_C_eq_card, card_toFinset_fibre S hx hd]
    omega
  rw [← eval_eq_sum_range' hdeg, fibrePoly_eq S ℓ hx hd, eval_prod]
  simp

theorem norm_coeff_fibrePoly_le (S : SetsData P) (ℓ : ComplexModel n → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ polydisc n P.dim S.r₁ S.r₂, ‖ℓ z‖ ≤ M) {x : ComplexModel P.dim}
    (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0) (j : ℕ) :
    ‖(fibrePoly S ℓ x).coeff j‖ ≤ (1 + M) ^ P.deg := by
  rw [fibrePoly_eq S ℓ hx hd, ← card_toFinset_fibre S hx hd]
  exact norm_coeff_prod_X_sub_C_le _ hM0
    (fun y hy => by
      have hm := (Set.Finite.mem_toFinset (S.finite_fibre x hx hd)).1 hy
      exact hM y hm.1.2) j

/-- A holomorphic section of `A ∩ Δ` through a point over the complement of the
discriminant locus. -/
theorem exists_section (S : SetsData P) {y : ComplexModel n}
    (hy : y ∈ A ∩ polydisc n P.dim S.r₁ S.r₂) (hd : P.disc (coordinateProjection n P.dim y) ≠ 0) :
    ∃ g : ComplexModel P.dim → ComplexModel n,
      DifferentiableAt ℂ g (coordinateProjection n P.dim y) ∧
      g (coordinateProjection n P.dim y) = y ∧
      ∀ᶠ x in 𝓝 (coordinateProjection n P.dim y), (‖x‖ < S.r₁ ∧ P.disc x ≠ 0) ∧
        g x ∈ fibre S x := by
  obtain ⟨U, V, g, hU, -, hyU, hyV, -, hUsub, hg, hgπ, hgA, hgV⟩ := S.local_graph y hy hd
  refine ⟨g, hg.differentiableAt (hU.mem_nhds hyU), (hgV y hyV hy.1).2, ?_⟩
  filter_upwards [hU.mem_nhds hyU] with x hx
  exact ⟨hUsub hx, hgA x hx, hgπ x hx⟩

/-- The coefficients of the canonical polynomial are holomorphic off the discriminant locus. -/
theorem differentiableAt_coeff_fibrePoly (S : SetsData P) (ℓ : ComplexModel n →L[ℂ] ℂ)
    {x₀ : ComplexModel P.dim} (hx₀ : ‖x₀‖ < S.r₁) (hd₀ : P.disc x₀ ≠ 0) (j : ℕ) :
    DifferentiableAt ℂ (fun x => (fibrePoly S ℓ x).coeff j) x₀ := by
  classical
  set T := (S.finite_fibre x₀ hx₀ hd₀).toFinset with hT
  have hsec : ∀ y, ∃ g : ComplexModel P.dim → ComplexModel n, y ∈ T →
      DifferentiableAt ℂ g x₀ ∧ g x₀ = y ∧
      ∀ᶠ x in 𝓝 x₀, (‖x‖ < S.r₁ ∧ P.disc x ≠ 0) ∧ g x ∈ fibre S x := by
    intro y
    by_cases hy : y ∈ T
    · obtain ⟨hyA, hyπ⟩ := (Set.Finite.mem_toFinset _).1 hy
      have hyπ' : coordinateProjection n P.dim y = x₀ := hyπ
      obtain ⟨g, h1, h2, h3⟩ := exists_section S hyA (hyπ' ▸ hd₀)
      rw [hyπ'] at h1 h2 h3
      exact ⟨g, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => y, fun h => absurd h hy⟩
  choose G hG using hsec
  obtain ⟨y₀, hy₀⟩ : T.Nonempty := by
    rw [← Finset.card_pos, hT, card_toFinset_fibre S hx₀ hd₀]
    exact P.deg_pos
  have hne : ∀ y ∈ T, ∀ y' ∈ T, ∀ᶠ x in 𝓝 x₀, y ≠ y' → G y x ≠ G y' x := by
    intro y hy y' hy'
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun x h => absurd hyy h
    · have := ((hG y hy).1.continuousAt.sub (hG y' hy').1.continuousAt).eventually_ne (by
        rw [Pi.sub_apply, (hG y hy).2.1, (hG y' hy').2.1]; exact sub_ne_zero.2 hyy)
      exact this.mono fun x hx _ => sub_ne_zero.1 hx
  have hev : ∀ᶠ x in 𝓝 x₀, (‖x‖ < S.r₁ ∧ P.disc x ≠ 0) ∧ (∀ y ∈ T, G y x ∈ fibre S x) ∧
      ∀ y ∈ T, ∀ y' ∈ T, y ≠ y' → G y x ≠ G y' x :=
    ((hG y₀ hy₀).2.2.mono fun x hx => hx.1).and
      (((eventually_all_finset T).2 fun y hy => (hG y hy).2.2.mono fun x hx => hx.2).and
        ((eventually_all_finset T).2 fun y hy => (eventually_all_finset T).2 (hne y hy)))
  have heq : (fun x => (∏ y ∈ T, (X - C (ℓ (G y x)))).coeff j) =ᶠ[𝓝 x₀]
      fun x => (fibrePoly S ℓ x).coeff j := by
    filter_upwards [hev] with x ⟨⟨hx, hdx⟩, hmemx, hinj⟩
    have hinj' : Set.InjOn (fun y => G y x) T := fun y hy y' hy' h =>
      by_contra fun hne => hinj y hy y' hy' hne h
    have himage : T.image (fun y => G y x) = (S.finite_fibre x hx hdx).toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
        exact (Set.Finite.mem_toFinset _).2 (hmemx y hy)
      · rw [Finset.card_image_of_injOn hinj', card_toFinset_fibre S hx hdx, hT,
          card_toFinset_fibre S hx₀ hd₀]
    rw [fibrePoly_eq S ℓ hx hdx, ← himage, Finset.prod_image hinj']
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  exact differentiableAt_coeff_prod_X_sub_C T (f := fun y x => ℓ (G y x))
    (fun y hy => ℓ.differentiableAt.comp x₀ (hG y hy).1) j

/-- **Riemann extension of the canonical coefficients.** -/
theorem exists_extension_coeff_fibrePoly (S : SetsData P) (ℓ : ComplexModel n →L[ℂ] ℂ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ polydisc n P.dim S.r₁ S.r₂, ‖ℓ z‖ ≤ M) (j : ℕ) :
    ∃ F : ComplexModel P.dim → ℂ, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ F x ∧
      (P.disc x ≠ 0 → F x = (fibrePoly S ℓ x).coeff j) := by
  have hball : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ‖x‖ < S.r₁ :=
    eventually_of_mem (ball_mem_nhds 0 S.r₁_pos) fun x hx => by simpa using hx
  have hdisc : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), DifferentiableAt ℂ P.disc x :=
    eventually_of_mem (ball_mem_nhds 0 P.rad_pos) fun x hx =>
      P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hx)
  obtain ⟨F, hFd, hFe⟩ := RiemannExtension.exists_extension_euclidean hdisc
    P.disc_not_eventually_zero
    (hball.mono fun x hx hdx => differentiableAt_coeff_fibrePoly S ℓ hx hdx j)
    ⟨(1 + M) ^ P.deg, hball.mono fun x hx hdx => norm_coeff_fibrePoly_le S ℓ hM0 hM hx hdx j⟩
  exact ⟨F, hFd.and hFe⟩

/-- **Canonical defining functions** (blueprint `lag:canonical-defining-functions`): the
canonical polynomial `P_ℓ` has holomorphic coefficients near `0`, and `P_ℓ(z', ℓ(z))`
vanishes on `A` near `0`. -/
theorem exists_canonical (S : SetsData P) (ℓ : ComplexModel n →L[ℂ] ℂ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ polydisc n P.dim S.r₁ S.r₂, ‖ℓ z‖ ≤ M) :
    ∃ F : ℕ → ComplexModel P.dim → ℂ,
      (∀ᶠ x in 𝓝 0, ∀ j ∈ Finset.range (P.deg + 1), DifferentiableAt ℂ (F j) x ∧
        (P.disc x ≠ 0 → F j x = (fibrePoly S ℓ x).coeff j)) ∧
      ∀ᶠ z in 𝓝 0, z ∈ A →
        ∑ j ∈ Finset.range (P.deg + 1), F j (coordinateProjection n P.dim z) * ℓ z ^ j = 0 := by
  choose F hF using exists_extension_coeff_fibrePoly S ℓ hM0 hM
  have hF' : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ∀ j ∈ Finset.range (P.deg + 1),
      DifferentiableAt ℂ (F j) x ∧ (P.disc x ≠ 0 → F j x = (fibrePoly S ℓ x).coeff j) :=
    (eventually_all_finset _).2 fun j _ => hF j
  refine ⟨F, hF', ?_⟩
  have hπ : Tendsto (coordinateProjection n P.dim) (𝓝 0) (𝓝 0) := by
    simpa using (coordinateProjection n P.dim).continuous.tendsto 0
  have hball : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ‖x‖ < S.r₁ :=
    eventually_of_mem (ball_mem_nhds 0 S.r₁_pos) fun x hx => by simpa using hx
  have hdisc : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), DifferentiableAt ℂ P.disc x :=
    eventually_of_mem (ball_mem_nhds 0 P.rad_pos) fun x hx =>
      P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hx)
  have hΔ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ polydisc n P.dim S.r₁ S.r₂ :=
    (isOpen_polydisc _ _ _ _).mem_nhds (zero_mem_polydisc S.r₁_pos S.r₂_pos)
  have key := P.prime (fun z => P.disc (coordinateProjection n P.dim z))
    (fun z => ∑ j ∈ Finset.range (P.deg + 1), F j (coordinateProjection n P.dim z) * ℓ z ^ j)
    ((hπ.eventually hdisc).mono fun z hz => hz.comp z
      (coordinateProjection n P.dim).differentiableAt)
    ((hπ.eventually hF').mono fun z hz => DifferentiableAt.fun_sum fun j hj =>
      ((hz j hj).1.comp z (coordinateProjection n P.dim).differentiableAt).mul
        (ℓ.differentiableAt.pow j))
    ((hΔ.and (hπ.eventually (hF'.and hball))).mono fun z hz hzA => by
      obtain ⟨hzΔ, hzF, hzb⟩ := hz
      by_cases hd : P.disc (coordinateProjection n P.dim z) = 0
      · simp [hd]
      · refine mul_eq_zero_of_right _ ?_
        have hsum : ∑ j ∈ Finset.range (P.deg + 1), F j (coordinateProjection n P.dim z) * ℓ z ^ j
            = ∑ j ∈ Finset.range (P.deg + 1),
              (fibrePoly S ℓ (coordinateProjection n P.dim z)).coeff j * ℓ z ^ j :=
          Finset.sum_congr rfl fun j hj => by rw [(hzF j hj).2 hd]
        rw [hsum, sum_coeff_fibrePoly S ℓ hzb hd]
        exact Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).2 ⟨⟨hzA, hzΔ⟩, rfl⟩)
          (sub_self _))
  exact key.resolve_left fun h => P.disc_not_eventually_zero (P.base P.disc hdisc h)

/-! ### Linear forms in general position -/

/-- The coefficients `i ^ (k - d)` (for `k ≥ d`) of the `i`-th fibre form. -/
def formCoef (d i : ℕ) (k : Fin n) : ℂ := if d ≤ k.1 then (i : ℂ) ^ (k.1 - d) else 0

/-- The fibre form `λ_i(z) = ∑_{k ≥ d} i ^ (k - d) z_k`. -/
def form (n d i : ℕ) : ComplexModel n →L[ℂ] ℂ :=
  ∑ k : Fin n, formCoef d i k • EuclideanSpace.proj k

theorem form_apply (d i : ℕ) (z : ComplexModel n) :
    form n d i z = ∑ k : Fin n, formCoef d i k * z k := by
  simp [form]

theorem norm_form_le {d i : ℕ} {z : ComplexModel n} {s : ℝ}
    (hz : ∀ k : Fin n, d ≤ k.1 → ‖z k‖ ≤ s) :
    ‖form n d i z‖ ≤ (∑ k : Fin n, ‖formCoef d i k‖) * s := by
  rw [form_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  by_cases hk : d ≤ k.1
  · exact mul_le_mul_of_nonneg_left (hz k hk) (norm_nonneg _)
  · simp [formCoef, hk]

/-- Any `n - d` of the fibre forms, together with the base coordinates, separate points
(a Vandermonde argument). -/
theorem eq_zero_of_form_eq_zero {d : ℕ} {I : Finset ℕ} (hI : n - d ≤ I.card)
    {v : ComplexModel n} (hπ : coordinateProjection n d v = 0)
    (hform : ∀ i ∈ I, form n d i v = 0) : v = 0 := by
  classical
  set p : ℂ[X] := ∑ k : Fin n, if d ≤ k.1 then C (v k) * X ^ (k.1 - d) else 0 with hp
  have hcoeff : ∀ j, p.coeff j = ∑ k : Fin n, if d ≤ k.1 ∧ j = k.1 - d then v k else 0 := by
    intro j
    simp only [hp, finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : d ≤ k.1
    · simp [hk]
    · simp [hk]
  have hcard : (I.image (fun i : ℕ => (i : ℂ))).card = I.card :=
    Finset.card_image_of_injective _ Nat.cast_injective
  have hp0 : p = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero (I.image (fun i : ℕ => (i : ℂ))) ?_ ?_
    · rw [hcard, degree_lt_iff_coeff_zero]
      intro j hj
      rw [hcoeff]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [ite_eq_right]
      have := k.2
      omega
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      rw [← hform i hi, form_apply, hp, eval_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : d ≤ k.1
      · simp only [formCoef, ite_eq_left hk, eval_mul, eval_C, eval_pow, eval_X]
        ring
      · simp [hk, formCoef]
  ext k
  by_cases hk : d ≤ k.1
  · have h := hcoeff (k.1 - d)
    rw [hp0, coeff_zero, Finset.sum_eq_single k] at h
    · simpa [hk] using h.symm
    · intro k' _ hk'
      rw [ite_eq_right]
      intro h'
      exact hk' (Fin.ext (by omega))
    · simp
  · have h := congrArg (fun w : ComplexModel d => w ⟨k.1, by omega⟩) hπ
    simpa [coordinateProjection_apply, k.2] using h

/-- A uniform linear bound: a vector whose base part and whose values under any `n - d` of
the first `N` fibre forms are at most `δ` has norm at most `K δ`. -/
theorem exists_bound_forms (d N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ I ⊆ Finset.range N, n - d ≤ I.card → ∀ (v : ComplexModel n) (δ : ℝ),
      0 ≤ δ → (∀ i ∈ I, ‖form n d i v‖ ≤ δ) → ‖coordinateProjection n d v‖ ≤ δ →
        ‖v‖ ≤ K * δ := by
  classical
  have h : ∀ I : Finset ℕ, ∃ K : ℝ, 0 ≤ K ∧ (n - d ≤ I.card → ∀ (v : ComplexModel n) (δ : ℝ),
      0 ≤ δ → (∀ i ∈ I, ‖form n d i v‖ ≤ δ) → ‖coordinateProjection n d v‖ ≤ δ →
        ‖v‖ ≤ K * δ) := by
    intro I
    by_cases hI : n - d ≤ I.card
    · let T : ComplexModel n →ₗ[ℂ] (I → ℂ) × ComplexModel d :=
        (LinearMap.pi fun i : I => (form n d i.1 : ComplexModel n →ₗ[ℂ] ℂ)).prod
          (coordinateProjection n d : ComplexModel n →ₗ[ℂ] ComplexModel d)
      have hker : LinearMap.ker T = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro v hv
        have h1 := congrArg Prod.fst hv
        have h2 := congrArg Prod.snd hv
        refine eq_zero_of_form_eq_zero hI h2 fun i hi => ?_
        exact congrFun h1 ⟨i, hi⟩
      obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hker
      refine ⟨K, K.coe_nonneg, fun _ v δ hδ hform hπ => ?_⟩
      have hT : ‖T v‖ ≤ δ := by
        rw [norm_prod_le_iff]
        exact ⟨(pi_norm_le_iff_of_nonneg hδ).2 fun i => hform i.1 i.2, hπ⟩
      exact (ZeroHomClass.bound_of_antilipschitz T hK v).trans
        (mul_le_mul_of_nonneg_left hT K.coe_nonneg)
    · exact ⟨0, le_rfl, fun h => absurd h hI⟩
  choose K hK0 hK using h
  refine ⟨∑ I ∈ (Finset.range N).powerset, K I, Finset.sum_nonneg fun I _ => hK0 I,
    fun I hIN hI v δ hδ hform hπ => (hK I hI v δ hδ hform hπ).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun J _ => hK0 J) (Finset.mem_powerset.2 hIN)) hδ

/-! ### Density -/

theorem polydisc_subset_polydisc {n d : ℕ} {r₁ r₁' r₂ : ℝ} (h : r₁ ≤ r₁') :
    polydisc n d r₁ r₂ ⊆ polydisc n d r₁' r₂ := polydisc_mono h

/-- The points off the projection discriminant are dense in a sufficiently small
polydisc. The same radius can be used to build a local parametrization or a
connected regular part. -/
theorem exists_radius_subset_closure (S : SetsData P) :
    ∃ ρ₀ > 0, ρ₀ ≤ S.r₁ ∧ A ∩ polydisc n P.dim ρ₀ S.r₂ ⊆
      closure (A ∩ polydisc n P.dim ρ₀ S.r₂ ∩
        coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) := by
  classical
  set N := P.deg * (n - P.dim) + 1 with hN
  have hcan : ∀ i : ℕ, ∃ F : ℕ → ComplexModel P.dim → ℂ,
      (∀ᶠ x in 𝓝 0, ∀ j ∈ Finset.range (P.deg + 1), DifferentiableAt ℂ (F j) x ∧
        (P.disc x ≠ 0 → F j x = (fibrePoly S (form n P.dim i) x).coeff j)) ∧
      ∀ᶠ z in 𝓝 0, z ∈ A → ∑ j ∈ Finset.range (P.deg + 1),
        F j (coordinateProjection n P.dim z) * form n P.dim i z ^ j = 0 := fun i =>
    exists_canonical S (form n P.dim i)
      (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) S.r₂_pos.le) fun z hz =>
      norm_form_le fun k hk => (hz.2 k hk).le
  choose F hFb hFz using hcan
  have hdisc : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), DifferentiableAt ℂ P.disc x :=
    eventually_of_mem (ball_mem_nhds 0 P.rad_pos) fun x hx =>
      P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hx)
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1
    ((eventually_all_finset (Finset.range N)).2 fun i _ => hFz i)
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := Metric.eventually_nhds_iff_ball.1
    (((eventually_all_finset (Finset.range N)).2 fun i _ => hFb i).and hdisc)
  obtain ⟨K, hK0, hK⟩ := exists_bound_forms (n := n) P.dim N
  set M := ∑ i ∈ Finset.range N, ∑ k : Fin n, ‖formCoef P.dim i k‖ + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ i ∈ Finset.range N, ∑ k : Fin n, ‖formCoef P.dim i k‖ := by positivity
    linarith
  have hformM : ∀ i ∈ Finset.range N, ∑ k : Fin n, ‖formCoef P.dim i k‖ ≤ M := fun i hi => by
    have := Finset.single_le_sum (f := fun i => ∑ k : Fin n, ‖formCoef P.dim i k‖)
      (fun i _ => by positivity) hi
    linarith
  have hcardN : n - P.dim ≤ (Finset.range N).card := by
    rw [Finset.card_range, hN]
    exact Nat.le_succ_of_le (Nat.le_mul_of_pos_left _ P.deg_pos)
  set s := ε / (2 * (K * M + 1)) with hs
  have hKM : 0 ≤ K * M := by nlinarith
  have hs0 : 0 < s := by positivity
  have hKMs : K * (M * s) < ε := by
    have h1 : (K * M + 1) * s = ε / 2 := by
      rw [hs]; field_simp
    nlinarith
  obtain ⟨η, hη, hηs⟩ := S.small s hs0
  set ρ₀ := min (min S.r₁ ρ₁) (min η s) with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min (lt_min S.r₁_pos hρ₁) (lt_min hη hs0)
  have hρ₀r₁ : ρ₀ ≤ S.r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₀ρ₁ : ρ₀ ≤ ρ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₀η : ρ₀ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₀s : ρ₀ ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : polydisc n P.dim ρ₀ S.r₂ ⊆ polydisc n P.dim S.r₁ S.r₂ := polydisc_mono hρ₀r₁
  -- the canonical defining functions vanish on `A ∩ Δ₀`
  have hvanish : ∀ z ∈ A ∩ polydisc n P.dim ρ₀ S.r₂, ∀ i ∈ Finset.range N,
      ∑ j ∈ Finset.range (P.deg + 1),
        F i j (coordinateProjection n P.dim z) * form n P.dim i z ^ j = 0 := by
    intro z hz i hi
    refine hεs z ?_ i hi hz.1
    have hsmall := hηs z ⟨hz.1, hsub hz.2⟩ (lt_of_lt_of_le hz.2.1 hρ₀η)
    have hMs : s ≤ M * s := le_mul_of_one_le_left hs0.le hM1
    have hbd := hK (Finset.range N) subset_rfl hcardN z (M * s) (by positivity)
      (fun i hi => (norm_form_le fun k hk => (hsmall k hk).le).trans
        (mul_le_mul_of_nonneg_right (hformM i hi) hs0.le))
      ((hz.2.1.le.trans hρ₀s).trans hMs)
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt hbd hKMs
  -- density
  have hdense : A ∩ polydisc n P.dim ρ₀ S.r₂ ⊆
      closure (A ∩ polydisc n P.dim ρ₀ S.r₂ ∩
        coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) := by
    intro y hy
    rw [Metric.mem_closure_iff]
    intro e he
    set δ := e / (2 * (K + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hKδ : K * δ < e := by
      have h1 : (K + 1) * δ = e / 2 := by
        rw [hδ]; field_simp
      nlinarith
    set y' := coordinateProjection n P.dim y with hy'
    have hy'ρ₀ : ‖y'‖ < ρ₀ := hy.2.1
    have hy'b : y' ∈ ball (0 : ComplexModel P.dim) ρ₁ := by
      rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hy'ρ₀ hρ₀ρ₁
    have hFy := (hρ₁s y' hy'b).1
    have hcont : ∀ i ∈ Finset.range N, ∀ᶠ x in 𝓝 y',
        ‖∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j‖ < δ ^ P.deg := by
      intro i hi
      have hc : ContinuousAt
          (fun x => ‖∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j‖) y' :=
        (DifferentiableAt.fun_sum fun j hj => (hFy i hi j hj).1.mul_const _).continuousAt.norm
      refine hc.eventually_lt continuousAt_const ?_
      rw [hvanish y hy i hi, norm_zero]
      positivity
    have hnear : ∀ᶠ x in 𝓝 y', (∀ i ∈ Finset.range N,
        ‖∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j‖ < δ ^ P.deg) ∧
        dist x y' < δ :=
      ((eventually_all_finset _).2 hcont).and (ball_mem_nhds y' hδ0)
    have hdiscOn : DifferentiableOn ℂ P.disc (ball (0 : ComplexModel P.dim) ρ₀) := fun x hx =>
      ((hρ₁s x (ball_subset_ball hρ₀ρ₁ hx)).2).differentiableWithinAt
    have hcl := RiemannExtension.dense_compl_zeroSet isOpen_ball
      (convex_ball (0 : ComplexModel P.dim) ρ₀).isPreconnected hdiscOn (mem_ball_self hρ₀0)
      P.disc_not_eventually_zero (mem_ball_zero_iff.2 hy'ρ₀)
    obtain ⟨x, ⟨hxF, hxy⟩, hxb, hxd⟩ := mem_closure_iff_nhds.1 hcl _ hnear
    have hxρ₀ : ‖x‖ < ρ₀ := mem_ball_zero_iff.1 hxb
    have hxr₁ : ‖x‖ < S.r₁ := lt_of_lt_of_le hxρ₀ hρ₀r₁
    have hxd' : P.disc x ≠ 0 := hxd
    set Tx := (S.finite_fibre x hxr₁ hxd').toFinset with hTx
    have hroot : ∀ i, ∃ b, i ∈ Finset.range N →
        b ∈ Tx ∧ ‖form n P.dim i y - form n P.dim i b‖ < δ := by
      intro i
      by_cases hi : i ∈ Finset.range N
      · by_contra hcon
        push Not at hcon
        have hge : δ ^ P.deg ≤ ‖∑ j ∈ Finset.range (P.deg + 1),
            F i j x * form n P.dim i y ^ j‖ := by
          have hsum : ∑ j ∈ Finset.range (P.deg + 1), F i j x * form n P.dim i y ^ j
              = ∑ j ∈ Finset.range (P.deg + 1),
                (fibrePoly S (form n P.dim i) x).coeff j * form n P.dim i y ^ j :=
            Finset.sum_congr rfl fun j hj => by
              rw [((hρ₁s x (ball_subset_ball hρ₀ρ₁ hxb)).1 i hi j hj).2 hxd']
          rw [hsum, sum_coeff_fibrePoly S _ hxr₁ hxd', norm_prod, ← card_toFinset_fibre S hxr₁
            hxd',
            ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun _ _ => hδ0.le) fun b hb => (hcon b).2 hb
        exact absurd (hxF i hi) (not_lt.2 hge)
      · exact ⟨0, fun h => absurd h hi⟩
    choose b hb using hroot
    obtain ⟨b₀, hb₀, hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.range N) (t := Tx) (f := b) (n := n - P.dim) (fun i hi => (hb i hi).1)
      (by rw [card_toFinset_fibre S hxr₁ hxd', Finset.card_range, hN]; omega)
    obtain ⟨⟨hb₀A, hb₀Δ⟩, hb₀π⟩ := (Set.Finite.mem_toFinset _).1 hb₀
    have hb₀π' : coordinateProjection n P.dim b₀ = x := hb₀π
    have hbd := hK _ (Finset.filter_subset _ _) hcard.le (y - b₀) δ hδ0.le
      (fun i hi => by
        have hi' := Finset.mem_filter.1 hi
        rw [map_sub, ← hi'.2]
        exact (hb i hi'.1).2.le)
      (by rw [map_sub, norm_sub_rev, ← dist_eq_norm, hb₀π']; exact hxy.le)
    refine ⟨b₀, ⟨⟨hb₀A, ?_, hb₀Δ.2⟩, ?_⟩, ?_⟩
    · rw [hb₀π']; exact hxρ₀
    · change P.disc (coordinateProjection n P.dim b₀) ≠ 0
      rw [hb₀π']; exact hxd'
    · rw [dist_eq_norm]; exact lt_of_le_of_lt hbd hKδ
  exact ⟨ρ₀, hρ₀0, hρ₀r₁, hdense⟩

theorem nonempty_localParametrization (P : ParametrizationData A) (S : SetsData P) :
    Nonempty (GermParametrization.LocalParametrization A) := by
  obtain ⟨ρ₀, hρ₀0, hρ₀r₁, hdense⟩ := exists_radius_subset_closure S
  have hsub := polydisc_mono (n := n) (d := P.dim) (r₂ := S.r₂) hρ₀r₁
  have hABeq : A ∩ polydisc n P.dim S.r₁ S.r₂ ∩ polydisc n P.dim ρ₀ S.r₂ =
      A ∩ polydisc n P.dim ρ₀ S.r₂ ∩ polydisc n P.dim ρ₀ S.r₂ :=
    Set.ext fun z => ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, hsub h.2⟩, h.2⟩⟩
  exact ⟨{
    dim := P.dim
    proj := coordinateProjection n P.dim
    nbhd := polydisc n P.dim ρ₀ S.r₂
    isOpen_nbhd := isOpen_polydisc _ _ _ _
    zero_mem_nbhd := zero_mem_polydisc hρ₀0 S.r₂_pos
    good := A ∩ polydisc n P.dim ρ₀ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}
    good_subset := fun z hz => hz.1
    regularAtDim_of_mem_good := fun y hy =>
      RegularPointDimension.regularAtDim_of_inter_eq (isOpen_polydisc _ _ _ _) hy.1.2
        hABeq
        (S.regular y ⟨hy.1.1, hsub hy.1.2⟩ hy.2)
    isOpen_image_inter_good := fun O hO => by
      have h := S.isOpen_image (O ∩ polydisc n P.dim ρ₀ S.r₂) (hO.inter (isOpen_polydisc _ _ _ _))
      have e : O ∩ (A ∩ polydisc n P.dim ρ₀ S.r₂ ∩
          coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) =
          O ∩ polydisc n P.dim ρ₀ S.r₂ ∩ (A ∩ polydisc n P.dim S.r₁ S.r₂ ∩
            coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) :=
        Set.ext fun z => ⟨fun h => ⟨⟨h.1, h.2.1.2⟩, ⟨h.2.1.1, hsub h.2.1.2⟩, h.2.2⟩,
          fun h => ⟨h.1.1, ⟨h.2.1.1, h.1.2⟩, h.2.2⟩⟩
      rw [e]
      exact h
    subset_closure_good := hdense
    exists_eqn_of_not_le := P.exists_eqn_of_not_le }⟩

end

end SGPT.Foundations.Analysis.Pending.GermParametrizationData
