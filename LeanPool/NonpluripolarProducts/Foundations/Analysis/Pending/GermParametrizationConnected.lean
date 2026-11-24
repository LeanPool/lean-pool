/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationDense
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationSets
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HypersurfaceComplementConnected

/-!
# The regular part of an irreducible germ is connected

Blueprint `lag:regular-part-connected` (Demailly, *Complex analytic and differential
geometry*, II.4.19).

In adapted coordinates, with `ParametrizationData A` and its `SetsData`, let `g` be
holomorphic near `0 ∈ ℂᵈ` and not identically zero.  On small polydiscs `Δ` the set
`G = A ∩ Δ ∩ π⁻¹{δ g ≠ 0}` is connected, dense in `A ∩ Δ`, and consists of regular points of
dimension `d`.  If `G ⊆ U₁ ∪ U₂` with `U₁, U₂` open and disjoint on `G`, the local
holomorphic sections through the fibre points exhaust the nearby fibres, so the polynomials
`W_j(x, T) = ∏_{y ∈ F_x ∩ U_j} (T - u(y))` have holomorphic bounded coefficients on the
connected complement `Y` of the hypersurface `{δ g = 0}` in a ball, and extend holomorphically
(Riemann).  `W_1(z', u(z)) W_2(z', u(z))` vanishes on `G`, hence on `A` near `0`; by primality
one factor, say `W_1(z', u(z))`, vanishes on `A` near `0`.  As `u` separates fibre points, all
fibres over points of `Y` near `0` lie in `U₁`.  The property `F_x ⊆ U₁` is locally constant on
the connected set `Y` (local sections again), so every fibre over `Y` lies in `U₁`, and `G`
does not meet `U₂`.
-/

@[expose] public section

open Set Filter Metric Polynomial
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationData

open FirstPass RegularLocusDense AnalyticGermDecomposition

noncomputable section

variable {n : ℕ} {A : Set (ComplexModel n)} {P : ParametrizationData A}

/-! ### Local sections exhaust the nearby fibres -/

/-- Near a base point off the discriminant locus, holomorphic sections through the fibre
points are pairwise distinct and exhaust the fibres. -/
theorem exists_local_sections (S : SetsData P) {x₀ : ComplexModel P.dim} (hx₀ : ‖x₀‖ < S.r₁)
    (hd₀ : P.disc x₀ ≠ 0) :
    ∃ G : ComplexModel n → ComplexModel P.dim → ComplexModel n,
      (∀ y ∈ fibre S x₀, DifferentiableAt ℂ (G y) x₀ ∧ G y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, ∃ (hx : ‖x‖ < S.r₁) (hdx : P.disc x ≠ 0),
        (∀ y ∈ fibre S x₀, G y x ∈ fibre S x) ∧ InjOn (fun y => G y x) (fibre S x₀) ∧
        (S.finite_fibre x hx hdx).toFinset =
          (S.finite_fibre x₀ hx₀ hd₀).toFinset.image (fun y => G y x) := by
  classical
  set T := (S.finite_fibre x₀ hx₀ hd₀).toFinset with hT
  have hTmem : ∀ y, y ∈ T ↔ y ∈ fibre S x₀ := fun y => Set.Finite.mem_toFinset _
  have hsec : ∀ y, ∃ g : ComplexModel P.dim → ComplexModel n, y ∈ fibre S x₀ →
      DifferentiableAt ℂ g x₀ ∧ g x₀ = y ∧
      ∀ᶠ x in 𝓝 x₀, (‖x‖ < S.r₁ ∧ P.disc x ≠ 0) ∧ g x ∈ fibre S x := by
    intro y
    by_cases hy : y ∈ fibre S x₀
    · obtain ⟨hyA, hyπ⟩ := hy
      have hyπ' : coordinateProjection n P.dim y = x₀ := hyπ
      obtain ⟨g, h1, h2, h3⟩ := exists_section S hyA (hyπ' ▸ hd₀)
      rw [hyπ'] at h1 h2 h3
      exact ⟨g, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => y, fun h => absurd h hy⟩
  choose G hG using hsec
  refine ⟨G, fun y hy => ⟨(hG y hy).1, (hG y hy).2.1⟩, ?_⟩
  obtain ⟨y₀, hy₀⟩ : T.Nonempty := by
    rw [← Finset.card_pos, hT, card_toFinset_fibre S hx₀ hd₀]
    exact P.deg_pos
  have hne : ∀ y ∈ T, ∀ y' ∈ T, ∀ᶠ x in 𝓝 x₀, y ≠ y' → G y x ≠ G y' x := by
    intro y hy y' hy'
    have hy1 := (hTmem y).1 hy
    have hy1' := (hTmem y').1 hy'
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun x h => absurd hyy h
    · have := ((hG y hy1).1.continuousAt.sub (hG y' hy1').1.continuousAt).eventually_ne (by
        rw [Pi.sub_apply, (hG y hy1).2.1, (hG y' hy1').2.1]; exact sub_ne_zero.2 hyy)
      exact this.mono fun x hx _ => sub_ne_zero.1 hx
  have hev : ∀ᶠ x in 𝓝 x₀, (‖x‖ < S.r₁ ∧ P.disc x ≠ 0) ∧ (∀ y ∈ T, G y x ∈ fibre S x) ∧
      ∀ y ∈ T, ∀ y' ∈ T, y ≠ y' → G y x ≠ G y' x :=
    ((hG y₀ ((hTmem y₀).1 hy₀)).2.2.mono fun x hx => hx.1).and
      (((eventually_all_finset T).2 fun y hy =>
        (hG y ((hTmem y).1 hy)).2.2.mono fun x hx => hx.2).and
        ((eventually_all_finset T).2 fun y hy => (eventually_all_finset T).2 (hne y hy)))
  filter_upwards [hev] with x ⟨⟨hx, hdx⟩, hmemx, hinj⟩
  have hinj' : Set.InjOn (fun y => G y x) (fibre S x₀) := fun y hy y' hy' h =>
    by_contra fun hne => hinj y ((hTmem y).2 hy) y' ((hTmem y').2 hy') hne h
  refine ⟨hx, hdx, fun y hy => hmemx y ((hTmem y).2 hy), hinj', ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (Set.Finite.mem_toFinset _).2 (hmemx y hy)
  · rw [Finset.card_image_of_injOn (fun y hy y' hy' h =>
      hinj' ((hTmem y).1 (Finset.mem_coe.1 hy)) ((hTmem y').1 (Finset.mem_coe.1 hy')) h),
      card_toFinset_fibre S hx hdx, hT, card_toFinset_fibre S hx₀ hd₀]

/-- Along the local sections, membership in a set `O` which is relatively clopen on the
fibres near `y` is locally constant. -/
theorem eventually_section_mem_iff {S : SetsData P} {O : Set (ComplexModel n)}
    {x₀ : ComplexModel P.dim} (hfin : (fibre S x₀).Finite)
    {G : ComplexModel n → ComplexModel P.dim → ComplexModel n}
    (hG : ∀ y ∈ fibre S x₀, DifferentiableAt ℂ (G y) x₀ ∧ G y x₀ = y)
    (hO : ∀ y ∈ fibre S x₀, ∀ᶠ z in 𝓝 y,
      z ∈ fibre S (coordinateProjection n P.dim z) → (z ∈ O ↔ y ∈ O)) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ fibre S x₀, G y x ∈ fibre S x → (G y x ∈ O ↔ y ∈ O) := by
  refine hfin.eventually_all.2 fun y hy => ?_
  have ht := (hG y hy).1.continuousAt.tendsto
  rw [(hG y hy).2] at ht
  filter_upwards [ht.eventually (hO y hy)] with x hx hmem
  have hπ : coordinateProjection n P.dim (G y x) = x := hmem.2
  exact hx (by rw [hπ]; exact hmem)

/-- The property `F_x ⊆ O` of the fibres is locally constant off the discriminant locus, for
`O` relatively clopen on the fibres. -/
theorem eventually_fibre_subset_iff (S : SetsData P) (O : Set (ComplexModel n))
    {x₀ : ComplexModel P.dim} (hx₀ : ‖x₀‖ < S.r₁) (hd₀ : P.disc x₀ ≠ 0)
    (hO : ∀ y ∈ fibre S x₀, ∀ᶠ z in 𝓝 y,
      z ∈ fibre S (coordinateProjection n P.dim z) → (z ∈ O ↔ y ∈ O)) :
    ∀ᶠ x in 𝓝 x₀, (fibre S x ⊆ O ↔ fibre S x₀ ⊆ O) := by
  obtain ⟨G, hG, hev⟩ := exists_local_sections S hx₀ hd₀
  filter_upwards [hev, eventually_section_mem_iff (S.finite_fibre x₀ hx₀ hd₀) hG hO]
    with x ⟨hx, hdx, hmem, _, himage⟩ hOx
  have hset : fibre S x = (fun y => G y x) '' fibre S x₀ := by
    have := congrArg (fun s : Finset (ComplexModel n) => (s : Set (ComplexModel n))) himage
    simp only [Finset.coe_image, Set.Finite.coe_toFinset] at this
    exact this
  rw [hset, Set.image_subset_iff]
  exact ⟨fun h y hy => (hOx y hy (hmem y hy)).1 (h hy),
    fun h y hy => (hOx y hy (hmem y hy)).2 (h hy)⟩

/-! ### The polynomials of the fibre points in a set -/

open Classical in
/-- The polynomial `∏_{y ∈ fibre ∩ O} (X - ℓ(y))` (and `1` for infinite fibres). -/
def fibrePolyOn (S : SetsData P) (O : Set (ComplexModel n)) (ℓ : ComplexModel n → ℂ)
    (x : ComplexModel P.dim) : ℂ[X] :=
  if h : (fibre S x).Finite then ∏ y ∈ h.toFinset.filter (· ∈ O), (X - C (ℓ y)) else 1

open Classical in
theorem fibrePolyOn_eq (S : SetsData P) (O : Set (ComplexModel n)) (ℓ : ComplexModel n → ℂ)
    {x : ComplexModel P.dim} (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0) :
    fibrePolyOn S O ℓ x = ∏ y ∈ (S.finite_fibre x hx hd).toFinset.filter (· ∈ O), (X - C (ℓ y)) :=
  dite_eq_left _

open Classical in
theorem sum_coeff_fibrePolyOn (S : SetsData P) (O : Set (ComplexModel n))
    (ℓ : ComplexModel n → ℂ) {x : ComplexModel P.dim} (hx : ‖x‖ < S.r₁) (hd : P.disc x ≠ 0)
    (t : ℂ) :
    ∑ j ∈ Finset.range (P.deg + 1), (fibrePolyOn S O ℓ x).coeff j * t ^ j =
      ∏ y ∈ (S.finite_fibre x hx hd).toFinset.filter (· ∈ O), (t - ℓ y) := by
  have hdeg : (fibrePolyOn S O ℓ x).natDegree < P.deg + 1 := by
    rw [fibrePolyOn_eq S O ℓ hx hd, natDegree_finsetProd_X_sub_C_eq_card]
    have := Finset.card_filter_le (S.finite_fibre x hx hd).toFinset (· ∈ O)
    rw [card_toFinset_fibre S hx hd] at this
    omega
  rw [← eval_eq_sum_range' hdeg, fibrePolyOn_eq S O ℓ hx hd, eval_prod]
  simp

theorem norm_coeff_fibrePolyOn_le (S : SetsData P) (O : Set (ComplexModel n))
    (ℓ : ComplexModel n → ℂ) {M : ℝ} (hM0 : 0 ≤ M) {x : ComplexModel P.dim} (hx : ‖x‖ < S.r₁)
    (hd : P.disc x ≠ 0) (hM : ∀ y ∈ fibre S x, ‖ℓ y‖ ≤ M) (j : ℕ) :
    ‖(fibrePolyOn S O ℓ x).coeff j‖ ≤ (1 + M) ^ P.deg := by
  classical
  rw [fibrePolyOn_eq S O ℓ hx hd]
  refine (norm_coeff_prod_X_sub_C_le _ hM0 (fun y hy =>
    hM y ((Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 hy).1)) j).trans ?_
  rw [← card_toFinset_fibre S hx hd]
  exact pow_le_pow_right₀ (by linarith) (Finset.card_filter_le _ _)

open Classical in
/-- The coefficients of `∏_{y ∈ F_x ∩ O} (X - ℓ(y))` are holomorphic off the discriminant
locus, for `ℓ` holomorphic and `O` relatively clopen on the fibres. -/
theorem differentiableAt_coeff_fibrePolyOn (S : SetsData P) (O : Set (ComplexModel n))
    (ℓ : ComplexModel n → ℂ) {x₀ : ComplexModel P.dim} (hx₀ : ‖x₀‖ < S.r₁)
    (hd₀ : P.disc x₀ ≠ 0) (hℓ : ∀ y ∈ fibre S x₀, DifferentiableAt ℂ ℓ y)
    (hO : ∀ y ∈ fibre S x₀, ∀ᶠ z in 𝓝 y,
      z ∈ fibre S (coordinateProjection n P.dim z) → (z ∈ O ↔ y ∈ O)) (j : ℕ) :
    DifferentiableAt ℂ (fun x => (fibrePolyOn S O ℓ x).coeff j) x₀ := by
  obtain ⟨G, hG, hev⟩ := exists_local_sections S hx₀ hd₀
  set T := (S.finite_fibre x₀ hx₀ hd₀).toFinset with hT
  have hTmem : ∀ y, y ∈ T ↔ y ∈ fibre S x₀ := fun y => Set.Finite.mem_toFinset _
  have heq : (fun x => (∏ y ∈ T.filter (· ∈ O), (X - C (ℓ (G y x)))).coeff j) =ᶠ[𝓝 x₀]
      fun x => (fibrePolyOn S O ℓ x).coeff j := by
    filter_upwards [hev, eventually_section_mem_iff (S.finite_fibre x₀ hx₀ hd₀) hG hO]
      with x ⟨hx, hdx, hmem, hinj, himage⟩ hOx
    rw [fibrePolyOn_eq S O ℓ hx hdx, himage, Finset.filter_image, Finset.prod_image]
    · refine congrArg (fun p : ℂ[X] => p.coeff j) ?_
      rw [Finset.prod_filter, Finset.prod_filter]
      refine Finset.prod_congr (s₂ := T) rfl fun y hy => ?_
      have h := hOx y ((hTmem y).1 hy) (hmem y ((hTmem y).1 hy))
      by_cases h1 : y ∈ O
      · rw [ite_eq_left h1, ite_eq_left (h.2 h1)]
      · rw [ite_eq_right h1, ite_eq_right (mt h.1 h1)]
    · intro y hy y' hy' h
      exact hinj ((hTmem y).1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1)
        ((hTmem y').1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy')).1) h
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  refine differentiableAt_coeff_prod_X_sub_C (T.filter (· ∈ O)) (f := fun y x => ℓ (G y x))
    (fun y hy => ?_) j
  have hy' := (hTmem y).1 (Finset.mem_filter.1 hy).1
  have h1 := hℓ y hy'
  rw [← (hG y hy').2] at h1
  exact h1.comp x₀ (hG y hy').1

/-! ### The primitive element on the fibres -/

theorem differentiableAt_fibreForm (P : ParametrizationData A) {z : ComplexModel n}
    (hz : coordinateProjection n P.dim z ∈ ball 0 P.rad) :
    DifferentiableAt ℂ (fibreForm P.dim P.coef) z := by
  unfold fibreForm
  refine DifferentiableAt.fun_sum fun k _ => ?_
  by_cases hk : P.dim ≤ k.1
  · simp only [hk, ite_true]
    exact (((P.differentiableOn_coef k).differentiableAt (isOpen_ball.mem_nhds hz)).comp z
      (coordinateProjection n P.dim).differentiableAt).mul
      (EuclideanSpace.proj (𝕜 := ℂ) k).differentiableAt
  · simp only [hk, ite_false]
    exact differentiableAt_const _

theorem exists_bound_fibreForm (S : SetsData P) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ∀ y ∈ fibre S x,
      ‖fibreForm P.dim P.coef y‖ ≤ M := by
  have hc : ∀ k, ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ‖P.coef k x‖ < ‖P.coef k 0‖ + 1 :=
    fun k => (((P.differentiableOn_coef k).differentiableAt (isOpen_ball.mem_nhds
      (mem_ball_self P.rad_pos))).continuousAt.norm).eventually_lt continuousAt_const
        (lt_add_one _)
  refine ⟨∑ k : Fin n, (‖P.coef k 0‖ + 1) * S.r₂,
    Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) S.r₂_pos.le, ?_⟩
  filter_upwards [Filter.eventually_all.2 hc] with x hx y hy
  have hπ : coordinateProjection n P.dim y = x := hy.2
  unfold fibreForm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  by_cases hk : P.dim ≤ k.1
  · rw [ite_eq_left hk, norm_mul, hπ]
    exact mul_le_mul (hx k).le (hy.1.2.2 k hk).le (norm_nonneg _) (by positivity)
  · rw [ite_eq_right hk, norm_zero]
    exact mul_nonneg (by positivity) S.r₂_pos.le

/-- The primitive element separates the points of a fibre off the discriminant locus. -/
theorem eq_of_fibreForm_eq (S : SetsData P) {x : ComplexModel P.dim} (hd : P.disc x ≠ 0)
    {y y' : ComplexModel n} (hy : y ∈ fibre S x) (hy' : y' ∈ fibre S x)
    (h : fibreForm P.dim P.coef y = fibreForm P.dim P.coef y') : y = y' := by
  have hπ : coordinateProjection n P.dim y = x := hy.2
  have hπ' : coordinateProjection n P.dim y' = x := hy'.2
  calc y = P.graphPoint (coordinateProjection n P.dim y) (fibreForm P.dim P.coef y) :=
        P.eq_graphPoint hy.1.1 (S.polydisc_subset hy.1.2) (by rw [hπ]; exact hd)
    _ = P.graphPoint (coordinateProjection n P.dim y') (fibreForm P.dim P.coef y') := by
        rw [hπ, hπ', h]
    _ = y' := (P.eq_graphPoint hy'.1.1 (S.polydisc_subset hy'.1.2) (by rw [hπ']; exact hd)).symm

/-- `∑_j F_j(z') u(z) ^ j`. -/
def canonicalEval (P : ParametrizationData A) (F : ℕ → ComplexModel P.dim → ℂ)
    (z : ComplexModel n) : ℂ :=
  ∑ j ∈ Finset.range (P.deg + 1), F j (coordinateProjection n P.dim z) * fibreForm P.dim P.coef z
    ^ j

theorem eventually_differentiableAt_canonicalEval {F : ℕ → ComplexModel P.dim → ℂ}
    (hF : ∀ᶠ x in 𝓝 0, ∀ j ∈ Finset.range (P.deg + 1), DifferentiableAt ℂ (F j) x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (canonicalEval P F) z := by
  have hπt : Tendsto (coordinateProjection n P.dim) (𝓝 0) (𝓝 0) := by
    simpa using (coordinateProjection n P.dim).continuous.tendsto 0
  filter_upwards [hπt.eventually hF, hπt.eventually (ball_mem_nhds 0 P.rad_pos)] with z hz hzr
  unfold canonicalEval
  exact DifferentiableAt.fun_sum fun j hj =>
    ((hz j hj).comp z (coordinateProjection n P.dim).differentiableAt).mul
      ((differentiableAt_fibreForm P hzr).pow j)

open Classical in
/-- **Riemann extension** of the coefficients of `∏_{y ∈ F_x ∩ O} (X - u(y))`. -/
theorem exists_extension_coeff_fibrePolyOn (S : SetsData P) {h : ComplexModel P.dim → ℂ}
    (hh : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) (hne : ¬ ∀ᶠ x in 𝓝 0, h x = 0)
    (hhd : ∀ x, h x ≠ 0 → P.disc x ≠ 0) (O : Set (ComplexModel n))
    (hO : ∀ᶠ x₀ in 𝓝 0, h x₀ ≠ 0 → ∀ y ∈ fibre S x₀, ∀ᶠ z in 𝓝 y,
      z ∈ fibre S (coordinateProjection n P.dim z) → (z ∈ O ↔ y ∈ O)) :
    ∃ F : ℕ → ComplexModel P.dim → ℂ, ∀ᶠ x in 𝓝 0, ∀ j ∈ Finset.range (P.deg + 1),
      DifferentiableAt ℂ (F j) x ∧
        (h x ≠ 0 → F j x = (fibrePolyOn S O (fibreForm P.dim P.coef) x).coeff j) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fibreForm S
  have hball : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ‖x‖ < S.r₁ ∧ ‖x‖ < P.rad :=
    eventually_of_mem (ball_mem_nhds 0 (lt_min S.r₁_pos P.rad_pos)) fun x hx => by
      have := mem_ball_zero_iff.1 hx
      exact ⟨this.trans_le (min_le_left _ _), this.trans_le (min_le_right _ _)⟩
  have hj : ∀ j, ∃ F : ComplexModel P.dim → ℂ, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ F x ∧
      (h x ≠ 0 → F x = (fibrePolyOn S O (fibreForm P.dim P.coef) x).coeff j) := by
    intro j
    obtain ⟨F, hFd, hFe⟩ := RiemannExtension.exists_extension_euclidean (h := h)
      (f := fun x => (fibrePolyOn S O (fibreForm P.dim P.coef) x).coeff j) hh hne
      ((hball.and hO).mono fun x hx hx0 =>
        differentiableAt_coeff_fibrePolyOn S O _ hx.1.1 (hhd x hx0)
          (fun y hy => differentiableAt_fibreForm P (by
            rw [show coordinateProjection n P.dim y = x from hy.2]
            exact mem_ball_zero_iff.2 hx.1.2))
          (hx.2 hx0) j)
      ⟨(1 + M) ^ P.deg, (hball.and hM).mono fun x hx hx0 =>
        norm_coeff_fibrePolyOn_le S O _ hM0 hx.1.1 (hhd x hx0) hx.2 j⟩
    exact ⟨F, hFd.and hFe⟩
  choose F hF using hj
  exact ⟨F, (eventually_all_finset _).2 fun j _ => hF j⟩

open Classical in
/-- If `W_O(z', u(z))` vanishes on `A` near `0`, then the fibres over some points of `Y` lie
in `O`. -/
theorem exists_fibre_subset_of_vanish (S : SetsData P) {h : ComplexModel P.dim → ℂ}
    {Y : Set (ComplexModel P.dim)} (hY0 : (0 : ComplexModel P.dim) ∈ closure Y)
    (hYsub : ∀ x ∈ Y, h x ≠ 0 ∧ ‖x‖ < S.r₁ ∧ P.disc x ≠ 0) (O : Set (ComplexModel n))
    {F : ℕ → ComplexModel P.dim → ℂ}
    (hF : ∀ᶠ x in 𝓝 0, ∀ j ∈ Finset.range (P.deg + 1),
      (h x ≠ 0 → F j x = (fibrePolyOn S O (fibreForm P.dim P.coef) x).coeff j))
    (hvan : ∀ᶠ z in 𝓝 0, z ∈ A → canonicalEval P F z = 0) :
    ∃ x ∈ Y, fibre S x ⊆ O := by
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 hvan
  set ε' := ε / (n + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hεε : ((n : ℝ) + 1) * ε' = ε := by rw [hε']; field_simp
  obtain ⟨η, hη, hηs⟩ := S.small ε' hε'0
  have hnear : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), (∀ j ∈ Finset.range (P.deg + 1),
      (h x ≠ 0 → F j x = (fibrePolyOn S O (fibreForm P.dim P.coef) x).coeff j)) ∧
      ‖x‖ < min η ε' :=
    hF.and (eventually_of_mem (ball_mem_nhds 0 (lt_min hη hε'0)) fun x hx =>
      mem_ball_zero_iff.1 hx)
  obtain ⟨x, ⟨hFx, hxm⟩, hxY⟩ := mem_closure_iff_nhds.1 hY0 _ hnear
  obtain ⟨hx0, hxr, hdx⟩ := hYsub x hxY
  refine ⟨x, hxY, fun y hy => ?_⟩
  have hπ : coordinateProjection n P.dim y = x := hy.2
  have hyb : y ∈ ball (0 : ComplexModel n) ε := by
    have hpoly : y ∈ polydisc n P.dim ε' ε' :=
      ⟨by rw [hπ]; exact hxm.trans_le (min_le_right _ _),
        fun k hk => hηs y hy.1 (by rw [hπ]; exact hxm.trans_le (min_le_left _ _)) k hk⟩
    have := polydisc_subset_ball hε'0 hpoly
    rwa [hεε] at this
  have hsum : ∑ j ∈ Finset.range (P.deg + 1),
      (fibrePolyOn S O (fibreForm P.dim P.coef) x).coeff j * fibreForm P.dim P.coef y ^ j = 0 := by
    calc _ = canonicalEval P F y := by
          unfold canonicalEval
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hπ, hFx j hj hx0]
      _ = 0 := hεs y hyb hy.1.1
  rw [sum_coeff_fibrePolyOn S O _ hxr hdx, Finset.prod_eq_zero_iff] at hsum
  obtain ⟨y', hy', hyy'⟩ := hsum
  obtain ⟨hy'1, hy'O⟩ := Finset.mem_filter.1 hy'
  rw [eq_of_fibreForm_eq S hdx hy ((Set.Finite.mem_toFinset _).1 hy'1) (sub_eq_zero.1 hyy')]
  exact hy'O

/-- If the fibres over some point of a preconnected set `Y` off the discriminant locus lie in
a relatively clopen `O`, then so do the fibres over every point of `Y`. -/
theorem false_of_fibre_subset (S : SetsData P) {Y : Set (ComplexModel P.dim)}
    (hY : IsPreconnected Y) (hYsub : ∀ x ∈ Y, ‖x‖ < S.r₁ ∧ P.disc x ≠ 0)
    {O : Set (ComplexModel n)}
    (hO : ∀ x₀ ∈ Y, ∀ y ∈ fibre S x₀, ∀ᶠ z in 𝓝 y,
      z ∈ fibre S (coordinateProjection n P.dim z) → (z ∈ O ↔ y ∈ O))
    {x₁ x₂ : ComplexModel P.dim} (hx₁ : x₁ ∈ Y) (hx₂ : x₂ ∈ Y) (h₁ : fibre S x₁ ⊆ O)
    (h₂ : ¬ fibre S x₂ ⊆ O) : False := by
  have hloc : ∀ x₀ ∈ Y, ∀ᶠ x in 𝓝 x₀, (fibre S x ⊆ O ↔ fibre S x₀ ⊆ O) := fun x₀ hx₀ =>
    eventually_fibre_subset_iff S O (hYsub x₀ hx₀).1 (hYsub x₀ hx₀).2 (hO x₀ hx₀)
  obtain ⟨x, -, hx1, hx2⟩ := hY {x | ∀ᶠ x' in 𝓝 x, fibre S x' ⊆ O}
    {x | ∀ᶠ x' in 𝓝 x, ¬ fibre S x' ⊆ O} isOpen_setOfPred_eventually_nhds
    isOpen_setOfPred_eventually_nhds
    (fun x₀ hx₀ => by
      by_cases h : fibre S x₀ ⊆ O
      · exact Or.inl ((hloc x₀ hx₀).mono fun x hx => hx.2 h)
      · exact Or.inr ((hloc x₀ hx₀).mono fun x hx => mt hx.1 h))
    ⟨x₁, hx₁, (hloc x₁ hx₁).mono fun x hx => hx.2 h₁⟩
    ⟨x₂, hx₂, (hloc x₂ hx₂).mono fun x hx => mt hx.1 h₂⟩
  exact hx2.self_of_nhds hx1.self_of_nhds

/-! ### Density of the part off the discriminant locus -/

/-! ### Connectedness -/

open Classical in
theorem isPreconnected_regularPart_aux (S : SetsData P) {h : ComplexModel P.dim → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hρr₁ : ρ ≤ S.r₁) (hh : DifferentiableOn ℂ h (ball 0 ρ))
    (hne : ¬ ∀ᶠ x in 𝓝 0, h x = 0) (hhd : ∀ x, h x ≠ 0 → P.disc x ≠ 0)
    (hdense : A ∩ polydisc n P.dim ρ S.r₂ ⊆
      closure (A ∩ polydisc n P.dim ρ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x | h x ≠ 0})) :
    IsPreconnected
      (A ∩ polydisc n P.dim ρ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x | h x ≠ 0}) := by
  set G := A ∩ polydisc n P.dim ρ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x | h x ≠ 0}
    with hGdef
  set Y := ball (0 : ComplexModel P.dim) ρ \ h ⁻¹' {0} with hYdef
  have hYo : IsOpen Y := hh.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hYc : IsPreconnected Y :=
    (HypersurfaceComplementConnected.isPathConnected_ball_diff_zeroSet hρ hh
      hne).isConnected.isPreconnected
  have hY0 : (0 : ComplexModel P.dim) ∈ closure Y :=
    RiemannExtension.dense_compl_zeroSet isOpen_ball (convex_ball _ ρ).isPreconnected hh
      (mem_ball_self hρ) hne (mem_ball_self hρ)
  have hYsub : ∀ x ∈ Y, ‖x‖ < S.r₁ ∧ P.disc x ≠ 0 := fun x hx =>
    ⟨(mem_ball_zero_iff.1 hx.1).trans_le hρr₁, hhd x hx.2⟩
  have hmemG : ∀ x ∈ Y, ∀ y ∈ fibre S x, y ∈ G := fun x hx y hy => by
    have hπ : coordinateProjection n P.dim y = x := hy.2
    refine ⟨⟨hy.1.1, ?_, hy.1.2.2⟩, ?_⟩
    · rw [hπ]; exact mem_ball_zero_iff.1 hx.1
    · change h (coordinateProjection n P.dim y) ≠ 0
      rw [hπ]; exact hx.2
  have hGY : ∀ y ∈ G, coordinateProjection n P.dim y ∈ Y ∧
      y ∈ fibre S (coordinateProjection n P.dim y) := fun y hy =>
    ⟨⟨mem_ball_zero_iff.2 hy.1.2.1, hy.2⟩, ⟨hy.1.1, polydisc_mono hρr₁ hy.1.2⟩,
      Set.mem_singleton _⟩
  have hclopen : ∀ {O O' : Set (ComplexModel n)}, IsOpen O → IsOpen O' → G ⊆ O ∪ O' →
      ¬ (G ∩ (O ∩ O')).Nonempty → ∀ x₀ ∈ Y, ∀ y ∈ fibre S x₀, ∀ᶠ z in 𝓝 y,
        z ∈ fibre S (coordinateProjection n P.dim z) → (z ∈ O ↔ y ∈ O) := by
    intro O O' hO hO' hc hd x₀ hx₀ y hy
    by_cases hyO : y ∈ O
    · exact eventually_of_mem (hO.mem_nhds hyO) fun z hz _ => iff_of_true hz hyO
    · have hyO' : y ∈ O' := (hc (hmemG x₀ hx₀ y hy)).resolve_left hyO
      have hyY : y ∈ coordinateProjection n P.dim ⁻¹' Y := by
        change coordinateProjection n P.dim y ∈ Y
        rw [show coordinateProjection n P.dim y = x₀ from hy.2]
        exact hx₀
      filter_upwards [hO'.mem_nhds hyO',
        (hYo.preimage (coordinateProjection n P.dim).continuous).mem_nhds hyY]
        with z hzO' hzY hzF
      exact iff_of_false (fun hzO => hd ⟨z, hmemG _ hzY z hzF, hzO, hzO'⟩) hyO
  have hhev : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), DifferentiableAt ℂ h x :=
    eventually_of_mem (ball_mem_nhds 0 hρ) fun x hx =>
      hh.differentiableAt (isOpen_ball.mem_nhds hx)
  intro U₁ U₂ hU₁ hU₂ hcover hne₁ hne₂
  by_contra hdisj
  have hdisj' : ¬ (G ∩ (U₂ ∩ U₁)).Nonempty := by rwa [inter_comm U₂ U₁]
  have hcover' : G ⊆ U₂ ∪ U₁ := by rwa [union_comm]
  have hO₁ := hclopen hU₁ hU₂ hcover hdisj
  have hO₂ := hclopen hU₂ hU₁ hcover' hdisj'
  obtain ⟨F₁, hF₁⟩ := exists_extension_coeff_fibrePolyOn S hhev hne hhd U₁
    (eventually_of_mem (ball_mem_nhds 0 hρ) fun x₀ hx₀ hx0 => hO₁ x₀ ⟨hx₀, hx0⟩)
  obtain ⟨F₂, hF₂⟩ := exists_extension_coeff_fibrePolyOn S hhev hne hhd U₂
    (eventually_of_mem (ball_mem_nhds 0 hρ) fun x₀ hx₀ hx0 => hO₂ x₀ ⟨hx₀, hx0⟩)
  have hd₁ := eventually_differentiableAt_canonicalEval (n := n) (A := A)
    (hF₁.mono fun x hx j hj => (hx j hj).1)
  have hd₂ := eventually_differentiableAt_canonicalEval (n := n) (A := A)
    (hF₂.mono fun x hx j hj => (hx j hj).1)
  have hπt : Tendsto (coordinateProjection n P.dim) (𝓝 0) (𝓝 0) := by
    simpa using (coordinateProjection n P.dim).continuous.tendsto 0
  -- `W₁(z', u(z)) W₂(z', u(z))` vanishes on `G`
  have hvanG : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ G →
      canonicalEval P F₁ z * canonicalEval P F₂ z = 0 := by
    filter_upwards [hπt.eventually (hF₁.and hF₂)] with z hz hzG
    obtain ⟨hzY, hzF⟩ := hGY z hzG
    obtain ⟨hr, hd⟩ := hYsub _ hzY
    have hx0 : h (coordinateProjection n P.dim z) ≠ 0 := hzY.2
    have hzT : z ∈ (S.finite_fibre _ hr hd).toFinset := (Set.Finite.mem_toFinset _).2 hzF
    have e1 : canonicalEval P F₁ z = ∏ y ∈ (S.finite_fibre _ hr hd).toFinset.filter (· ∈ U₁),
        (fibreForm P.dim P.coef z - fibreForm P.dim P.coef y) := by
      rw [← sum_coeff_fibrePolyOn S U₁ (fibreForm P.dim P.coef) hr hd]
      unfold canonicalEval
      exact Finset.sum_congr rfl fun j hj => by rw [(hz.1 j hj).2 hx0]
    have e2 : canonicalEval P F₂ z = ∏ y ∈ (S.finite_fibre _ hr hd).toFinset.filter (· ∈ U₂),
        (fibreForm P.dim P.coef z - fibreForm P.dim P.coef y) := by
      rw [← sum_coeff_fibrePolyOn S U₂ (fibreForm P.dim P.coef) hr hd]
      unfold canonicalEval
      exact Finset.sum_congr rfl fun j hj => by rw [(hz.2 j hj).2 hx0]
    rcases hcover hzG with hz1 | hz2
    · rw [e1, Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hzT, hz1⟩) (sub_self _), zero_mul]
    · rw [e2, Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hzT, hz2⟩) (sub_self _), mul_zero]
  -- hence on `A` near `0`, by density and continuity
  have hvanA : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ A →
      canonicalEval P F₁ z * canonicalEval P F₂ z = 0 := by
    obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 (hd₁.and (hd₂.and hvanG))
    have hΔ : polydisc n P.dim ρ S.r₂ ∈ 𝓝 (0 : ComplexModel n) :=
      (isOpen_polydisc _ _ _ _).mem_nhds (zero_mem_polydisc hρ S.r₂_pos)
    filter_upwards [ball_mem_nhds (0 : ComplexModel n) hε, hΔ] with z hzb hzΔ hzA
    have hzcl : z ∈ closure (ball 0 ε ∩ G) := isOpen_ball.inter_closure ⟨hzb, hdense ⟨hzA, hzΔ⟩⟩
    have hcont : ContinuousAt (fun z => canonicalEval P F₁ z * canonicalEval P F₂ z) z :=
      ((hεs z hzb).1.mul (hεs z hzb).2.1).continuousAt
    have hsub : (fun z => canonicalEval P F₁ z * canonicalEval P F₂ z) '' (ball 0 ε ∩ G) ⊆
        {0} := by
      rintro _ ⟨w, ⟨hwb, hwG⟩, rfl⟩
      exact (hεs w hwb).2.2 hwG
    have := closure_mono hsub (mem_closure_image hcont hzcl)
    rwa [closure_singleton] at this
  have hYsub' : ∀ x ∈ Y, h x ≠ 0 ∧ ‖x‖ < S.r₁ ∧ P.disc x ≠ 0 := fun x hx =>
    ⟨hx.2, hYsub x hx⟩
  rcases P.prime _ _ hd₁ hd₂ hvanA with hv | hv
  · obtain ⟨x₁, hx₁, hsub₁⟩ := exists_fibre_subset_of_vanish S hY0 hYsub' U₁
      (hF₁.mono fun x hx j hj => (hx j hj).2) hv
    obtain ⟨z, hzG, hzU⟩ := hne₂
    exact false_of_fibre_subset S hYc hYsub hO₁ hx₁ (hGY z hzG).1 hsub₁
      fun hsub => hdisj ⟨z, hzG, hsub (hGY z hzG).2, hzU⟩
  · obtain ⟨x₁, hx₁, hsub₁⟩ := exists_fibre_subset_of_vanish S hY0 hYsub' U₂
      (hF₂.mono fun x hx j hj => (hx j hj).2) hv
    obtain ⟨z, hzG, hzU⟩ := hne₁
    exact false_of_fibre_subset S hYc hYsub hO₂ hx₁ (hGY z hzG).1 hsub₁
      fun hsub => hdisj' ⟨z, hzG, hsub (hGY z hzG).2, hzU⟩

/-- **Connected dense regular parts.** -/
theorem exists_isPreconnected_regularPart (P : ParametrizationData A) (S : SetsData P)
    {g : ComplexModel P.dim → ℂ} (hg : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ g x)
    (hgne : ¬ ∀ᶠ x in 𝓝 0, g x = 0) {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 0) :
    ∃ Δ : Set (ComplexModel n), IsOpen Δ ∧ (0 : ComplexModel n) ∈ Δ ∧ A ∩ Δ ⊆ N ∧
      IsPreconnected (A ∩ Δ ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x * g x ≠ 0}) ∧
      A ∩ Δ ⊆ closure (A ∩ Δ ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x * g x ≠ 0}) ∧
      ∀ y ∈ A ∩ Δ, P.disc (coordinateProjection n P.dim y) * g (coordinateProjection n P.dim y)
        ≠ 0 →
        RegularAtDim (n := n) (M := ComplexModel n) (A ∩ Δ) y P.dim := by
  obtain ⟨ρ₀, hρ₀, hρ₀r₁, hdense₀⟩ := exists_radius_subset_closure S
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  set ε' := ε / (n + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hεε : ((n : ℝ) + 1) * ε' = ε := by rw [hε']; field_simp
  obtain ⟨η, hη, hηs⟩ := S.small ε' hε'0
  have hdg : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim),
      DifferentiableAt ℂ P.disc x ∧ DifferentiableAt ℂ g x :=
    (eventually_of_mem (ball_mem_nhds 0 P.rad_pos) fun x hx =>
      P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hx)).and hg
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := Metric.eventually_nhds_iff_ball.1 hdg
  set ρ := min (min ρ₀ ρ₁) (min η ε') with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₀ hρ₁) (lt_min hη hε'0)
  have hρρ₀ : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρρ₁ : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hρη : ρ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hρε : ρ ≤ ε' := (min_le_right _ _).trans (min_le_right _ _)
  have hρr₁ : ρ ≤ S.r₁ := hρρ₀.trans hρ₀r₁
  have hh : DifferentiableOn ℂ (fun x => P.disc x * g x) (ball 0 ρ) := fun x hx =>
    ((hρ₁s x (ball_subset_ball hρρ₁ hx)).1.mul
      (hρ₁s x (ball_subset_ball hρρ₁ hx)).2).differentiableWithinAt
  have hne : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), P.disc x * g x = 0 := by
    intro h0
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hdg.and h0)
    have hdd : DifferentiableOn ℂ P.disc (ball 0 r) := fun z hz =>
      (hball z hz).1.1.differentiableWithinAt
    have hgc : ContinuousOn g (ball 0 r) := fun z hz =>
      (hball z hz).1.2.continuousAt.continuousWithinAt
    have := RiemannExtension.eqOn_zero_of_eqOn_zero_compl_zeroSet isOpen_ball
      (convex_ball 0 r).isPreconnected hdd (mem_ball_self hr) P.disc_not_eventually_zero hgc
      fun z hz hdz => (mul_eq_zero.1 (hball z hz).2).resolve_left hdz
    exact hgne (eventually_of_mem (ball_mem_nhds 0 hr) this)
  have hsubΔ : polydisc n P.dim ρ S.r₂ ⊆ polydisc n P.dim S.r₁ S.r₂ := polydisc_mono hρr₁
  -- density of the part off the discriminant locus
  have h1 : A ∩ polydisc n P.dim ρ S.r₂ ⊆ closure (A ∩ polydisc n P.dim ρ S.r₂ ∩
      coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0}) := by
    intro y hy
    have := (isOpen_polydisc n P.dim ρ S.r₂).inter_closure
      ⟨hy.2, hdense₀ ⟨hy.1, polydisc_mono hρρ₀ hy.2⟩⟩
    refine closure_mono ?_ this
    rintro z ⟨hzΔ, ⟨hzA, -⟩, hzd⟩
    exact ⟨⟨hzA, hzΔ⟩, hzd⟩
  -- density of `G`, through local graphs
  have hY : ball (0 : ComplexModel P.dim) ρ ⊆
      closure (ball 0 ρ \ (fun x => P.disc x * g x) ⁻¹' {0}) :=
    RiemannExtension.dense_compl_zeroSet isOpen_ball (convex_ball _ ρ).isPreconnected hh
      (mem_ball_self hρ0) hne
  have h2 : A ∩ polydisc n P.dim ρ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x ≠ 0} ⊆
      closure (A ∩ polydisc n P.dim ρ S.r₂ ∩
        coordinateProjection n P.dim ⁻¹' {x | P.disc x * g x ≠ 0}) := by
    rintro y ⟨⟨hyA, hyΔ⟩, hyd⟩
    obtain ⟨U, V, s, hU, -, hyU, hyV, -, -, hs, hπs, hsA, hVA⟩ :=
      S.local_graph y ⟨hyA, hsubΔ hyΔ⟩ hyd
    have hsy : s (coordinateProjection n P.dim y) = y := (hVA y hyV hyA).2
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨O, hOt, hO, hyO⟩ := _root_.mem_nhds_iff.1 ht
    have hWo : IsOpen (U ∩ s ⁻¹' (O ∩ polydisc n P.dim ρ S.r₂) ∩ ball 0 ρ) :=
      (hs.continuousOn.isOpen_inter_preimage hU (hO.inter (isOpen_polydisc _ _ _ _))).inter
        isOpen_ball
    have hyW : coordinateProjection n P.dim y ∈
        U ∩ s ⁻¹' (O ∩ polydisc n P.dim ρ S.r₂) ∩ ball 0 ρ :=
      ⟨⟨hyU, by rw [mem_preimage, hsy]; exact ⟨hyO, hyΔ⟩⟩, mem_ball_zero_iff.2 hyΔ.1⟩
    obtain ⟨x, ⟨⟨hxU, hxO, hxΔ⟩, -⟩, -, hx0⟩ :=
      mem_closure_iff_nhds.1 (hY (mem_ball_zero_iff.2 hyΔ.1)) _ (hWo.mem_nhds hyW)
    refine ⟨s x, hOt hxO, ⟨(hsA x hxU).1, hxΔ⟩, ?_⟩
    change P.disc (coordinateProjection n P.dim (s x)) * g (coordinateProjection n P.dim (s x)) ≠ 0
    rw [hπs x hxU]
    exact hx0
  have hdense := h1.trans (closure_minimal h2 isClosed_closure)
  refine ⟨polydisc n P.dim ρ S.r₂, isOpen_polydisc _ _ _ _, zero_mem_polydisc hρ0 S.r₂_pos,
    ?_, ?_, hdense, ?_⟩
  · intro z hz
    apply hεN
    have hpoly : z ∈ polydisc n P.dim ε' ε' :=
      ⟨hz.2.1.trans_le hρε, fun k hk => hηs z ⟨hz.1, hsubΔ hz.2⟩ (hz.2.1.trans_le hρη) k hk⟩
    have := polydisc_subset_ball hε'0 hpoly
    rwa [hεε] at this
  · exact isPreconnected_regularPart_aux S (h := fun x => P.disc x * g x) hρ0 hρr₁ hh hne
      (fun x hx => left_ne_zero_of_mul hx) hdense
  · intro y hy hyd
    refine RegularPointDimension.regularAtDim_of_inter_eq (isOpen_polydisc _ _ _ _) hy.2 ?_
      (S.regular y ⟨hy.1, hsubΔ hy.2⟩ (left_ne_zero_of_mul hyd))
    exact Set.ext fun z => ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, hsubΔ h.2⟩, h.2⟩⟩

end

end SGPT.Foundations.Analysis.Pending.GermParametrizationData
