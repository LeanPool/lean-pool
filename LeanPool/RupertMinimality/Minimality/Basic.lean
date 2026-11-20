/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Sequences
public import LeanPool.RupertMinimality.MainTheorem
public import LeanPool.RupertMinimality.Pipeline.Similarity

/-! # Basic -/

@[expose] public section

namespace RupertMinimality

/-!
# Minimality: shared definitions

The setting, in the conventions of `IsRupert`
(`MainTheorem.lean`): the screen is the xy-plane, a point
`x : ℝ³` has screen position `projXy x` and depth `x 2`, and the *standard
view* is the direction `ez = e₂`.  A general view `u` is
reduced to the standard one by a rotation (`exists_rotation_to_ez`,
`isRupert_of_isRupert_image_rotation`).

Main definitions:
* `rot90` — `J`, rotation of the screen by +90°.
* `crossMatrix ω` — `[ω]×`, the matrix of `x ↦ ω × x`.
* `screenVel ω τ x` — the screen velocity `ν(x) = P(ω × x + τ)` of the
  first-order motion `(ω, τ)`.
* `IsInwardAt S p d` — `d` points strictly into `S` at `p`, i.e.
  `d ∈ int T_S(p)` for a convex polygon `S` (`isInwardAt_iff_forall_normal`).
* `IsDoubleNormalDir F u` — `u` is the direction of a double normal of `F`
  (used in L3, `DoubleNormal.lean`).
* `innerShadow`, `outerShadow` — the two shadows of `IsRupert`, so that
  `isRupert_iff_shadows` is `Iff.rfl`.
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- The standard view direction `e_z = e₂`: `projXy` forgets it. -/
noncomputable def ez : ℝ³ := EuclideanSpace.single 2 1

/-- `J`, rotation of the screen by +90°: `J (x, y) = (-y, x)`. -/
noncomputable def rot90 (p : ℝ²) : ℝ² := !₂[-p 1, p 0]

/-- `[ω]×`, the skew matrix of the linear map `x ↦ ω × x`. -/
def crossMatrix (ω : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -ω 2, ω 1;
     ω 2, 0, -ω 0;
     -ω 1, ω 0, 0]

/-- The screen velocity `ν(x) = P(ω × x + τ)` of the first-order motion
`(ω, τ)` at the point `x`, in the standard view. -/
noncomputable def screenVel (ω τ x : ℝ³) : ℝ² :=
  projXy ((crossMatrix ω).toEuclideanLin x + τ)

/-- `d` points strictly into `S` at `p`: some positive step along `d` lands in
the interior of `S`.  For a closed convex `S` with nonempty interior and
`p ∈ S` this is `d ∈ int T_S(p)`, i.e. `n ⬝ d < 0` for every nonzero outward
normal `n` at `p` (`isInwardAt_iff_forall_normal`); in particular it holds for
every `d` when `p ∈ interior S`. -/
def IsInwardAt {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (S : Set E) (p d : E) : Prop :=
  ∃ ε > (0 : ℝ), p + ε • d ∈ interior S

/-- `u` is a *double-normal direction* of `F`: there is a chord
`[a, b]`, `a ≠ b`, parallel to `u`, with `b - a ∈ N_F(b)` and `a - b ∈ N_F(a)`
(the lines through `a` and `b` perpendicular to `ab` both support `F`).  The
sign of `u` is irrelevant, and `u ≠ 0` is forced. -/
def IsDoubleNormalDir {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Set E) (u : E) : Prop :=
  ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ (∃ t : ℝ, b - a = t • u) ∧
    (∀ q ∈ F, ⟪b - a, q - b⟫ ≤ 0) ∧ (∀ q ∈ F, ⟪a - b, q - a⟫ ≤ 0)

/-- The inner shadow of `IsRupert`: `o + P(R p)` for `p ∈ S`. -/
def innerShadow (R : Matrix (Fin 3) (Fin 3) ℝ) (o : ℝ²) (S : Set ℝ³) : Set ℝ² :=
  { o + projXy (R.toEuclideanLin p) | p ∈ S }

/-- The outer shadow of `IsRupert`: `P(R p)` for `p ∈ S`. -/
def outerShadow (R : Matrix (Fin 3) (Fin 3) ℝ) (S : Set ℝ³) : Set ℝ² :=
  { projXy (R.toEuclideanLin p) | p ∈ S }

/-- `IsRupert`, restated with `innerShadow`/`outerShadow`. -/
theorem isRupert_iff_shadows (V : Finset ℝ³) :
    IsRupert V ↔ ∃ R₁ ∈ SO3, ∃ o : ℝ², ∃ R₂ ∈ SO3,
      innerShadow R₁ o (convexHull ℝ (V : Set ℝ³)) ⊆
        interior (outerShadow R₂ (convexHull ℝ (V : Set ℝ³))) :=
  Iff.rfl

/-- `IsRupert V` depends only on `convexHull ℝ V`. -/
theorem isRupert_congr_hull {V V' : Finset ℝ³}
    (h : convexHull ℝ (V : Set ℝ³) = convexHull ℝ (V' : Set ℝ³)) :
    IsRupert V ↔ IsRupert V' := by
  simp only [isRupert_iff_shadows, h]

/-- The standard-view outer shadow is `projXy '' S`. -/
theorem outerShadow_one (S : Set ℝ³) : outerShadow 1 S = projXy '' S := by
  ext x; simp [outerShadow]

theorem transpose_mem_SO3 {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q ∈ SO3) : Qᵀ ∈ SO3 := by
  have := (Matrix.mem_specialOrthogonalGroup_iff).mp hQ
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  exact ⟨by simpa using (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp this.1,
    by simpa using this.2⟩

/-- `projXy` as a linear map. -/
noncomputable def projL : ℝ³ →ₗ[ℝ] ℝ² where
  toFun := projXy
  map_add' x y := by ext i; fin_cases i <;> simp [projXy]
  map_smul' c x := by ext i; fin_cases i <;> simp [projXy]

theorem projL_apply (x : ℝ³) : projL x = projXy x := rfl

theorem proj_xy_add' (x y : ℝ³) : projXy (x + y) = projXy x + projXy y := projL.map_add x y

theorem proj_xy_smul' (c : ℝ) (x : ℝ³) : projXy (c • x) = c • projXy x := projL.map_smul c x

theorem proj_xy_sub' (x y : ℝ³) : projXy (x - y) = projXy x - projXy y := projL.map_sub x y

/-- Inner products with horizontal vectors survive the projection. -/
theorem inner_proj_xy_of_horizontal {x : ℝ³} (hx : x 2 = 0) (y : ℝ³) :
    ⟪projXy x, projXy y⟫ = ⟪x, y⟫ := by
  simp [projXy, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, hx]

/-- A vector parallel to a non-vertical plane (`⟪N, z⟫ = 0`, `N 2 ≠ 0`) with
zero projection is zero. -/
theorem eq_zero_of_proj_xy_eq_zero {N z : ℝ³} (hN : N 2 ≠ 0) (hz : ⟪N, z⟫ = 0)
    (hp : projXy z = 0) : z = 0 := by
  have h0 : z 0 = 0 := by simpa [projXy] using congrArg (fun w : ℝ² => w 0) hp
  have h1 : z 1 = 0 := by simpa [projXy] using congrArg (fun w : ℝ² => w 1) hp
  have h2 : z 2 = 0 := by
    have hmul : z 2 * N 2 = 0 := by
      simpa [PiLp.inner_apply, Fin.sum_univ_three, h0, h1] using hz
    exact (mul_eq_zero.mp hmul).resolve_right hN
  ext i; fin_cases i <;> simp [h0, h1, h2]

/-- Rupertness is invariant under rotating the vertex set (converse direction:
`Noperts.Pipeline.isRupert_image_rotation` applied to `Qᵀ`). -/
theorem isRupert_of_isRupert_image_rotation (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q ∈ SO3)
    (V : Finset ℝ³) (h : IsRupert (V.image Q.toEuclideanLin)) : IsRupert V := by
  have hQt : Qᵀ ∈ SO3 := transpose_mem_SO3 hQ
  have hQtQ : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hQ.1
  have := Noperts.Pipeline.isRupert_image_rotation Qᵀ hQt _ h
  rwa [Finset.image_image, show (Qᵀ.toEuclideanLin ∘ Q.toEuclideanLin) = id by
    funext p; simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hQtQ], Finset.image_id] at this

/-- Rotation about the z-axis with `cos = c`, `sin = s`. -/
def rotZ (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![c, -s, 0; s, c, 0; 0, 0, 1]

/-- Rotation about the x-axis with `cos = c`, `sin = s`. -/
def rotX (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, c, -s; 0, s, c]

theorem rotZ_mem_SO3 {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rotZ c s ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring_nf <;> linear_combination h
  · simp [rotZ, Matrix.det_fin_three]; linear_combination h

theorem rotX_mem_SO3 {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rotX c s ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotX, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring_nf <;> linear_combination h
  · simp [rotX, Matrix.det_fin_three]; linear_combination h

/-- Every nonzero direction is taken to the standard view axis by some
rotation. -/
theorem exists_rotation_to_ez (u : ℝ³) (hu : u ≠ 0) :
    ∃ R ∈ SO3, ∃ r : ℝ, r ≠ 0 ∧ R.toEuclideanLin u = r • ez := by
  set ρ := √(u 0 ^ 2 + u 1 ^ 2) with hρ
  have hρ2 : ρ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := Real.sq_sqrt (by positivity)
  set n := √(ρ ^ 2 + u 2 ^ 2) with hn
  have hn2 : n ^ 2 = ρ ^ 2 + u 2 ^ 2 := Real.sq_sqrt (by positivity)
  have hnpos : 0 < n := by
    rw [hn, Real.sqrt_pos, hρ2]
    by_contra hle
    apply hu
    ext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
  -- first rotation about the z-axis: u ↦ (0, ρ, u 2)
  obtain ⟨c, s, hcs, h0, h1⟩ : ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * u 0 - s * u 1 = 0 ∧
      s * u 0 + c * u 1 = ρ := by
    by_cases hρ0 : ρ = 0
    · have hu0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have hu1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      exact ⟨1, 0, by norm_num, by simp [hu0, hu1], by simp [hu0, hu1, hρ0]⟩
    · refine ⟨u 1 / ρ, u 0 / ρ, ?_, ?_, ?_⟩
      · field_simp; linarith
      · field_simp; ring
      · field_simp; linarith
  refine ⟨rotX (u 2 / n) (ρ / n) * rotZ c s,
    Submonoid.mul_mem _ (rotX_mem_SO3 (by field_simp; linarith)) (rotZ_mem_SO3 hcs),
    n, hnpos.ne', ?_⟩
  ext i
  fin_cases i <;>
    simp [rotX, rotZ, ez, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three] <;>
    field_simp
  · linear_combination h0
  · linear_combination (u 2) * h1
  · linear_combination ρ * h1 - hn2

/-- An inward direction makes a negative angle with every nonzero normal. -/
theorem IsInwardAt.inner_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {p d : E} (h : IsInwardAt S p d) {n : E} (hn : n ≠ 0)
    (hN : ∀ q ∈ S, ⟪n, q - p⟫ ≤ 0) : ⟪n, d⟫ < 0 := by
  obtain ⟨ε, hε, hin⟩ := h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hin
  have hn' : 0 < ‖n‖ := norm_pos_iff.mpr hn
  set q := p + ε • d + (r / 2 / ‖n‖) • n with hq
  have hqS : q ∈ S := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hn'.ne']
    linarith))
  have := hN q hqS
  rw [hq, show p + ε • d + (r / 2 / ‖n‖) • n - p = ε • d + (r / 2 / ‖n‖) • n by abel,
    inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq] at this
  have h2 : 0 < r / 2 / ‖n‖ * ‖n‖ ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg hε.le hcon]

/-- Converse of `IsInwardAt.inner_neg` (separation plus compactness of the
unit sphere). -/
theorem isInwardAt_of_forall_normal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) {p : E} (hp : p ∈ closure S) (d : E)
    (h : ∀ n : E, n ≠ 0 → (∀ q ∈ S, ⟪n, q - p⟫ ≤ 0) → ⟪n, d⟫ < 0) : IsInwardAt S p d := by
  by_contra hne
  have hne' : ∀ k : ℕ, p + (1 / ((k : ℝ) + 1)) • d ∉ interior S := fun k hk =>
    hne ⟨_, by positivity, hk⟩
  -- separating unit normals
  have hsep : ∀ k : ℕ, ∃ m : E, ‖m‖ = 1 ∧
      ∀ a ∈ closure S, ⟪m, a⟫ ≤ ⟪m, p + (1 / ((k : ℝ) + 1)) • d⟫ := by
    intro k
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hS.interior isOpen_interior (hne' k)
    set n := (InnerProductSpace.toDual ℝ E).symm f
    have hnf : ∀ x, ⟪n, x⟫ = f x := fun x => InnerProductSpace.toDual_symm_apply
    have hn0 : n ≠ 0 := by
      intro h0
      obtain ⟨a, ha⟩ := hint
      have := hf a ha
      rw [← hnf, ← hnf, h0, inner_zero_left, inner_zero_left] at this
      exact lt_irrefl _ this
    have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
    refine ⟨(1 / ‖n‖) • n, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp, ?_⟩
    have hcl : closure S ⊆ {a | ⟪n, a⟫ ≤ ⟪n, p + (1 / ((k : ℝ) + 1)) • d⟫} := by
      rw [← hS.closure_interior_eq_closure_of_nonempty_interior hint]
      refine closure_minimal (fun a ha => ?_) (isClosed_le (by fun_prop) (by fun_prop))
      simp only [Set.mem_ofPred_eq, hnf]
      exact (hf a ha).le
    intro a ha
    rw [inner_smul_left, inner_smul_left]
    exact mul_le_mul_of_nonneg_left (hcl ha) (by simp [hnpos.le])
  choose m hm1 hm using hsep
  obtain ⟨m₀, hm₀, φ, hφ, hlim⟩ :=
    (isCompact_sphere (0 : E) 1).tendsto_subseq (x := m) (fun k => by simp [hm1 k])
  have hm₀1 : ‖m₀‖ = 1 := by simpa using hm₀
  have hε : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlimit : ∀ a ∈ closure S, ⟪m₀, a⟫ ≤ ⟪m₀, p⟫ := by
    intro a ha
    have h1 : Tendsto (fun k => ⟪m (φ k), p + (1 / ((φ k : ℝ) + 1)) • d⟫ - ⟪m (φ k), a⟫)
        atTop (𝓝 (⟪m₀, p + (0 : ℝ) • d⟫ - ⟪m₀, a⟫)) :=
      ((hlim.inner (tendsto_const_nhds.add (hε.smul tendsto_const_nhds))).sub
        (hlim.inner tendsto_const_nhds))
    have := ge_of_tendsto h1 (Eventually.of_forall fun k => sub_nonneg.mpr (hm (φ k) a ha))
    simpa using this
  have hd : 0 ≤ ⟪m₀, d⟫ := by
    have hk : ∀ k, 0 ≤ ⟪m (φ k), d⟫ := by
      intro k
      have := hm (φ k) p hp
      rw [inner_add_right, inner_smul_right] at this
      have hpos : (0 : ℝ) < 1 / ((φ k : ℝ) + 1) := by positivity
      nlinarith
    exact ge_of_tendsto (hlim.inner tendsto_const_nhds) (Eventually.of_forall hk)
  have hm0 : m₀ ≠ 0 := by rintro rfl; simp at hm₀1
  have := h m₀ hm0 (fun q hq => by
    have := hlimit q (subset_closure hq)
    rw [inner_sub_right]; linarith)
  linarith

/-- `IsInwardAt` is the interior of the tangent cone, described by normals:
for a convex set with nonempty interior in a finite-dimensional space and
`p ∈ closure S`, `d` is inward at `p` iff `⟪n, d⟫ < 0` for every nonzero
`n ∈ N_S(p)`. (For a polygon `N_S(p)` is spanned by the outward normals of
the one or two edges at `p`, so this is the open tangent cone `int T_S(p)`.) -/
theorem isInwardAt_iff_forall_normal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) {p : E} (hp : p ∈ closure S) (d : E) :
    IsInwardAt S p d ↔ ∀ n : E, n ≠ 0 → (∀ q ∈ S, ⟪n, q - p⟫ ≤ 0) → ⟪n, d⟫ < 0 :=
  ⟨fun h _ hn hN => h.inner_neg hn hN, isInwardAt_of_forall_normal hS hint hp d⟩

/-- Once some step along `d` enters the interior, all smaller steps do. -/
theorem IsInwardAt.eventually {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {S : Set E} (hS : Convex ℝ S) {p d : E}
    (hp : p ∈ closure S) (h : IsInwardAt S p d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • d ∈ interior S := by
  obtain ⟨ε₀, hε₀, hin⟩ := h
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  have h1 : (1 - ε / ε₀) • p + (ε / ε₀) • (p + ε₀ • d) = p + ε • d := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hε₀.ne']
    module
  rw [← h1]
  exact hS.combo_closure_interior_mem_interior hp hin
    (by rw [sub_nonneg, div_le_one hε₀]; exact hε.2.le) (div_pos hε.1 hε₀) (by ring)

/-- Every point of the interior is inward in every direction. -/
theorem isInwardAt_of_mem_interior {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {S : Set E} {p : E}
    (hp : p ∈ interior S) (d : E) : IsInwardAt S p d := by
  have hc : Continuous fun ε : ℝ => p + ε • d := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), p + ε • d ∈ interior S :=
    hc.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hp)
  obtain ⟨ε, hε, hεpos⟩ := (hev.filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] 0)).exists
  exact ⟨ε, hεpos, hε⟩

/-- `IsDoubleNormalDir` is invariant under linear isometries. -/
theorem isDoubleNormalDir_image_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E ≃ₗᵢ[ℝ] E) (F : Set E) (u : E) :
    IsDoubleNormalDir (f '' F) (f u) ↔ IsDoubleNormalDir F u := by
  have key : ∀ (f : E ≃ₗᵢ[ℝ] E) (F : Set E) (u : E),
      IsDoubleNormalDir F u → IsDoubleNormalDir (f '' F) (f u) := by
    rintro f F u ⟨a, ha, b, hb, hab, ⟨t, ht⟩, hB, hA⟩
    refine ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, fun h => hab (f.injective h),
      ⟨t, by rw [← map_sub, ht, map_smul]⟩, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      rw [← map_sub, ← map_sub, f.inner_map_map]; exact hB q hq
    · rintro _ ⟨q, hq, rfl⟩
      rw [← map_sub, ← map_sub, f.inner_map_map]; exact hA q hq
  refine ⟨fun h => ?_, key f F u⟩
  have := key f.symm _ _ h
  rwa [← Set.image_comp, show (f.symm ∘ f : E → E) = id from funext f.symm_apply_apply,
    Set.image_id, f.symm_apply_apply] at this

/-- Rotations preserve inner products. -/
theorem inner_toEuclideanLin_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (x y : ℝ³) :
    ⟪R.toEuclideanLin x, R.toEuclideanLin y⟫ = ⟪x, y⟫ := by
  have hRR : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hR.1
  have e : ∀ i j, R 0 i * R 0 j + R 1 i * R 1 j + R 2 i * R 2 j =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by
    have := congrFun (congrFun hRR i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have h00 := e 0 0; have h01 := e 0 1; have h02 := e 0 2
  have h10 := e 1 0; have h11 := e 1 1; have h12 := e 1 2
  have h20 := e 2 0; have h21 := e 2 1; have h22 := e 2 2
  simp at h00 h01 h02 h10 h11 h12 h20 h21 h22
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, RCLike.inner_apply, conj_trivial]
  linear_combination x 0 * y 0 * h00 + x 0 * y 1 * h01 + x 0 * y 2 * h02 + x 1 * y 0 * h10 +
    x 1 * y 1 * h11 + x 1 * y 2 * h12 + x 2 * y 0 * h20 + x 2 * y 1 * h21 + x 2 * y 2 * h22

/-- A rotation as a linear isometry equivalence. -/
noncomputable def so3Isometry {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) : ℝ³ ≃ₗᵢ[ℝ] ℝ³ :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinearMap R.toEuclideanLin Rᵀ.toEuclideanLin
      (by
        have h : R * Rᵀ = 1 := by
          simpa using (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hR.1
        ext x i
        simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, h])
      (by
        have h : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hR.1
        ext x i
        simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, h]))
    (inner_toEuclideanLin_SO3 hR)

@[simp] theorem so3Isometry_apply {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (x : ℝ³) :
    so3Isometry hR x = R.toEuclideanLin x := rfl

/-- Rupertness is invariant under translation (converse direction). -/
theorem isRupert_of_isRupert_image_add (c : ℝ³) (V : Finset ℝ³)
    (h : IsRupert (V.image fun x => c + x)) : IsRupert V := by
  have := Noperts.Pipeline.isRupert_image_add (-c) _ h
  rwa [Finset.image_image, show ((fun x => -c + x) ∘ fun x => c + x) = id by
    funext x; simp, Finset.image_id] at this

end Minimality

end RupertMinimality
