/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Prism

/-! # Tilt -/

@[expose] public section

namespace RupertMinimality

/-!
# L8 framework: tilting off a degenerate view (frame-free)

Step 4 of `minimality.md`.

Everything is stated with the triple product `det3 a b c = ⟪a × b, c⟫` at a
view `w` (no rotation needed): for a rotation `R` with `R w = r e_z`, `r > 0`,
`cross2 (P R a) (P R b) = det3 a b w / r`.

* `isRupert_of_tiltCert`: Lemma 1 at the view `w` with *local certificates*:
  every point is either a corner whose velocity points strictly into the
  angle formed with two other points, or lies strictly inside a triangle of
  three other points.
* `eventually_pos_affine`: `A + εB > 0` for small `ε > 0` when `A > 0`, or
  `A = 0` and `B > 0` (each test of Lemma 8.0 is such a determinant `A + εB`).
* `eventually_tilted_cycle` (Lemma 8.0, instance-wise): the sign facts
  `D0 ≥ 0`, `D0 = 0 ⇒ D1 > 0` for a predicted cycle give that cycle as the
  silhouette at `u0 + εv` for all small `ε > 0`, with (G1).
* `isRupert_of_tilted_unimodal` (Corollary 8.0′): the same, with an open
  condition on the limit depths that forces unimodality.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The triple product `det (a, b, c) = ⟪a × b, c⟫`. -/
noncomputable def det3 (a b c : ℝ³) : ℝ := ⟪cross a b, c⟫

theorem det3_add_smul (a b u v : ℝ³) (ε : ℝ) :
    det3 a b (u + ε • v) = det3 a b u + ε * det3 a b v := by
  simp only [det3, inner_add_right, real_inner_smul_right]

/-- At a rotation taking the view `w` to `r e_z`, screen orientations are
triple products with `w`. -/
theorem cross2_proj_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {w : ℝ³} {r : ℝ}
    (hRw : R.toEuclideanLin w = r • ez) (a b : ℝ³) :
    r * cross2 (projXy (R.toEuclideanLin a)) (projXy (R.toEuclideanLin b)) = det3 a b w := by
  have := inner_cross_toEuclideanLin hR a b w
  rw [hRw, real_inner_smul_right, inner_cross_ez] at this
  exact this

theorem cross2_proj_rot_pos {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {w : ℝ³} {r : ℝ}
    (hr : 0 < r) (hRw : R.toEuclideanLin w = r • ez) {a b : ℝ³} (h : 0 < det3 a b w) :
    0 < cross2 (projXy (R.toEuclideanLin a)) (projXy (R.toEuclideanLin b)) := by
  rw [← cross2_proj_rot hR hRw] at h
  exact pos_of_mul_pos_right h hr.le

theorem proj_rot_sub (R : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ³) :
    projXy (R.toEuclideanLin a) - projXy (R.toEuclideanLin b) =
      projXy (R.toEuclideanLin (a - b)) := by
  rw [map_sub, proj_xy_sub']

/-- Rotations preserve the cross product. -/
theorem cross_toEuclideanLin {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (a b : ℝ³) :
    R.toEuclideanLin (cross a b) = cross (R.toEuclideanLin a) (R.toEuclideanLin b) := by
  apply ext_inner_right ℝ
  intro c
  obtain ⟨c', rfl⟩ := (so3Isometry hR).surjective c
  rw [so3Isometry_apply, inner_toEuclideanLin_SO3 hR, inner_cross_toEuclideanLin hR]

theorem crossMatrix_apply (ω x : ℝ³) : (crossMatrix ω).toEuclideanLin x = cross ω x := by
  ext i; fin_cases i <;>
    simp [crossMatrix, cross, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- The triangle `abc` as a 3-cycle. -/
def tri {α : Type*} (a b c : α) : ZMod 3 → α := ![a, b, c]

/-- A point strictly left of the three edges of a counterclockwise triangle is
in the interior of the triangle. -/
theorem mem_interior_tri {a b c q : ℝ²} (h0 : 0 < cross2 (b - a) (c - a))
    (h1 : 0 < cross2 (b - a) (q - a)) (h2 : 0 < cross2 (c - b) (q - b))
    (h3 : 0 < cross2 (a - c) (q - c)) : q ∈ interior (convexHull ℝ (Set.range (tri a b c))) := by
  have e1 : cross2 (c - b) (a - b) = cross2 (b - a) (c - a) := by simp [cross2]; ring
  have e2 : cross2 (a - c) (b - c) = cross2 (b - a) (c - a) := by simp [cross2]; ring
  have hp : IsCcwPolygon (tri a b c) := by
    refine ⟨le_refl _, fun i j hi hj => ?_⟩
    have hcase : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
        (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide
    rcases hcase i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h0
    · change 0 < cross2 (c - b) (a - b); rw [e1]; exact h0
    · change 0 < cross2 (a - c) (b - c); rw [e2]; exact h0
  refine hp.mem_interior_of_left fun i => ?_
  have hcase : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hcase i with rfl | rfl | rfl
  exacts [h1, h2, h3]


theorem eventually_pos_affine {A B : ℝ} (h : 0 < A ∨ (A = 0 ∧ 0 < B)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A + ε * B := by
  rcases h with h | ⟨rfl, h⟩
  · have hc : Continuous fun ε : ℝ => A + ε * B := by fun_prop
    exact (hc.continuousAt.eventually (lt_mem_nhds (by simpa using h))).filter_mono
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [zero_add]; exact mul_pos hε h

/-- A local certificate for Lemma 1 at `x`, view `w`, motion `(ω, τ)`:
either `x` is a corner between `y₀` (before) and `y₁` (after) and its
velocity points strictly into the angle `y₀ x y₁`, or `x` lies strictly inside
the triangle `abc`. -/
def TiltCert (V : Finset ℝ³) (w ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, 0 < det3 (y₁ - x) (y₀ - x) w ∧
      0 < det3 (y₁ - x) (cross ω x + τ) w ∧ 0 < det3 (x - y₀) (cross ω x + τ) w) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, 0 < det3 (b - a) (c - a) w ∧ 0 < det3 (b - a) (x - a) w ∧
      0 < det3 (c - b) (x - b) w ∧ 0 < det3 (a - c) (x - c) w)

/-- **Lemma 1, frame-free, with local certificates.** -/
theorem isRupert_of_tiltCert (V : Finset ℝ³) (w : ℝ³) (hw : w ≠ 0) (ω τ : ℝ³)
    (h : ∀ x ∈ V, TiltCert V w ω τ x) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRw⟩ := exists_rotation_to_ez_pos w hw
  set P : ℝ³ → ℝ² := fun y => projXy (R.toEuclideanLin y) with hP
  set S := projXy '' convexHull ℝ ((V.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³) with hS
  have hSc : Convex ℝ S := by
    rw [hS, show (projXy : ℝ³ → ℝ²) = projL from rfl]
    exact (convex_convexHull ℝ _).linear_image projL
  have hmem : ∀ y ∈ V, P y ∈ S := fun y hy =>
    ⟨R.toEuclideanLin y, subset_convexHull ℝ _ (by
      simp only [coe_image, Set.mem_image, SetLike.mem_coe]
      exact ⟨y, hy, rfl⟩), rfl⟩
  have htri : ∀ {a b c : ℝ³}, a ∈ V → b ∈ V → c ∈ V →
      interior (convexHull ℝ (Set.range (tri (P a) (P b) (P c)))) ⊆ interior S := by
    intro a b c ha hb hc
    refine interior_mono (convexHull_min ?_ hSc)
    rintro _ ⟨i, rfl⟩
    have hcase : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hcase i with rfl | rfl | rfl
    exacts [hmem a ha, hmem b hb, hmem c hc]
  have hpos : ∀ {a b : ℝ³}, 0 < det3 a b w → 0 < cross2 (P a) (P b) :=
    fun h => cross2_proj_rot_pos hR hr hRw h
  have hsub : ∀ a b : ℝ³, P a - P b = P (a - b) := fun a b => proj_rot_sub R a b
  refine isRupert_of_firstOrderInward_image V R hR (R.toEuclideanLin ω) (R.toEuclideanLin τ) ?_
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hx'
  have hvel : screenVel (R.toEuclideanLin ω) (R.toEuclideanLin τ) (R.toEuclideanLin x) =
      P (cross ω x + τ) := by
    simp only [screenVel, crossMatrix_apply, hP, map_add, cross_toEuclideanLin hR]
  rw [hvel]
  rcases h x hx with ⟨y₀, hy₀, y₁, hy₁, h0, h1, h2⟩ | ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩
  · -- a corner
    set d := P (cross ω x + τ)
    have e0 : 0 < cross2 (P y₁ - P x) (P y₀ - P x) := by rw [hsub, hsub]; exact hpos h0
    have e1 : 0 < cross2 (P y₁ - P x) d := by rw [hsub]; exact hpos h1
    have e2 : 0 < cross2 (P x - P y₀) d := by rw [hsub]; exact hpos h2
    have ev1 := eventually_pos_affine (A := 0) (B := cross2 (P y₁ - P x) d) (Or.inr ⟨rfl, e1⟩)
    have ev2 := eventually_pos_affine (A := cross2 (P y₀ - P y₁) (P x - P y₁))
      (B := cross2 (P y₀ - P y₁) d) (Or.inl (by
        have : cross2 (P y₀ - P y₁) (P x - P y₁) = cross2 (P y₁ - P x) (P y₀ - P x) := by
          simp [cross2]; ring
        rw [this]; exact e0))
    have ev3 := eventually_pos_affine (A := 0) (B := cross2 (P x - P y₀) d) (Or.inr ⟨rfl, e2⟩)
    obtain ⟨δ, hδ, f1, f2, f3⟩ := ((show ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ from self_mem_nhdsWithin).and
      (ev1.and (ev2.and ev3))).exists
    refine ⟨δ, hδ, htri hx hy₁ hy₀ (mem_interior_tri e0 ?_ ?_ ?_)⟩
    · rw [add_sub_cancel_left, cross2_smul_right]; linarith
    · rw [show P x + δ • d - P y₁ = (P x - P y₁) + δ • d by abel, cross2_add_right,
        cross2_smul_right]; linarith
    · rw [show P x + δ • d - P y₀ = (P x - P y₀) + δ • d by abel, cross2_add_right,
        cross2_smul_right, cross2_self]; linarith
  · -- hidden
    apply isInwardAt_of_mem_interior
    refine htri ha hb hc (mem_interior_tri ?_ ?_ ?_ ?_)
    · rw [hsub, hsub]; exact hpos h0
    · rw [hsub, hsub]; exact hpos h1
    · rw [hsub, hsub]; exact hpos h2
    · rw [hsub, hsub]; exact hpos h3

/-- The sign facts of Lemma 8.0 for one determinant test. -/
def TiltSign (a b u₀ v : ℝ³) : Prop :=
  0 < det3 a b u₀ ∨ (det3 a b u₀ = 0 ∧ 0 < det3 a b v)

theorem TiltSign.eventually {a b u₀ v : ℝ³} (h : TiltSign a b u₀ v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a b (u₀ + ε • v) := by
  simp only [det3_add_smul]; exact eventually_pos_affine h

/-- The determinant tests of Lemma 8.0 hold for all small tilts. -/
theorem eventually_tilted_dets (V : Finset ℝ³) (u₀ v : ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) (u₀ + ε • v)) ∧
      (∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) (u₀ + ε • v)) := by
  classical
  refine (eventually_all.2 fun i => eventually_all.2 fun j => ?_).and
    ((eventually_all_finset V).2 fun y hy => ?_)
  · by_cases hj : j ≠ i ∧ j ≠ i + 1
    · exact ((hcyc i j hj.1 hj.2).eventually).mono fun _ h _ _ => h
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hj
  · by_cases hy' : ∀ j, y ≠ x j
    · exact (eventually_all.2 fun i => (hrest y hy hy' i).eventually).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h hy'

/-- **Lemma 8.0, instance-wise (determinant form).**  If the predicted cycle
`x` passes every determinant test in the limit (`D0 ≥ 0`, and `D1 > 0` when
`D0 = 0`), then for all small `ε > 0` it is the silhouette at the view
`u₀ + εv`: strictly convex, counterclockwise, with every other point of `V`
strictly inside (in particular (G1)). -/
theorem eventually_tilted_cycle (V : Finset ℝ³) (u₀ v : ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (x : ZMod k → ℝ³)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ R ∈ SO3, ∀ r : ℝ, 0 < r → R.toEuclideanLin (u₀ + ε • v) = r • ez →
      IsCcwPolygon (fun i => projXy (R.toEuclideanLin (x i))) ∧
      ∀ y ∈ V, (∀ j, y ≠ x j) → projXy (R.toEuclideanLin y) ∈
        interior (convexHull ℝ (Set.range fun i => projXy (R.toEuclideanLin (x i)))) := by
  filter_upwards [eventually_tilted_dets V u₀ v x hcyc hrest] with ε ⟨h1, h2⟩
  intro R hR r hr hRw
  have hp : IsCcwPolygon (fun i => projXy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRw (h1 i j hi hj)
  refine ⟨hp, fun y hy hyx => hp.mem_interior_of_left fun i => ?_⟩
  simp only [proj_rot_sub]
  exact cross2_proj_rot_pos hR hr hRw (h2 y hy hyx i)

/-- **Corollary 8.0′, eventual form.**  As Corollary 8.0′, but the depth
condition `Q` is only required at the tilted views `u₀ + εv` for all small
`ε > 0` (this covers robust unimodality of the limit depths, and also
depth ties at `u₀` broken lexicographically by the tilt, as used for weak quad
edges in `Oct9Weak.lean`). -/
theorem isRupert_of_tilted_unimodal' (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → Q z → Q (fun i => c * z i))
    (hQe : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q fun i => ⟪x i, u₀ + ε • v⟫)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) : IsRupert V := by
  classical
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u₀ + ε • v ≠ 0 := by
    have hc : Continuous fun ε : ℝ => u₀ + ε • v := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hu₀)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨h1, h2⟩, hw, hQε⟩ :=
    ((eventually_tilted_dets V u₀ v x hcyc hrest).and (hne.and hQe)).exists
  obtain ⟨R, hR, r, hr, hRw⟩ := exists_rotation_to_ez_pos _ hw
  have hp : IsCcwPolygon (fun i => projXy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRw (h1 i j hi hj)
  have hinj : Function.Injective x := fun i j hij => hp.injective (by simp only [hij])
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀ + ε • v⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀ + ε • v⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRw, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_open_unimodal V hR x hxV hinj hp ?_ Q hQo ?_ hQu
  · intro y hy hyx i
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRw (h2 y hy hyx i)
  · simp only [hdepth]
    exact hQs _ _ (inv_pos.mpr hr) hQε

/-- **Corollary 8.0′ (robust unimodality).**  In Lemma 8.0, if the limit depths
`⟪x i, u₀⟫` satisfy an open, scale-invariant condition `Q` that forces cyclic
unimodality once the depths are distinct, then `V` is Rupert. -/
theorem isRupert_of_tilted_unimodal (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → Q z → Q (fun i => c * z i))
    (hQ : Q fun i => ⟪x i, u₀⟫)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) : IsRupert V := by
  refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk x hxV hcyc hrest Q hQo hQs ?_ hQu
  have hc : Continuous fun ε : ℝ => fun i => ⟪x i, u₀ + ε • v⟫ :=
    continuous_pi fun i => by fun_prop
  have h0 : (fun ε : ℝ => fun i => ⟪x i, u₀ + ε • v⟫) 0 ∈ {z | Q z} := by simpa using hQ
  exact Eventually.filter_mono nhdsWithin_le_nhds
    (hc.continuousAt.preimage_mem_nhds (hQo.mem_nhds h0))

end Minimality

end RupertMinimality
