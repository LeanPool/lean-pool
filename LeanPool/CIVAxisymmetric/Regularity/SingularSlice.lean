/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin
public import LeanPool.CIVAxisymmetric.Statements.IsAxisymmetricOn
public import LeanPool.CIVAxisymmetric.Statements.IsBoundedNear
public import LeanPool.CIVAxisymmetric.Statements.SingularSlice
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# The singular slice at the blow-up time

`lem:aniso:annulus` starts from the set of points of the closed ball where the velocity
fails to be bounded on every backward parabolic neighbourhood ending at the blow-up time
`t = 0`. Design note R12 records why this set, rather than a boundary version of CKN's
singular set, is what the argument needs: CKN's partial-regularity theorems are stated
with a `limsup` gradient hypothesis on open space-time sets and cannot be evaluated at
`t = 0` itself (design note R3).

`IsBoundedNear u x` is the scale-invariant version of `BoundedNearOrigin`, centred at a
general point `x` and with the backward time window tied to the spatial radius; the
singular slice `singularSlice u` is its failure set. The set is closed
(`isClosed_singularSlice`), invariant under the axis rotations on the open unit ball
when `u` is axisymmetric (`rotZ_mem_singularSlice_iff`), and agrees with
`BoundedNearOrigin` at the origin (`boundedNearOrigin_iff`). The closing step of design
note R12 — a sphere disjoint from the singular slice carries a uniform bound on a whole
space-time annulus around it — is `exists_annulus_bound_of_sphere_disjoint`, obtained
from compactness of the sphere by a finite-cover argument.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-! ### Two shrinking lemmas -/

/-- If `u` is bounded by `M` on `B(x, r) × (-r², 0)` and `0 < s ≤ r`, the same bound holds
on the smaller cylinder `B(x, s) × (-s², 0)`: shrinking the radius keeps a bound valid,
because both the spatial ball and the backward time window shrink with it. -/
private theorem forall_vec3Ball_ioo_of_le {u : ParabolicPoint → Vec3} {x : Vec3} {r M s : ℝ}
    (hs : 0 < s) (hsr : s ≤ r)
    (hbound : ∀ y ∈ vec3Ball x r, ∀ t ∈ Ioo (-(r ^ 2)) 0, vec3EuclideanNorm (u (y, t)) ≤ M) :
    ∀ y ∈ vec3Ball x s, ∀ t ∈ Ioo (-(s ^ 2)) 0, vec3EuclideanNorm (u (y, t)) ≤ M := by
  intro y hy t ht
  refine hbound y (vec3Ball_mono hsr hy) t ⟨?_, ht.2⟩
  have hsq : s ^ 2 ≤ r ^ 2 := by nlinarith only [hs, hsr]
  linarith only [ht.1, hsq]

/-- If `u` is bounded by `M` on `B(x, r) × (-r², 0)` and `x'` lies within `r / 2` of `x`,
then `u` is bounded by the same `M` on `B(x', r/2) × (-(r/2)², 0)`: the triangle
inequality moves the ball, and shrinking the radius to `r / 2` keeps it, and the
matching time window, inside the original cylinder. -/
private theorem forall_vec3Ball_ioo_shift {u : ParabolicPoint → Vec3} {x x' : Vec3} {r M : ℝ}
    (hx' : x' ∈ vec3Ball x (r / 2))
    (hbound : ∀ y ∈ vec3Ball x r, ∀ t ∈ Ioo (-(r ^ 2)) 0, vec3EuclideanNorm (u (y, t)) ≤ M) :
    ∀ y ∈ vec3Ball x' (r / 2), ∀ t ∈ Ioo (-((r / 2) ^ 2)) 0, vec3EuclideanNorm (u (y, t)) ≤ M := by
  intro y hy t ht
  have hy' : vec3EuclideanNorm (y - x') < r / 2 := hy
  have hx'' : vec3EuclideanNorm (x' - x) < r / 2 := hx'
  have htri : vec3EuclideanNorm (y - x) ≤ vec3EuclideanNorm (y - x') + vec3EuclideanNorm (x' -
    x) := by
    have heq : y - x = (y - x') + (x' - x) := by abel
    rw [heq]; exact vec3EuclideanNorm_add_le _ _
  refine hbound y (mem_vec3Ball.mpr (by linarith only [htri, hy', hx''])) t ⟨?_, ht.2⟩
  have hsq : (r / 2) ^ 2 ≤ r ^ 2 := by nlinarith only [sq_nonneg r]
  linarith only [ht.1, hsq]

/-! ### Openness and closedness -/

/-- The set of points near which `u` is bounded is open: design note R12 needs the
complementary singular slice to be closed. -/
theorem isOpen_isBoundedNear (u : ParabolicPoint → Vec3) : IsOpen {x | IsBoundedNear u x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨r, M, hr, hbound⟩
  have hsub : vec3Ball x (r / 2) ⊆ {x | IsBoundedNear u x} :=
    fun x' hx' => ⟨r / 2, M, by linarith only [hr], forall_vec3Ball_ioo_shift hx' hbound⟩
  refine Filter.mem_of_superset ((isOpen_vec3Ball x (r / 2)).mem_nhds ?_) hsub
  refine mem_vec3Ball.mpr ?_
  rw [sub_self, vec3EuclideanNorm_zero]
  linarith only [hr]

/-- The singular slice at the blow-up time is closed, being the complement of the open
set of points of local boundedness. -/
theorem isClosed_singularSlice (u : ParabolicPoint → Vec3) : IsClosed (singularSlice u) := by
  have hcompl : singularSlice u = {x | IsBoundedNear u x}ᶜ := rfl
  rw [hcompl]
  exact (isOpen_isBoundedNear u).isClosed_compl

/-! ### Rotation invariance on the open unit ball -/

/-- The image of a Euclidean ball under a rotation about the vertical axis is the
Euclidean ball of the same radius around the rotated centre: rotations preserve the
Euclidean norm, so membership in the rotated ball transports along `rotZ (-φ)`. -/
theorem image_rotZ_vec3Ball (φ r : ℝ) (x : Vec3) :
    rotZ φ '' vec3Ball x r = vec3Ball (rotZ φ x) r := by
  ext y'
  simp only [mem_image, mem_vec3Ball]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have heq : rotZ φ y - rotZ φ x = rotZ φ (y - x) := (rotZ_sub_vec φ y x).symm
    rw [heq, vec3EuclideanNorm_rotZ]
    exact hy
  · intro hy'
    refine ⟨rotZ (-φ) y', ?_, rotZ_rotZ_neg φ y'⟩
    have heq : rotZ (-φ) y' - x = rotZ (-φ) (y' - rotZ φ x) := by
      rw [rotZ_sub_vec, rotZ_neg_rotZ]
    rw [heq, vec3EuclideanNorm_rotZ]
    exact hy'

/-- On the open unit ball, an axisymmetric field is bounded near a rotated point exactly
when it is bounded near the original point: rotating the witness cylinder of
`IsBoundedNear` and using `IsAxisymmetricOn.apply_rotZ` on the (shrunk) cylinder, which
stays inside the unit cylinder because the centre is shrunk away from the boundary. -/
private theorem isBoundedNear_rotZ_of_isBoundedNear {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder) {x : Vec3} (hx : x ∈ vec3Ball 0 1) (φ : ℝ)
    (h : IsBoundedNear u x) : IsBoundedNear u (rotZ φ x) := by
  obtain ⟨r, M, hr, hbound⟩ := h
  have hx1 : vec3EuclideanNorm x < 1 := by simpa using hx
  set r' : ℝ := min r (1 - vec3EuclideanNorm x) with hr'def
  have hr'pos : 0 < r' := lt_min hr (by linarith only [hx1])
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'ball : r' ≤ 1 - vec3EuclideanNorm x := min_le_right _ _
  have hr'le1 : r' ≤ 1 := hr'ball.trans (by linarith only [vec3EuclideanNorm_nonneg x])
  have hbound' : ∀ y ∈ vec3Ball x r', ∀ t ∈ Ioo (-(r' ^ 2)) 0,
      vec3EuclideanNorm (u (y, t)) ≤ M := forall_vec3Ball_ioo_of_le hr'pos hr'r hbound
  have hsubBall : vec3Ball x r' ⊆ vec3Ball 0 1 := by
    intro y hy
    have hy' : vec3EuclideanNorm (y - x) < r' := hy
    have htri : vec3EuclideanNorm y ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm x := by
      conv_lhs => rw [show y = (y - x) + x from by abel]
      exact vec3EuclideanNorm_add_le _ _
    refine mem_vec3Ball.mpr ?_
    rw [sub_zero]
    linarith only [htri, hy', hr'ball]
  have hr'sq_le1 : r' ^ 2 ≤ 1 := pow_le_one₀ hr'pos.le hr'le1
  refine ⟨r', M, hr'pos, ?_⟩
  intro y' hy' t ht
  have hy'img : y' ∈ rotZ φ '' vec3Ball x r' := (image_rotZ_vec3Ball φ r' x).symm ▸ hy'
  obtain ⟨y, hy, rfl⟩ := hy'img
  have hzUnit : (y, t) ∈ unitCylinder := by
    change y ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0
    exact ⟨hsubBall hy, by linarith only [ht.1, hr'sq_le1], ht.2⟩
  rw [haxi.apply_rotZ φ hzUnit, vec3EuclideanNorm_rotZ]
  exact hbound' y hy t ht

/-- On the open unit ball, an axisymmetric field's singular slice is invariant under the
axis rotations: `Q_φ x` is singular exactly when `x` is (design note R12, used to
transport the smallness estimate around the torus swept by a ball). -/
theorem rotZ_mem_singularSlice_iff {u : ParabolicPoint → Vec3} {x : Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder) (hx : x ∈ vec3Ball 0 1) (φ : ℝ) :
    rotZ φ x ∈ singularSlice u ↔ x ∈ singularSlice u := by
  have hiff : IsBoundedNear u (rotZ φ x) ↔ IsBoundedNear u x := by
    constructor
    · intro h
      have hφx : rotZ φ x ∈ vec3Ball 0 1 := (rotZ_mem_vec3Ball_zero_iff φ 1 x).mpr hx
      have := isBoundedNear_rotZ_of_isBoundedNear haxi hφx (-φ) h
      rwa [rotZ_neg_rotZ] at this
    · exact isBoundedNear_rotZ_of_isBoundedNear haxi hx φ
  change ¬ IsBoundedNear u (rotZ φ x) ↔ ¬ IsBoundedNear u x
  rw [hiff]

/-! ### Comparison with `BoundedNearOrigin` -/

/-- At the origin, `IsBoundedNear` agrees with `BoundedNearOrigin`: the two constants `r`
and `δ` of `BoundedNearOrigin` can always be replaced by the single radius `min r (√δ)`,
whose square is at most `δ`, and conversely `δ = r²` recovers `BoundedNearOrigin` from
`IsBoundedNear` directly. -/
theorem boundedNearOrigin_iff {u : ParabolicPoint → Vec3} :
    BoundedNearOrigin u ↔ IsBoundedNear u 0 := by
  constructor
  · rintro ⟨r, δ, M, hr, hδ, hbound⟩
    set r' : ℝ := min r (Real.sqrt δ) with hr'def
    have hr'pos : 0 < r' := lt_min hr (Real.sqrt_pos.mpr hδ)
    have hr'r : r' ≤ r := min_le_left _ _
    have hr'sq : r' ≤ Real.sqrt δ := min_le_right _ _
    have hr'sqδ : r' ^ 2 ≤ δ := (Real.le_sqrt hr'pos.le hδ.le).mp hr'sq
    refine ⟨r', M, hr'pos, ?_⟩
    intro y hy t ht
    refine hbound y (vec3Ball_mono hr'r hy) t ⟨?_, ht.2⟩
    linarith only [ht.1, hr'sqδ]
  · rintro ⟨r, M, hr, hbound⟩
    exact ⟨r, r ^ 2, M, hr, by positivity, hbound⟩

/-! ### A uniform bound on an annulus disjoint from the singular slice -/

/-- If a sphere `{|x| = R}` carries no singular point, some annulus around it, over some
backward time window, carries a single bound for `u`: the closing step of design note
R12, obtained by covering the compact sphere by finitely many bounded-near balls and
taking a Lebesgue-number–style radial projection. -/
theorem exists_annulus_bound_of_sphere_disjoint {u : ParabolicPoint → Vec3} {R : ℝ}
    (hR : 0 < R) (hdisj : ∀ x : Vec3, vec3EuclideanNorm x = R → x ∉ singularSlice u) :
    ∃ δ t₀ M : ℝ, 0 < δ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧ ∀ x : Vec3, R - δ < vec3EuclideanNorm x →
      vec3EuclideanNorm x < R + δ → ∀ t ∈ Ioo t₀ 0, vec3EuclideanNorm (u (x, t)) ≤ M := by
  classical
  set S : Set Vec3 := {x : Vec3 | vec3EuclideanNorm x = R} with hSdef
  have hSclosed : IsClosed S := isClosed_singleton.preimage continuous_vec3EuclideanNorm
  have hSsub : S ⊆ closure (vec3Ball 0 R) := by
    intro x hx
    rw [closure_vec3Ball hR]
    simpa using hx.le
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_closure_vec3Ball hR) hSclosed hSsub
  have hSne : S.Nonempty := by
    refine ⟨![R, 0, 0], ?_⟩
    have hsum : (∑ i : Fin 3, (![R, 0, 0] : Vec3) i ^ 2) = R ^ 2 := by
      simp [Fin.sum_univ_three]
    change vec3EuclideanNorm (![R, 0, 0] : Vec3) = R
    unfold vec3EuclideanNorm
    rw [hsum, Real.sqrt_sq hR.le]
  have hB : ∀ p : S, ∃ r M : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧
      ∀ y ∈ vec3Ball (p : Vec3) r, ∀ t ∈ Ioo (-(r ^ 2)) 0, vec3EuclideanNorm (u (y, t)) ≤ M := by
    rintro ⟨x, hx⟩
    have hxsing : IsBoundedNear u x := Classical.not_not.mp (hdisj x hx)
    obtain ⟨r, M, hr, hbound⟩ := hxsing
    refine ⟨min r (1 / 2), M, lt_min hr (by norm_num), min_le_right _ _, ?_⟩
    exact forall_vec3Ball_ioo_of_le (lt_min hr (by norm_num)) (min_le_left _ _) hbound
  choose r M hr hrle hbound using hB
  have hcover : S ⊆ ⋃ p : S, vec3Ball (p : Vec3) (r p / 2) := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    refine mem_vec3Ball.mpr ?_
    rw [sub_self, vec3EuclideanNorm_zero]
    linarith only [hr ⟨x, hx⟩]
  obtain ⟨t, hfin⟩ :=
    hScompact.elim_finite_subcover (fun p : S => vec3Ball (p : Vec3) (r p / 2))
      (fun p => isOpen_vec3Ball _ _) hcover
  obtain ⟨x0, hx0S⟩ := hSne
  obtain ⟨p0, hp0t, -⟩ := mem_iUnion₂.mp (hfin hx0S)
  have htne : t.Nonempty := ⟨p0, hp0t⟩
  set ρ : ℝ := t.inf' htne r with hρdef
  have hρpos : 0 < ρ := (Finset.lt_inf'_iff htne).mpr fun p _ => hr p
  set δ : ℝ := min (ρ / 2) (R / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith only [hρpos]) (by linarith only [hR])
  have hδρ : δ ≤ ρ / 2 := min_le_left _ _
  have hδR : δ ≤ R / 2 := min_le_right _ _
  refine ⟨δ, -(ρ ^ 2), t.sup' htne M, hδpos, ⟨?_, ?_⟩, ?_⟩
  · have hρle : ρ ≤ 1 / 2 := (Finset.inf'_le hp0t (f := r)).trans (hrle p0)
    nlinarith only [hρpos, hρle]
  · nlinarith only [hρpos]
  · intro x hxlo hxhi t' ht'
    have hxpos : 0 < vec3EuclideanNorm x := by linarith only [hxlo, hδR, hR]
    have hxne : vec3EuclideanNorm x ≠ 0 := hxpos.ne'
    set z : Vec3 := (R / vec3EuclideanNorm x) • x with hzdef
    have hzS : z ∈ S := by
      change vec3EuclideanNorm z = R
      rw [hzdef, vec3EuclideanNorm_smul,
        abs_of_nonneg (div_nonneg hR.le (vec3EuclideanNorm_nonneg x))]
      field_simp
    obtain ⟨p, hpt, hzp⟩ := mem_iUnion₂.mp (hfin hzS)
    have hzp' : vec3EuclideanNorm (z - (p : Vec3)) < r p / 2 := hzp
    have hcalc : (1 - R / vec3EuclideanNorm x) * vec3EuclideanNorm x
        = vec3EuclideanNorm x - R := by
      field_simp
    have hxz : vec3EuclideanNorm (x - z) = |vec3EuclideanNorm x - R| := by
      have heq : x - z = (1 - R / vec3EuclideanNorm x) • x := by
        rw [hzdef]; module
      rw [heq, vec3EuclideanNorm_smul]
      calc |1 - R / vec3EuclideanNorm x| * vec3EuclideanNorm x
          = |1 - R / vec3EuclideanNorm x| * |vec3EuclideanNorm x| := by
            rw [abs_of_nonneg (vec3EuclideanNorm_nonneg x)]
        _ = |(1 - R / vec3EuclideanNorm x) * vec3EuclideanNorm x| := (abs_mul _ _).symm
        _ = |vec3EuclideanNorm x - R| := by rw [hcalc]
    have hxzlt : vec3EuclideanNorm (x - z) < δ := by
      rw [hxz]
      rw [abs_lt]
      constructor <;> linarith only [hxlo, hxhi]
    have hxtri : vec3EuclideanNorm (x - (p : Vec3)) ≤
        vec3EuclideanNorm (x - z) + vec3EuclideanNorm (z - (p : Vec3)) := by
      have heq : x - (p : Vec3) = (x - z) + (z - (p : Vec3)) := by abel
      rw [heq]; exact vec3EuclideanNorm_add_le _ _
    have hδrp : δ ≤ r p / 2 := hδρ.trans (by
      have := Finset.inf'_le hpt (f := r); linarith only [this])
    have hxmem : x ∈ vec3Ball (p : Vec3) (r p) := by
      refine mem_vec3Ball.mpr ?_
      linarith only [hxtri, hxzlt, hzp', hδrp]
    have htmem : t' ∈ Ioo (-(r p) ^ 2) 0 := by
      have hrpge : ρ ≤ r p := Finset.inf'_le hpt (f := r)
      refine ⟨?_, ht'.2⟩
      nlinarith only [ht'.1, hrpge, hρpos]
    have := hbound p x hxmem t' htmem
    exact this.trans (Finset.le_sup' M hpt)

end CIV
