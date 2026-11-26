/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# Drawing a graph in a surface of large genus: points of the model surfaces

The proof of (10.3) needs that every graph can be drawn in `Σ(a, b, c)` once `2a + b` is large. We
draw the graph as curves in the plane that avoid the deleted discs and that may jump across the
pasted
circles. This file gives the map `qq` from points of the plane to the model, and the invariant
`keyOf` that says when two points of the plane have the same image: two points outside all the
circles have the same image only if they are equal, and points of different handles have different
images.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface

variable (a b c : ℕ)

/-- The point `(z.1, z.2)` of the plane. -/
noncomputable def pl (z : ℝ × ℝ) : EuclideanPlane := !₂[z.1, z.2]

theorem continuous_pl : Continuous pl := by
  unfold pl
  fun_prop

theorem norm_sq (u : EuclideanPlane) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

theorem dist_centre_sq (z : ℝ × ℝ) (i : ℕ) :
    dist (pl z) (modelCentre i) ^ 2 = (z.1 - 3 * i) ^ 2 + z.2 ^ 2 := by
  rw [dist_eq_norm, norm_sq]
  simp [pl, modelCentre]

/-- `z` is outside the open discs. -/
def Ok (z : ℝ × ℝ) : Prop := ∀ i < 2 * a + b + c, 1 ≤ (z.1 - 3 * i) ^ 2 + z.2 ^ 2

/-- `z` is outside the closed discs. -/
def Clear (z : ℝ × ℝ) : Prop := ∀ i < 2 * a + b + c, 1 < (z.1 - 3 * i) ^ 2 + z.2 ^ 2

variable {a b c}

theorem Clear.ok {z : ℝ × ℝ} (h : Clear a b c z) : Ok a b c z := fun i hi ↦ (h i hi).le

theorem mem_base {z : ℝ × ℝ} (h : Ok a b c z) :
    ((pl z : EuclideanPlane) : OnePoint EuclideanPlane) ∈ modelBase (2 * a + b + c) := by
  intro i hi x hx
  obtain rfl := OnePoint.coe_injective hx
  have h₁ := h i hi
  rw [← dist_centre_sq] at h₁
  have h₂ : 0 ≤ dist (pl z) (modelCentre i) := dist_nonneg
  nlinarith

variable (a b c)

theorem infty_mem_base : (OnePoint.infty : OnePoint EuclideanPlane) ∈ modelBase (2 * a + b + c)
  := by
  intro i _ x hx
  exact absurd hx (OnePoint.infty_ne_coe x)

/-- The point of the model given by a point of the plane outside the open discs. -/
noncomputable def qq (z : ℝ × ℝ) : SurfaceModel a b c :=
  open Classical in
  if h : Ok a b c z then Quot.mk _ ⟨_, mem_base h⟩ else Quot.mk _ ⟨_, infty_mem_base a b c⟩

variable {a b c}

theorem qq_of_ok {z : ℝ × ℝ} (h : Ok a b c z) : qq a b c z = Quot.mk _ ⟨_, mem_base h⟩ :=
  dite_eq_left h

theorem continuous_mk : Continuous
    (Quot.mk _ : modelBase (2 * a + b + c) → SurfaceModel a b c) :=
  continuous_quot_mk

theorem continuousOn_qq : ContinuousOn (qq a b c) {z | Ok a b c z} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : ({z | Ok a b c z}.domRestrict (qq a b c)) =
      fun z ↦ Quot.mk _ ⟨_, mem_base z.2⟩ := by
    funext z
    exact qq_of_ok z.2
  rw [this]
  refine continuous_mk.comp (Continuous.subtype_mk ?_ _)
  exact OnePoint.continuous_coe.comp (continuous_pl.comp continuous_subtype_val)

/-! ### The invariant -/

variable (a b)

/-- The handle or cross-cap of the `i`th circle. -/
def grp (i : ℕ) : ℕ := if i < 2 * a then i / 2 else i

/-- A number that separates the pairs of antipodal points of a cross-cap. -/
noncomputable def tw (i : ℕ) (u : EuclideanPlane) : ℝ :=
  open Classical in if 2 * a ≤ i ∧ i < 2 * a + b then u 0 * u 1 else 0

variable (c)

/-- The invariant of a point of the plane. -/
noncomputable def keyPl (x : EuclideanPlane) : (ℕ × ℝ) ⊕ EuclideanPlane :=
  open Classical in
  if h : ∃ i < 2 * a + b + c, ‖x - modelCentre i‖ = 1 then
    Sum.inl (grp a h.choose, tw a b h.choose (x - modelCentre h.choose))
  else Sum.inr x

/-- The invariant of a point of the sphere. -/
noncomputable def keyS (p : OnePoint EuclideanPlane) : Option ((ℕ × ℝ) ⊕ EuclideanPlane) :=
  OnePoint.elim p none (fun x ↦ some (keyPl a b c x))

variable {a b c}

theorem modelCentre_dist {i j : ℕ} (hij : i ≠ j) {x : EuclideanPlane}
    (hi : ‖x - modelCentre i‖ = 1) (hj : ‖x - modelCentre j‖ = 1) : False := by
  have h₁ : ‖modelCentre i - modelCentre j‖ ≤ 2 := by
    calc ‖modelCentre i - modelCentre j‖
        = ‖(x - modelCentre j) - (x - modelCentre i)‖ := by congr 1; abel
      _ ≤ ‖x - modelCentre j‖ + ‖x - modelCentre i‖ := norm_sub_le _ _
      _ = 2 := by rw [hi, hj]; norm_num
  have h₂ : ‖modelCentre i - modelCentre j‖ ^ 2 = (3 * (i : ℝ) - 3 * j) ^ 2 := by
    rw [norm_sq]
    simp [modelCentre]
  have h₃ : (1 : ℝ) ≤ ((i : ℝ) - j) ^ 2 := by
    have : (i : ℤ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
    have h₄ : (1 : ℤ) ≤ ((i : ℤ) - j) ^ 2 := by
      have := sq_pos_of_ne_zero this
      omega
    exact_mod_cast h₄
  have h₅ := norm_nonneg (modelCentre i - modelCentre j)
  nlinarith

theorem keyPl_of_mem {i : ℕ} (hi : i < 2 * a + b + c) {x : EuclideanPlane}
    (h : ‖x - modelCentre i‖ = 1) :
    keyPl a b c x = Sum.inl (grp a i, tw a b i (x - modelCentre i)) := by
  classical
  have hex : ∃ i < 2 * a + b + c, ‖x - modelCentre i‖ = 1 := ⟨i, hi, h⟩
  have hspec := hex.choose_spec
  have heq : hex.choose = i := by
    by_contra hne
    exact modelCentre_dist hne hspec.2 h
  unfold keyPl
  rw [dite_eq_left hex, heq]

theorem keyPl_of_notMem {x : EuclideanPlane}
    (h : ∀ i < 2 * a + b + c, ‖x - modelCentre i‖ ≠ 1) : keyPl a b c x = Sum.inr x := by
  classical
  unfold keyPl
  rw [dite_eq_right]
  rintro ⟨i, hi, h'⟩
  exact h i hi h'

theorem keyS_glue {p q : modelBase (2 * a + b + c)} (h : ModelGlue a b (2 * a + b + c) p q) :
    keyS a b c p.1 = keyS a b c q.1 := by
  have hmir : ∀ u : EuclideanPlane, ‖modelMirror u‖ = ‖u‖ := fun u ↦ by
    have h₁ : ‖modelMirror u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq, norm_sq]
      simp [modelMirror]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h₁
  cases h with
  | handle i hi u hu p q hp hq =>
    rw [hp, hq]
    simp only [keyS, OnePoint.elim_some]
    rw [keyPl_of_mem (i := 2 * i) (by omega) (by simpa using hu),
      keyPl_of_mem (i := 2 * i + 1) (by omega) (by simpa [hmir] using hu)]
    have h₁ : grp a (2 * i) = i := by simp only [grp]; rw [ite_eq_left (by omega)]; omega
    have h₂ : grp a (2 * i + 1) = i := by simp only [grp]; rw [ite_eq_left (by omega)]; omega
    have h₃ : tw a b (2 * i) (modelCentre (2 * i) + u - modelCentre (2 * i)) = 0 := by
      simp only [tw]; rw [ite_eq_right (by omega)]
    have h₄ : tw a b (2 * i + 1) (modelCentre (2 * i + 1) + modelMirror u -
        modelCentre (2 * i + 1)) = 0 := by
      simp only [tw]; rw [ite_eq_right (by omega)]
    rw [h₁, h₂, h₃, h₄]
  | crosscap i hi u hu p q hp hq =>
    rw [hp, hq]
    simp only [keyS, OnePoint.elim_some]
    have hi' : 2 * a + i < 2 * a + b + c := by omega
    rw [keyPl_of_mem hi' (by simpa using hu),
      keyPl_of_mem hi' (by simpa [sub_eq_add_neg, add_assoc] using hu)]
    have h₃ : ∀ v : EuclideanPlane, tw a b (2 * a + i) v = v 0 * v 1 := fun v ↦ by
      simp only [tw]; rw [ite_eq_left (by omega)]
    rw [h₃, h₃]
    simp

/-- The invariant of a point of the model. -/
noncomputable def keyM : SurfaceModel a b c → Option ((ℕ × ℝ) ⊕ EuclideanPlane) :=
  Quot.lift (fun p ↦ keyS a b c p.1) fun _ _ h ↦ keyS_glue h

theorem keyM_qq {z : ℝ × ℝ} (h : Ok a b c z) :
    keyM (qq a b c z) = some (keyPl a b c (pl z)) := by
  rw [qq_of_ok h]
  rfl

theorem norm_sub_centre_sq (z : ℝ × ℝ) (i : ℕ) :
    ‖pl z - modelCentre i‖ ^ 2 = (z.1 - 3 * i) ^ 2 + z.2 ^ 2 := by
  rw [← dist_eq_norm, dist_centre_sq]

theorem keyPl_clear {z : ℝ × ℝ} (h : Clear a b c z) : keyPl a b c (pl z) = Sum.inr (pl z) := by
  refine keyPl_of_notMem fun i hi h₁ ↦ ?_
  have h₂ := h i hi
  rw [← norm_sub_centre_sq, h₁] at h₂
  norm_num at h₂

theorem pl_injective : Function.Injective pl := by
  intro z z' h
  have h₀ := congrFun (congrArg (fun v : EuclideanPlane ↦ (v : Fin 2 → ℝ)) h) 0
  have h₁ := congrFun (congrArg (fun v : EuclideanPlane ↦ (v : Fin 2 → ℝ)) h) 1
  simp only [pl] at h₀ h₁
  exact Prod.ext (by simpa using h₀) (by simpa using h₁)

/-- A point outside the closed discs has only itself as a preimage. -/
theorem eq_of_qq_eq {z z' : ℝ × ℝ} (h : Clear a b c z) (h' : Ok a b c z')
    (heq : qq a b c z = qq a b c z') : z = z' := by
  have h₁ := congrArg keyM heq
  rw [keyM_qq h.ok, keyM_qq h', keyPl_clear h] at h₁
  have h₂ := Option.some.inj h₁
  by_cases hc : ∃ i < 2 * a + b + c, ‖pl z' - modelCentre i‖ = 1
  · obtain ⟨i, hi, h₃⟩ := hc
    rw [keyPl_of_mem hi h₃] at h₂
    cases h₂
  · rw [keyPl_of_notMem fun i hi h' ↦ hc ⟨i, hi, h'⟩] at h₂
    exact pl_injective (Sum.inr.inj h₂)

/-- A point on a circle has key given by that circle. -/
theorem keyM_circle {z : ℝ × ℝ} {i : ℕ} (hi : i < 2 * a + b + c) (h : Ok a b c z)
    (hz : (z.1 - 3 * i) ^ 2 + z.2 ^ 2 = 1) :
    keyM (qq a b c z) = some (Sum.inl (grp a i, tw a b i (pl z - modelCentre i))) := by
  rw [keyM_qq h, keyPl_of_mem hi]
  have h₁ := norm_sub_centre_sq z i
  rw [hz] at h₁
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₁

end GraphMinor.GM20.Draw
