/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw8
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Topology.LocalAtTarget

/-!
# Counting the cuffs of a model surface

A model `SurfaceModel a b c` has at least `c` cuffs. The last `c` circles are not pasted to
anything,
so near them the model looks like the plane outside a disc. So their points are not interior points
of
the model, by invariance of domain. A circle of radius `3/2` around one of them consists of interior
points, and it separates this circle from the others. So the `c` circles lie in different components
of the boundary.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface Metric

variable {a b c : ℕ}

/-- `z` is off the closed discs whose circles are pasted. -/
def Free (a b : ℕ) (z : ℝ × ℝ) : Prop := ∀ i < 2 * a + b, 1 < (z.1 - 3 * i) ^ 2 + z.2 ^ 2

/-- The points on circles that are pasted. -/
def glued (a b : ℕ) : Set (OnePoint EuclideanPlane) :=
  {p | ∃ i < 2 * a + b, ∃ v : EuclideanPlane, p = v ∧ dist v (modelCentre i) = 1}

/-- The map that sends the points of pasted circles to infinity, and fixes the other points. -/
noncomputable def kap (a b : ℕ) (p : OnePoint EuclideanPlane) : OnePoint EuclideanPlane :=
  open Classical in if p ∈ glued a b then OnePoint.infty else p

theorem kap_glue {n : ℕ} {p q : modelBase n} (h : ModelGlue a b n p q) :
    kap a b p.1 = kap a b q.1 := by
  have key : p.1 ∈ glued a b ∧ q.1 ∈ glued a b := by
    cases h with
    | handle i hi u hu p q hp hq =>
      have hm : ‖modelMirror u‖ = 1 := by
        have h₁ : ‖modelMirror u‖ ^ 2 = 1 := by
          rw [norm_sq]
          have h₂ := norm_sq u
          rw [hu] at h₂
          simp only [modelMirror]
          simp
          linarith
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₁
      exact ⟨⟨2 * i, by omega, _, hp, by simp [dist_eq_norm, hu]⟩,
        ⟨2 * i + 1, by omega, _, hq, by simp [dist_eq_norm, hm]⟩⟩
    | crosscap i hi u hu p q hp hq =>
      exact ⟨⟨2 * a + i, by omega, _, hp, by simp [dist_eq_norm, hu]⟩,
        ⟨2 * a + i, by omega, _, hq, by simp [hu]⟩⟩
  simp only [kap, ite_eq_left key.1, ite_eq_left key.2]

/-- The map `kap` on the model. -/
noncomputable def keyK : SurfaceModel a b c → OnePoint EuclideanPlane :=
  Quot.lift (fun p ↦ kap a b p.1) fun _ _ h ↦ kap_glue h

theorem notMem_glued {z : ℝ × ℝ} (hf : Free a b z) :
    ((pl z : EuclideanPlane) : OnePoint EuclideanPlane) ∉ glued a b := by
  rintro ⟨i, hi, v, hv, hd⟩
  obtain rfl := OnePoint.coe_injective hv
  have h₁ := hf i hi
  rw [← dist_centre_sq, hd] at h₁
  norm_num at h₁

theorem keyK_qq {z : ℝ × ℝ} (hz : Ok a b c z) (hf : Free a b z) :
    keyK (qq a b c z) = ((pl z : EuclideanPlane) : OnePoint EuclideanPlane) := by
  rw [qq_of_ok hz]
  exact ite_eq_right (notMem_glued hf)

theorem eq_of_free {z z' : ℝ × ℝ} (hz : Ok a b c z) (hf : Free a b z) (hz' : Ok a b c z')
    (hf' : Free a b z') (h : qq a b c z = qq a b c z') : z = z' := by
  have h₁ := congrArg keyK h
  rw [keyK_qq hz hf, keyK_qq hz' hf'] at h₁
  exact pl_injective (OnePoint.coe_injective h₁)

theorem base_eq {z : ℝ × ℝ} (hz : Ok a b c z) (hf : Free a b z)
    {x : modelBase (2 * a + b + c)} (h : Quot.mk _ x = qq a b c z) :
    x.1 = ((pl z : EuclideanPlane) : OnePoint EuclideanPlane) := by
  have h₁ := congrArg keyK h
  rw [keyK_qq hz hf] at h₁
  change kap a b x.1 = _ at h₁
  unfold kap at h₁
  split_ifs at h₁ with h₂
  · exact absurd h₁ (OnePoint.infty_ne_coe _)
  · exact h₁

/-- A complex number as a point of the plane. -/
def cp (ζ : ℂ) : ℝ × ℝ := (ζ.re, ζ.im)

/-- The domain of a chart. -/
def chartDom (a b c : ℕ) (B : Set ℂ) : Set ℂ := B ∩ {ζ | Ok a b c (cp ζ)}

/-- A chart of the model. -/
noncomputable def chart (a b c : ℕ) (B : Set ℂ) : chartDom a b c B → SurfaceModel a b c :=
  fun ζ ↦ qq a b c (cp ζ.1)

theorem continuous_cp : Continuous cp := by
  unfold cp
  fun_prop

theorem cp_injective : Function.Injective cp := fun ζ ζ' h ↦ by
  obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp h
  exact Complex.ext h₁ h₂

/-- A chart off the pasted circles is an open embedding. -/
theorem isOpenEmbedding_chart {B : Set ℂ} (hB : IsOpen B)
    (hf : ∀ ζ ∈ B, Ok a b c (cp ζ) → Free a b (cp ζ)) : IsOpenEmbedding (chart a b c B) := by
  refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuousOn_qq.comp_continuous (continuous_cp.comp continuous_subtype_val)
      fun ζ ↦ ζ.2.2
  · intro ζ ζ' h
    exact Subtype.ext (cp_injective (eq_of_free ζ.2.2 (hf _ ζ.2.1 ζ.2.2) ζ'.2.2
      (hf _ ζ'.2.1 ζ'.2.2) h))
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := isOpen_induced_iff.mp hA
    let ip : EuclideanPlane → ℂ := fun v ↦ (v 0 : ℂ) + (v 1 : ℂ) * Complex.I
    have hip : Continuous ip := by
      simp only [ip]
      fun_prop
    have hre : ∀ v, (ip v).re = v 0 := fun v ↦ by simp [ip]
    have him : ∀ v, (ip v).im = v 1 := fun v ↦ by simp [ip]
    have hpl : ∀ v, pl (cp (ip v)) = v := fun v ↦ by
      ext j
      fin_cases j
      · simp [pl, cp, hre]
      · simp [pl, cp, him]
    have hip' : ∀ ζ, ip (pl (cp ζ)) = ζ := fun ζ ↦ cp_injective (by
      apply pl_injective
      exact hpl _)
    let P : Set EuclideanPlane := ip ⁻¹' (A' ∩ B)
    have hP : IsOpen P := (hA'.inter hB).preimage hip
    have hO : IsOpen ((↑) '' P : Set (OnePoint EuclideanPlane)) :=
      OnePoint.isOpenEmbedding_coe.isOpenMap _ hP
    have hset : Quot.mk (ModelGlue a b (2 * a + b + c)) ⁻¹'
        (chart a b c B '' (Subtype.val ⁻¹' A')) = Subtype.val ⁻¹' ((↑) '' P) := by
      ext x
      constructor
      · rintro ⟨ζ, hζ, heq⟩
        have h₁ := base_eq ζ.2.2 (hf _ ζ.2.1 ζ.2.2) heq.symm
        refine ⟨pl (cp ζ.1), ?_, h₁.symm⟩
        change ip (pl (cp ζ.1)) ∈ A' ∩ B
        rw [hip']
        exact ⟨hζ, ζ.2.1⟩
      · rintro ⟨v, hv, hxv⟩
        have hok : Ok a b c (cp (ip v)) := fun i hi ↦ by
          have h₁ := x.2 i hi v hxv.symm
          have h₂ := dist_centre_sq (cp (ip v)) i
          rw [hpl] at h₂
          rw [← h₂]
          nlinarith
        refine ⟨⟨ip v, hv.2, hok⟩, hv.1, ?_⟩
        change qq a b c (cp (ip v)) = Quot.mk _ x
        rw [qq_of_ok hok]
        refine congrArg _ (Subtype.ext ?_)
        change ((pl (cp (ip v)) : EuclideanPlane) : OnePoint EuclideanPlane) = x.1
        rw [hpl, hxv]
    have h₂ : IsOpen (Quot.mk (ModelGlue a b (2 * a + b + c)) ⁻¹'
        (chart a b c B '' (Subtype.val ⁻¹' A'))) := by
      rw [hset]
      exact hO.preimage continuous_subtype_val
    exact h₂

/-- A point of a chart domain that is not interior in the plane is not an interior point. -/
theorem not_interior_of_chart {X : Type*} [TopologicalSpace X] {W : Set ℂ} {j : W → X}
    (hj : IsOpenEmbedding j) (w₀ : W) (hw : w₀.1 ∉ interior W) : ¬ IsInteriorPoint (j w₀) := by
  rintro ⟨U, hU, hxU, ⟨f⟩⟩
  let Y : Set W := j ⁻¹' U
  have h₁ : IsOpenEmbedding (U.restrictPreimage j) := hj.restrictPreimage U
  let φ : Y → ℂ := fun y ↦ complexPlane.symm (f (U.restrictPreimage j y)).1
  have hφ : IsOpenEmbedding φ :=
    complexPlane.symm.toHomeomorph.isOpenEmbedding.comp
      ((isOpen_ball.isOpenEmbedding_subtypeVal).comp (f.isOpenEmbedding.comp h₁))
  have : Nonempty Y := ⟨⟨w₀, hxU⟩⟩
  let Φ := hφ.toOpenPartialHomeomorph φ
  let k : ℂ → ℂ := fun ζ ↦ (Φ.symm ζ).1.1
  have hkc : ContinuousOn k Φ.target :=
    (continuous_subtype_val.comp continuous_subtype_val).comp_continuousOn Φ.continuousOn_symm
  have hki : InjOn k Φ.target := fun ζ hζ ζ' hζ' h ↦
    Φ.symm.injOn hζ hζ' (Subtype.ext (Subtype.ext h))
  have hopen := isOpen_image_of_injOn Φ.open_target hkc hki
  have hmem : w₀.1 ∈ k '' Φ.target := by
    refine ⟨φ ⟨w₀, hxU⟩, ?_, ?_⟩
    · exact Φ.map_source (mem_univ _ : _ ∈ Φ.source)
    · simp only [k]
      rw [show Φ.symm (φ ⟨w₀, hxU⟩) = ⟨w₀, hxU⟩ from
        Φ.left_inv (mem_univ _ : _ ∈ Φ.source)]
  have hsub : k '' Φ.target ⊆ W := by
    rintro _ ⟨ζ, _, rfl⟩
    exact (Φ.symm ζ).1.2
  exact hw (mem_interior.mpr ⟨_, hsub, hopen, hmem⟩)

theorem interior_of_chart {X : Type*} [TopologicalSpace X] {W : Set ℂ} {j : W → X}
    (hj : IsOpenEmbedding j) (he : Nonempty (W ≃ₜ OpenUnitDisc)) (w₀ : W) :
    IsInteriorPoint (j w₀) := by
  obtain ⟨e⟩ := he
  exact ⟨range j, hj.isOpen_range, mem_range_self _,
    ⟨(hj.isEmbedding.toHomeomorph).symm.trans e⟩⟩

/-- An open ball of the complex plane is homeomorphic to the open unit disc. -/
noncomputable def ballHomeo (ζ₀ : ℂ) {r : ℝ} (hr : 0 < r) : ball ζ₀ r ≃ₜ OpenUnitDisc where
  toFun ζ := ⟨complexPlane (((r⁻¹ : ℝ) : ℂ) * (ζ.1 - ζ₀)), by
    refine mem_ball_zero_iff.mpr ?_
    rw [LinearIsometryEquiv.norm_map, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    have h₁ : ‖ζ.1 - ζ₀‖ < r := by
      have h₂ := ζ.2
      rwa [mem_ball, dist_eq_norm] at h₂
    rw [inv_mul_lt_iff₀ hr]
    linarith⟩
  invFun v := ⟨ζ₀ + (r : ℂ) * complexPlane.symm v.1, by
    have h₁ : ‖v.1‖ < 1 := mem_ball_zero_iff.mp v.2
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, LinearIsometryEquiv.norm_map]
    nlinarith⟩
  left_inv ζ := by
    apply Subtype.ext
    have h₁ : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [LinearIsometryEquiv.symm_apply_apply]
    push_cast
    field_simp
    ring
  right_inv v := by
    apply Subtype.ext
    have h₁ : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [add_sub_cancel_left]
    push_cast
    rw [inv_mul_cancel_left₀ h₁]
    simp
  continuous_toFun := by
    refine Continuous.subtype_mk (complexPlane.continuous.comp ?_) _
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    have := complexPlane.symm.continuous
    fun_prop

end GraphMinor.GM20.Draw
