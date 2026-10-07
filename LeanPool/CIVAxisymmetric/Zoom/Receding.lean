/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Identities.PotentialVorticity
public import LeanPool.CIVAxisymmetric.Identities.ScalarSystemDiv
public import LeanPool.CIVAxisymmetric.Zoom.ChainRule
public import LeanPool.CIVAxisymmetric.Zoom.ChainRuleSecond
public import LeanPool.CIVAxisymmetric.Zoom.Exponents
public import LeanPool.CIVAxisymmetric.Zoom.ScalarChainRule

/-!
# The receding-axis zoom

The recentred zoom-in map of `eq:aniso:zoom:receding:variables` sends `((R, Z), τ)` to the
point with radius `rc + lam * R`, height `zc + lam ^ (1 - 2 * h) * Z` and parabolic time
`lam ^ 2 * τ`. Only the radial slot differs from `eq:aniso:zoom:finite:variables`, and it
differs by the *constant* offset `rc`, so every derivative in the recentred variables has
exactly the same prefactor as in the finite-axis variables.

The file follows `CIV.Zoom.Rescaling`, `CIV.Zoom.ChainRule`, `CIV.Zoom.ChainRuleSecond`,
`CIV.Zoom.DivergenceIdentity` and `CIV.Zoom.RescaledBounds` step by step; the receding
declarations carry a `Rec` suffix so that the two families never clash. The
second-derivative helpers are obtained from the general scalar chain rule of
`CIV.Zoom.ScalarChainRule`, which is stated for an arbitrary curve inside a fixed time
slice and therefore accepts the offset radial line of the recentred map.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The recentred zoom map and the rescaled fields -/

/-- The recentred zoom-in map of `eq:aniso:zoom:receding:variables`, with the radial offset
`rc` and the vertical offset `zc`. -/
@[expose] def zoomPointRec (lam h rc zc : ℝ) (p : (ℝ × ℝ) × ℝ) : ParabolicPoint :=
  (meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2), lam ^ 2 * p.2)

/-- `V_n` of `eq:aniso:zoom:fields` in the recentred variables. -/
@[expose] def zoomVRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam * u (zoomPointRec lam h rc zc p) 0

/-- `W_n` of `eq:aniso:zoom:fields` in the recentred variables. -/
@[expose] def zoomWRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc p) 2

/-- `S_n` of `eq:aniso:zoom:fields` in the recentred variables. -/
@[expose] def zoomSRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc p) 1

/-- The rescaled azimuthal vorticity `Θ_n = lam² δ_n ω_θ` of
`eq:aniso:zoom:receding:vorticity`. -/
@[expose] def zoomTheta (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam ^ 2 * lam ^ (2 * h) * azimuthalVorticity u (zoomPointRec lam h rc zc p)

/-! ### Membership, continuity and smoothness of the recentred zoom map -/

/-- Membership of the recentred zoom point in the unit cylinder, read off in coordinates.
The time slot is `lam ^ 2 * p.2` with `p.2 = τ < 0`, exactly as in
`zoomPoint_mem_unitCylinder_iff`. -/
theorem zoomPointRec_mem_unitCylinder_iff (lam h rc zc : ℝ) (p : (ℝ × ℝ) × ℝ) :
    zoomPointRec lam h rc zc p ∈ unitCylinder ↔
      (rc + lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2 < 1 ∧
        lam ^ 2 * p.2 ∈ Ioo (-1 : ℝ) 0 := by
  constructor
  · intro hmem
    rcases hmem with ⟨hball, htime⟩
    have hball_norm :
        vec3EuclideanNorm
            (meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)) < 1 := by
      simpa [unitCylinder, spaceTimeSet, zoomPointRec, mem_vec3Ball, sub_zero] using hball
    have hsum :
        vec3EuclideanNorm (meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)) =
          Real.sqrt ((rc + lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2) := by
      rw [vec3EuclideanNorm]
      simp [meridional, Fin.sum_univ_three]
    rw [hsum] at hball_norm
    have hsq : (rc + lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2 < 1 := by
      have htemp := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mp hball_norm
      simpa [sq] using htemp
    exact ⟨hsq, htime⟩
  · intro ⟨hsq, htime⟩
    have hball_norm :
        Real.sqrt ((rc + lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2) < 1 := by
      apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
      simpa [sq] using hsq
    have hsum :
        vec3EuclideanNorm (meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)) =
          Real.sqrt ((rc + lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2) := by
      rw [vec3EuclideanNorm]
      simp [meridional, Fin.sum_univ_three]
    have hball_norm' :
        vec3EuclideanNorm
            (meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)) < 1 := by
      rw [hsum]
      exact hball_norm
    have hball : meridional (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)
        ∈ vec3Ball (0 : Vec3) 1 := by
      rwa [mem_vec3Ball, sub_zero]
    have hunit : zoomPointRec lam h rc zc p ∈ unitCylinder := by
      rw [unitCylinder, spaceTimeSet, zoomPointRec]
      exact Set.mem_prod.mpr ⟨hball, htime⟩
    exact hunit

/-- `zoomPointRec` is affine in `p`, hence continuous. As in `continuous_zoomPoint`, the
codomain is named `Y := Vec3 × ℝ` so that the product topology, not the parabolic metric of
`ParabolicPoint`, is the one used (design note R2). -/
theorem continuous_zoomPointRec (lam h rc zc : ℝ) :
    Continuous (Y := Vec3 × ℝ) (fun p : (ℝ × ℝ) × ℝ => zoomPointRec lam h rc zc p) := by
  unfold zoomPointRec
  apply Continuous.prodMk
  · refine continuous_pi ?_
    intro i
    fin_cases i
    · simp only [meridional]
      exact Continuous.add continuous_const
        (Continuous.mul continuous_const (continuous_fst.comp continuous_fst))
    · simp only [meridional]
      exact continuous_const
    · simp only [meridional]
      refine Continuous.add continuous_const ?_
      exact Continuous.mul continuous_const (continuous_snd.comp continuous_fst)
  · exact Continuous.mul continuous_const continuous_snd

/-- `zoomPointRec` is affine, hence smooth; the codomain is named `F := Vec3 × ℝ` for the
same reason as in `continuous_zoomPointRec`. -/
theorem contDiff_zoomPointRec (lam h rc zc : ℝ) :
    ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => zoomPointRec lam h rc zc p) := by
  unfold zoomPointRec
  apply ContDiff.prodMk
  · have hx : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => rc + lam * p.1.1) :=
      ContDiff.add contDiff_const
        (ContDiff.mul contDiff_const (contDiff_fst.comp contDiff_fst))
    have hz : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => zc + lam ^ (1 - 2 * h) * p.1.2) :=
      ContDiff.add contDiff_const
        (ContDiff.mul contDiff_const (contDiff_snd.comp contDiff_fst))
    refine (contDiff_pi (ι := Fin 3)).2 ?_
    intro i
    fin_cases i
    · simpa [meridional] using hx
    · simpa [meridional] using contDiff_const
    · simpa [meridional] using hz
  · exact ContDiff.mul contDiff_const contDiff_snd

/-! ### Derivatives of the recentred meridional line -/

/-- Moving the radial coordinate of a meridional point away from the offset `b` at speed `a`
moves it along `e₁`. -/
theorem hasDerivAt_meridional_fst_shift (b a c x : ℝ) :
    HasDerivAt (fun s : ℝ => meridional (b + a * s) c) (a • basisVec 0) x := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [meridional, basisVec_apply] using ((hasDerivAt_id x).const_mul a).const_add b
  · simpa [meridional, basisVec_apply] using hasDerivAt_const x (0 : ℝ)
  · simpa [meridional, basisVec_apply] using hasDerivAt_const x c

/-! ### The recentred zoom map differentiated in `R` and in `Z` -/

/-- Differentiating a component of `u ∘ zoomPointRec` in the radial variable. -/
theorem hasDerivAt_zoomRec_component_r (lam h rc zc : ℝ) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => u (zoomPointRec lam h rc zc ((r, p.1.2), p.2)) i)
      (lam * spatialPartial (fun w => u w i) 0 (zoomPointRec lam h rc zc p)) p.1.1 :=
  hasDerivAt_comp_spatialSlice hu hp
    (hasDerivAt_meridional_fst_shift rc lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1) rfl i

/-- Differentiating a component of `u ∘ zoomPointRec` in the vertical variable. -/
theorem hasDerivAt_zoomRec_component_z (lam h rc zc : ℝ) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => u (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) i)
      (lam ^ (1 - 2 * h) * spatialPartial (fun w => u w i) 2 (zoomPointRec lam h rc zc p))
      p.1.2 :=
  hasDerivAt_comp_spatialSlice hu hp
    (hasDerivAt_meridional_snd (rc + lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl i

/-! ### First-order chain rules for the recentred fields -/

/-- `∂_R V_n` in terms of the radial partial derivative of `u_r`. -/
theorem dr_zoomVRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (zoomVRec lam h rc zc u) p
      = lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPointRec lam h rc zc p) := by
  have hbase := (hasDerivAt_zoomRec_component_r lam h rc zc hu p hp 0).const_mul lam
  have heq : lam * (lam * spatialPartial (fun w => u w 0) 0 (zoomPointRec lam h rc zc p))
      = lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPointRec lam h rc zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_Z V_n` in terms of the vertical partial derivative of `u_r`. -/
theorem dz_zoomVRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (zoomVRec lam h rc zc u) p
      = lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc p) := by
  have hbase := (hasDerivAt_zoomRec_component_z lam h rc zc hu p hp 0).const_mul lam
  have heq : lam * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc p))
      = lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_R W_n` in terms of the radial partial derivative of `u_z`. -/
theorem dr_zoomWRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (zoomWRec lam h rc zc u) p
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc p) := by
  have hbase :=
    (hasDerivAt_zoomRec_component_r lam h rc zc hu p hp 2).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) *
        (lam * spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc p))
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_Z W_n` in terms of the vertical partial derivative of `u_z`. -/
theorem dz_zoomWRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (zoomWRec lam h rc zc u) p
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc p) := by
  have hbase :=
    (hasDerivAt_zoomRec_component_z lam h rc zc hu p hp 2).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc p))
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_R S_n` in terms of the radial partial derivative of `u_θ`. -/
theorem dr_zoomSRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (zoomSRec lam h rc zc u) p
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 0 (zoomPointRec lam h rc zc p) := by
  have hbase :=
    (hasDerivAt_zoomRec_component_r lam h rc zc hu p hp 1).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) *
        (lam * spatialPartial (fun w => u w 1) 0 (zoomPointRec lam h rc zc p))
      = lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 0 (zoomPointRec lam h rc zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-- `∂_Z S_n` in terms of the vertical partial derivative of `u_θ`. -/
theorem dz_zoomSRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (zoomSRec lam h rc zc u) p
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPointRec lam h rc zc p) := by
  have hbase :=
    (hasDerivAt_zoomRec_component_z lam h rc zc hu p hp 1).const_mul (lam * lam ^ (2 * h))
  have heq : lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPointRec lam h rc zc p))
      = lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPointRec lam h rc zc p) := by ring
  rw [heq] at hbase
  exact hbase.deriv

/-! ### Open-neighbourhood lemmas for the recentred zoom -/

theorem isOpen_zoomPointRec_preimage (lam h rc zc : ℝ) :
    IsOpen {q : (ℝ × ℝ) × ℝ | zoomPointRec lam h rc zc q ∈ unitCylinder} :=
  isOpen_unitCylinder_prod.preimage (continuous_zoomPointRec lam h rc zc)

theorem isOpen_slice_r_rec (lam h rc zc : ℝ) (p : (ℝ × ℝ) × ℝ) :
    IsOpen {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} := by
  have h_cont : Continuous (fun r : ℝ => ((r, p.1.2), p.2)) :=
    (Continuous.prodMk continuous_id continuous_const).prodMk continuous_const
  exact (isOpen_zoomPointRec_preimage lam h rc zc).preimage h_cont

theorem isOpen_slice_z_rec (lam h rc zc : ℝ) (p : (ℝ × ℝ) × ℝ) :
    IsOpen {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} := by
  have h_cont : Continuous (fun s : ℝ => ((p.1.1, s), p.2)) :=
    (Continuous.prodMk continuous_const continuous_id).prodMk continuous_const
  exact (isOpen_zoomPointRec_preimage lam h rc zc).preimage h_cont

/-- A first-order identity valid at every recentred zoom point of the unit cylinder holds on a
whole neighbourhood of `p.1.1` inside the radial slice through `p`. -/
theorem eventuallyEq_slice_r_rec (lam h rc zc : ℝ) (φ : (ℝ × ℝ) × ℝ → ℝ)
    (ψ : ParabolicPoint → ℝ) (K : ℝ) (p : (ℝ × ℝ) × ℝ)
    (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hφ : ∀ q : (ℝ × ℝ) × ℝ, zoomPointRec lam h rc zc q ∈ unitCylinder →
      φ q = K * ψ (zoomPointRec lam h rc zc q)) :
    (fun r : ℝ => φ ((r, p.1.2), p.2)) =ᶠ[𝓝 p.1.1]
      fun r : ℝ => K * ψ (zoomPointRec lam h rc zc ((r, p.1.2), p.2)) := by
  have hS_open : IsOpen {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} :=
    isOpen_slice_r_rec lam h rc zc p
  have hpS : p.1.1 ∈ {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
  filter_upwards [hS_open.mem_nhds hpS] with r hr
  exact hφ ((r, p.1.2), p.2) hr

/-- The vertical counterpart of `eventuallyEq_slice_r_rec`. -/
theorem eventuallyEq_slice_z_rec (lam h rc zc : ℝ) (φ : (ℝ × ℝ) × ℝ → ℝ)
    (ψ : ParabolicPoint → ℝ) (K : ℝ) (p : (ℝ × ℝ) × ℝ)
    (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hφ : ∀ q : (ℝ × ℝ) × ℝ, zoomPointRec lam h rc zc q ∈ unitCylinder →
      φ q = K * ψ (zoomPointRec lam h rc zc q)) :
    (fun s : ℝ => φ ((p.1.1, s), p.2)) =ᶠ[𝓝 p.1.2]
      fun s : ℝ => K * ψ (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) := by
  have hS_open : IsOpen {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} :=
    isOpen_slice_z_rec lam h rc zc p
  have hpS : p.1.2 ∈ {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} := hp
  filter_upwards [hS_open.mem_nhds hpS] with s hs
  exact hφ ((p.1.1, s), p.2) hs

/-! ### Second-derivative helpers for the recentred zoom -/

/-- The `R`-derivative of `spatialPartial (u· i) 0` composed with `zoomPointRec`. -/
theorem hasDerivAt_spatialPartial_zero_zoomRec_r (lam h rc zc : ℝ)
    (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ =>
      spatialPartial (fun w => u w i) 0 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam * meridionalPartial (fun w => u w i) 2 0 (zoomPointRec lam h rc zc p)) p.1.1 := by
  have hpar : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w i) 0 z) unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu i) 0
  exact hasDerivAt_comp_spatialSlice_scalar isOpen_unitCylinder_prod hpar hp
    (hasDerivAt_meridional_fst_shift rc lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1) rfl

/-- The `R`-derivative of `spatialPartial (u· i) 2` composed with `zoomPointRec`. -/
theorem hasDerivAt_spatialPartial_two_zoomRec_r (lam h rc zc : ℝ)
    (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ =>
      spatialPartial (fun w => u w i) 2 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam * meridionalPartial (fun w => u w i) 1 1 (zoomPointRec lam h rc zc p)) p.1.1 := by
  have hpar : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w i) 2 z) unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu i) 2
  exact hasDerivAt_comp_spatialSlice_scalar isOpen_unitCylinder_prod hpar hp
    (hasDerivAt_meridional_fst_shift rc lam (zc + lam ^ (1 - 2 * h) * p.1.2) p.1.1) rfl

/-- The `Z`-derivative of `spatialPartial (u· i) 2` composed with `zoomPointRec`. -/
theorem hasDerivAt_spatialPartial_two_zoomRec_z (lam h rc zc : ℝ)
    (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ =>
      spatialPartial (fun w => u w i) 2 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w i) 0 2 (zoomPointRec lam h rc zc p))
      p.1.2 := by
  have hpar : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w i) 2 z) unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu i) 2
  exact hasDerivAt_comp_spatialSlice_scalar isOpen_unitCylinder_prod hpar hp
    (hasDerivAt_meridional_snd (rc + lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl

/-! ### Second-order chain rules for the recentred fields -/

theorem drdr_zoomVRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (dr (zoomVRec lam h rc zc u)) p
      = lam ^ 3 * meridionalPartial (fun w => u w 0) 2 0 (zoomPointRec lam h rc zc p) := by
  rw [dr]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dr (zoomVRec lam h rc zc u))
    (spatialPartial (fun w => u w 0) 0) (lam ^ 2) p hp
    (fun q hq => dr_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 *
        spatialPartial (fun w => u w 0) 0 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam ^ 3 * meridionalPartial (fun w => u w 0) 2 0 (zoomPointRec lam h rc zc p))
      p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_zero_zoomRec_r lam h rc zc u 0 hu p hp
    have h_mul := h_inner.const_mul (lam ^ 2)
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem drdz_zoomVRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (dz (zoomVRec lam h rc zc u)) p
      = lam ^ 2 * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 0) 1 1 (zoomPointRec lam h rc zc p) := by
  rw [dr]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dz (zoomVRec lam h rc zc u))
    (spatialPartial (fun w => u w 0) 2) (lam * lam ^ (1 - 2 * h)) p hp
    (fun q hq => dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam ^ 2 * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 0) 1 1 (zoomPointRec lam h rc zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoomRec_r lam h rc zc u 0 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem dzdz_zoomVRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (dz (zoomVRec lam h rc zc u)) p
      = lam * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 0) 0 2 (zoomPointRec lam h rc zc p) := by
  rw [dz]
  have h_event := eventuallyEq_slice_z_rec lam h rc zc (dz (zoomVRec lam h rc zc u))
    (spatialPartial (fun w => u w 0) 2) (lam * lam ^ (1 - 2 * h)) p hp
    (fun q hq => dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) *
        spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 0) 0 2 (zoomPointRec lam h rc zc p)) p.1.2 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoomRec_z lam h rc zc u 0 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem drdr_zoomWRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (dr (zoomWRec lam h rc zc u)) p
      = lam ^ 3 * lam ^ (2 * h) *
        meridionalPartial (fun w => u w 2) 2 0 (zoomPointRec lam h rc zc p) := by
  rw [dr]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dr (zoomWRec lam h rc zc u))
    (spatialPartial (fun w => u w 2) 0) (lam ^ 2 * lam ^ (2 * h)) p hp
    (fun q hq => dr_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam ^ 3 * lam ^ (2 * h) *
        meridionalPartial (fun w => u w 2) 2 0 (zoomPointRec lam h rc zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_zero_zoomRec_r lam h rc zc u 2 hu p hp
    have h_mul := h_inner.const_mul (lam ^ 2 * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem drdz_zoomWRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (dz (zoomWRec lam h rc zc u)) p
      = lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 2) 1 1 (zoomPointRec lam h rc zc p) := by
  rw [dr]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dz (zoomWRec lam h rc zc u))
    (spatialPartial (fun w => u w 2) 2) (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h)) p hp
    (fun q hq => dz_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 2) 1 1 (zoomPointRec lam h rc zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoomRec_r lam h rc zc u 2 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem dzdz_zoomWRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (dz (zoomWRec lam h rc zc u)) p
      = lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 2) 0 2 (zoomPointRec lam h rc zc p) := by
  rw [dz]
  have h_event := eventuallyEq_slice_z_rec lam h rc zc (dz (zoomWRec lam h rc zc u))
    (spatialPartial (fun w => u w 2) 2) (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h)) p hp
    (fun q hq => dz_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 2) 0 2 (zoomPointRec lam h rc zc p)) p.1.2 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoomRec_z lam h rc zc u 2 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem drdr_zoomSRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (dr (zoomSRec lam h rc zc u)) p
      = lam ^ 3 * lam ^ (2 * h) *
        meridionalPartial (fun w => u w 1) 2 0 (zoomPointRec lam h rc zc p) := by
  rw [dr]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dr (zoomSRec lam h rc zc u))
    (spatialPartial (fun w => u w 1) 0) (lam ^ 2 * lam ^ (2 * h)) p hp
    (fun q hq => dr_zoomSRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam ^ 2 * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 0 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam ^ 3 * lam ^ (2 * h) *
        meridionalPartial (fun w => u w 1) 2 0 (zoomPointRec lam h rc zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_zero_zoomRec_r lam h rc zc u 1 hu p hp
    have h_mul := h_inner.const_mul (lam ^ 2 * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem drdz_zoomSRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (dz (zoomSRec lam h rc zc u)) p
      = lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 1) 1 1 (zoomPointRec lam h rc zc p) := by
  rw [dr]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dz (zoomSRec lam h rc zc u))
    (spatialPartial (fun w => u w 1) 2) (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h)) p hp
    (fun q hq => dz_zoomSRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun r : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPointRec lam h rc zc ((r, p.1.2), p.2)))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 1) 1 1 (zoomPointRec lam h rc zc p)) p.1.1 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoomRec_r lam h rc zc u 1 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

theorem dzdz_zoomSRec (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (dz (zoomSRec lam h rc zc u)) p
      = lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 1) 0 2 (zoomPointRec lam h rc zc p) := by
  rw [dz]
  have h_event := eventuallyEq_slice_z_rec lam h rc zc (dz (zoomSRec lam h rc zc u))
    (spatialPartial (fun w => u w 1) 2) (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h)) p hp
    (fun q hq => dz_zoomSRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_deriv_rhs : HasDerivAt (fun s : ℝ =>
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) *
        spatialPartial (fun w => u w 1) 2 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ 2 *
        meridionalPartial (fun w => u w 1) 0 2 (zoomPointRec lam h rc zc p)) p.1.2 := by
    have h_inner := hasDerivAt_spatialPartial_two_zoomRec_z lam h rc zc u 1 hu p hp
    have h_mul := h_inner.const_mul (lam * lam ^ (1 - 2 * h) * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact (h_deriv_rhs.congr_of_eventuallyEq h_event).deriv

/-! ### The rescaled azimuthal vorticity -/

/-- `eq:aniso:zoom:receding:vorticity`: the rescaled azimuthal vorticity is
`Θ_n = δ_n² ∂_Z V_n - ∂_R W_n`, with `δ_n = lam ^ (2 * h)`. -/
theorem zoomTheta_eq (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    zoomTheta lam h rc zc u p
      = (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) p
        - dr (zoomWRec lam h rc zc u) p := by
  have hd : lam = lam ^ (2 * h) * lam ^ (1 - 2 * h) := zoom_lambda_eq_delta_mul_mu hlam
  have hkey : (lam ^ (2 * h)) ^ 2 * (lam * lam ^ (1 - 2 * h)) = lam ^ 2 * lam ^ (2 * h) := by
    calc (lam ^ (2 * h)) ^ 2 * (lam * lam ^ (1 - 2 * h))
        = lam ^ (2 * h) * lam * (lam ^ (2 * h) * lam ^ (1 - 2 * h)) := by ring
      _ = lam ^ (2 * h) * lam * lam := by rw [← hd]
      _ = lam ^ 2 * lam ^ (2 * h) := by ring
  rw [dz_zoomVRec lam h rc zc u hu p hp, dr_zoomWRec lam h rc zc u hu p hp]
  unfold zoomTheta
  rw [azimuthalVorticity, curlComp_one]
  linear_combination
    (-(spatialPartial (fun w => u w 0) 2 (zoomPointRec lam h rc zc p))) * hkey

/-! ### The recentred divergence identity -/

/-- Off the receding axis, the recentred radial velocity divided by `A + R` equals `lam²`
times the meridional radial quotient at the recentred zoom point, with `A = rc / lam`. -/
theorem zoomVRec_div_eq (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (p : (ℝ × ℝ) × ℝ) (hR : p.1.1 ≠ -(rc / lam)) :
    zoomVRec lam h rc zc u p / (rc / lam + p.1.1)
      = lam ^ 2 *
        (u (zoomPointRec lam h rc zc p) 0 / (zoomPointRec lam h rc zc p).1 0) := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hA : rc / lam + p.1.1 ≠ 0 := by
    intro hcontra
    exact hR (by linarith only [hcontra])
  have hz0 : (zoomPointRec lam h rc zc p).1 0 = rc + lam * p.1.1 := by
    simp [zoomPointRec, meridional]
  have heq : rc + lam * p.1.1 = lam * (rc / lam + p.1.1) := by
    field_simp
  unfold zoomVRec
  rw [hz0, heq]
  field_simp

/-- `eq:aniso:zoom:receding:div`: in the recentred variables the divergence-free condition
reads `∂_R V_n + V_n / (A + R) + ∂_Z W_n = 0`, with `A = rc / lam`, at every point with
`R ≠ -A`. -/
theorem zoomRec_divergence_identity (lam h rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pr f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder)
    (hR : p.1.1 ≠ -(rc / lam)) :
    dr (zoomVRec lam h rc zc u) p + zoomVRec lam h rc zc u p / (rc / lam + p.1.1)
      + dz (zoomWRec lam h rc zc u) p = 0 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by exact_mod_cast le_top)
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hA : rc / lam + p.1.1 ≠ 0 := by
    intro hcontra
    exact hR (by linarith only [hcontra])
  have hz0 : (zoomPointRec lam h rc zc p).1 0 = rc + lam * p.1.1 := by
    simp [zoomPointRec, meridional]
  have hplane : (zoomPointRec lam h rc zc p).1 1 = 0 := by
    simp [zoomPointRec, meridional]
  have heq : rc + lam * p.1.1 = lam * (rc / lam + p.1.1) := by
    field_simp
  have hr_zoom : (zoomPointRec lam h rc zc p).1 0 ≠ 0 := by
    rw [hz0, heq]
    exact mul_ne_zero hlam_ne hA
  have h_exp : lam * lam ^ (1 - 2 * h) * lam ^ (2 * h) = lam ^ 2 := by
    calc
      lam * lam ^ (1 - 2 * h) * lam ^ (2 * h)
          = lam * (lam ^ (1 - 2 * h) * lam ^ (2 * h)) := by ring
      _ = lam * lam ^ ((1 - 2 * h) + (2 * h)) := by
        rw [← Real.rpow_add hlam (1 - 2 * h) (2 * h)]
      _ = lam * lam ^ (1 : ℝ) := by
        have h_exp_simp : (1 - 2 * h) + (2 * h) = (1 : ℝ) := by ring
        rw [h_exp_simp]
      _ = lam * lam := by simp
      _ = lam ^ 2 := by ring
  rw [dr_zoomVRec lam h rc zc u hu1 p hp, dz_zoomWRec lam h rc zc u hu1 p hp,
    zoomVRec_div_eq lam h rc zc hlam u p hR]
  rw [hz0, h_exp]
  have h_scalar :=
    scalar_nse_div u pr f hsol haxi (zoomPointRec lam h rc zc p) hp hplane hr_zoom
  rw [hz0] at h_scalar
  calc
    lam ^ 2 * spatialPartial (fun w => u w 0) 0 (zoomPointRec lam h rc zc p)
        + lam ^ 2 * (u (zoomPointRec lam h rc zc p) 0 / (rc + lam * p.1.1))
        + lam ^ 2 * spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc p)
        = lam ^ 2 * (spatialPartial (fun w => u w 0) 0 (zoomPointRec lam h rc zc p)
            + u (zoomPointRec lam h rc zc p) 0 / (rc + lam * p.1.1)
            + spatialPartial (fun w => u w 2) 2 (zoomPointRec lam h rc zc p)) := by ring
    _ = lam ^ 2 * 0 := by rw [h_scalar]
    _ = 0 := by ring

/-! ### The anisotropic bounds in the recentred variables (`eq:aniso:zoom:derivatives`) -/

/-- Scale invariance of the radial anisotropic bound in the recentred variables. If `F` is the
`lam`-prefactored meridional derivative `∂₁^a ∂₃^b u_r` evaluated at the recentred zoom point,
then `F` obeys the anisotropic bound of order `(a, b)` in the rescaled time `p.2`. -/
private theorem abs_zoomVRec_prefactor_le {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) (a b : ℕ) (hab : a + b ≤ 2)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (F e : ℝ)
    (hF : F = lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 0) a b (zoomPointRec lam h rc zc p))
    (he : e = -(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) :
    |F| ≤ C * (-p.2) ^ e := by
  subst hF
  subst he
  have hlamsq : (0 : ℝ) < lam ^ 2 := by positivity
  have htime : lam ^ 2 * p.2 < 0 :=
    ((zoomPointRec_mem_unitCylinder_iff lam h rc zc p).mp hp).2.2
  have htau : p.2 < 0 := by nlinarith only [htime, hlamsq]
  have hKnn : (0 : ℝ) ≤ lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b :=
    mul_nonneg (pow_nonneg hlam.le _) (pow_nonneg (Real.rpow_nonneg hlam.le _) _)
  have hbound :=
    (hb a b hab (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) (lam ^ 2 * p.2) hp).1
  rw [abs_mul, abs_of_nonneg hKnn]
  refine (mul_le_mul_of_nonneg_left hbound hKnn).trans_eq ?_
  have hneg : -(lam ^ 2 * p.2) = lam ^ 2 * (-p.2) := by ring
  rw [hneg]
  calc
    lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
        (C * (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)))
        = C * (lam ^ (1 + a) * (lam ^ (1 - 2 * h)) ^ b *
          (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ))) := by
      ring
    _ = C * (-p.2) ^ (-(1 / 2 : ℝ) - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) := by
      rw [zoom_rescaled_exponent hlam a b p.2 htau]

/-- Scale invariance of the joint vertical/swirl anisotropic bound in the recentred variables.
If `F` and `G` are the `lam`-prefactored meridional derivatives `∂₁^a ∂₃^b u_z` and
`∂₁^a ∂₃^b u_θ` evaluated at the recentred zoom point, then `|F| + |G|` obeys the anisotropic
bound of order `(a, b)` in the rescaled time `p.2`. -/
private theorem abs_zoomWSRec_prefactor_le {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) (a b : ℕ) (hab : a + b ≤ 2)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (F G e : ℝ)
    (hF : F = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 2) a b (zoomPointRec lam h rc zc p))
    (hG : G = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 1) a b (zoomPointRec lam h rc zc p))
    (he : e = -(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) :
    |F| + |G| ≤ C * (-p.2) ^ e := by
  subst hF
  subst hG
  subst he
  have hlamsq : (0 : ℝ) < lam ^ 2 := by positivity
  have htime : lam ^ 2 * p.2 < 0 :=
    ((zoomPointRec_mem_unitCylinder_iff lam h rc zc p).mp hp).2.2
  have htau : p.2 < 0 := by nlinarith only [htime, hlamsq]
  have hKnn : (0 : ℝ) ≤ lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b :=
    mul_nonneg (mul_nonneg (pow_nonneg hlam.le _) (Real.rpow_nonneg hlam.le _))
      (pow_nonneg (Real.rpow_nonneg hlam.le _) _)
  have hbound :=
    (hb a b hab (rc + lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) (lam ^ 2 * p.2) hp).2
  have habsW : |lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 2) a b (zoomPointRec lam h rc zc p)|
      = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        |meridionalPartial (fun z => u z 2) a b (zoomPointRec lam h rc zc p)| := by
    rw [abs_mul, abs_of_nonneg hKnn]
  have habsS : |lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
      meridionalPartial (fun z => u z 1) a b (zoomPointRec lam h rc zc p)|
      = lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        |meridionalPartial (fun z => u z 1) a b (zoomPointRec lam h rc zc p)| := by
    rw [abs_mul, abs_of_nonneg hKnn]
  rw [habsW, habsS, ← mul_add]
  refine (mul_le_mul_of_nonneg_left hbound hKnn).trans_eq ?_
  have hneg : -(lam ^ 2 * p.2) = lam ^ 2 * (-p.2) := by ring
  rw [hneg]
  calc
    lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
        (C * (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)))
        = C * (lam ^ (1 + a) * lam ^ (2 * h) * (lam ^ (1 - 2 * h)) ^ b *
          (lam ^ 2 * (-p.2)) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ))) := by
      ring
    _ = C * (-p.2) ^ (-(1 / 2 : ℝ) - h - (a : ℝ) / 2 - (1 / 2 - h) * (b : ℝ)) := by
      rw [zoom_rescaled_exponent_swirl hlam a b p.2 htau]

theorem abs_zoomVRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |zoomVRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomVRec_prefactor_le hlam hb 0 0 (by omega) p hp _ _ ?_ (by norm_num)
  simp only [meridionalPartial, Function.iterate_zero_apply]
  rw [zoomVRec]
  ring

theorem abs_dr_zoomVRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dr (zoomVRec lam h rc zc u) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomVRec_prefactor_le hlam hb 1 0 (by omega) p hp _ _ ?_ (by norm_num)
  rw [dr_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) p hp]
  simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
  ring

theorem abs_dz_zoomVRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dz (zoomVRec lam h rc zc u) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomVRec_prefactor_le hlam hb 0 1 (by omega) p hp _ _ ?_ (by norm_num)
  rw [dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) p hp]
  simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
  ring

theorem abs_drdr_zoomVRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dr (dr (zoomVRec lam h rc zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 2 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomVRec_prefactor_le hlam hb 2 0 (by omega) p hp _ _ ?_ (by norm_num)
  rw [drdr_zoomVRec lam h rc zc u hu p hp]
  ring

theorem abs_drdz_zoomVRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dr (dz (zoomVRec lam h rc zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 1 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomVRec_prefactor_le hlam hb 1 1 (by omega) p hp _ _ ?_ (by norm_num)
  rw [drdz_zoomVRec lam h rc zc u hu p hp]
  ring

theorem abs_dzdz_zoomVRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dz (dz (zoomVRec lam h rc zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 2) := by
  refine abs_zoomVRec_prefactor_le hlam hb 0 2 (by omega) p hp _ _ ?_ (by norm_num)
  rw [dzdz_zoomVRec lam h rc zc u hu p hp]
  ring

theorem abs_zoomWRec_add_abs_zoomSRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |zoomWRec lam h rc zc u p| + |zoomSRec lam h rc zc u p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomWSRec_prefactor_le hlam hb 0 0 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · simp only [meridionalPartial, Function.iterate_zero_apply]
    rw [zoomWRec]
    ring
  · simp only [meridionalPartial, Function.iterate_zero_apply]
    rw [zoomSRec]
    ring

theorem abs_dr_zoomWRec_add_abs_dr_zoomSRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dr (zoomWRec lam h rc zc u) p| + |dr (zoomSRec lam h rc zc u) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomWSRec_prefactor_le hlam hb 1 0 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [dr_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring
  · rw [dr_zoomSRec lam h rc zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring

theorem abs_dz_zoomWRec_add_abs_dz_zoomSRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dz (zoomWRec lam h rc zc u) p| + |dz (zoomSRec lam h rc zc u) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomWSRec_prefactor_le hlam hb 0 1 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [dz_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring
  · rw [dz_zoomSRec lam h rc zc u (hu.of_le (by norm_num)) p hp]
    simp only [meridionalPartial, Function.iterate_zero_apply, Function.iterate_one]
    ring

theorem abs_drdr_zoomWRec_add_abs_drdr_zoomSRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dr (dr (zoomWRec lam h rc zc u)) p| + |dr (dr (zoomSRec lam h rc zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0) := by
  refine abs_zoomWSRec_prefactor_le hlam hb 2 0 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [drdr_zoomWRec lam h rc zc u hu p hp]
    ring
  · rw [drdr_zoomSRec lam h rc zc u hu p hp]
    ring

theorem abs_drdz_zoomWRec_add_abs_drdz_zoomSRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dr (dz (zoomWRec lam h rc zc u)) p| + |dr (dz (zoomSRec lam h rc zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 1) := by
  refine abs_zoomWSRec_prefactor_le hlam hb 1 1 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [drdz_zoomWRec lam h rc zc u hu p hp]
    ring
  · rw [drdz_zoomSRec lam h rc zc u hu p hp]
    ring

theorem abs_dzdz_zoomWRec_add_abs_dzdz_zoomSRec_le (C h lam rc zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |dz (dz (zoomWRec lam h rc zc u)) p| + |dz (dz (zoomSRec lam h rc zc u)) p|
      ≤ C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 2) := by
  refine abs_zoomWSRec_prefactor_le hlam hb 0 2 (by omega) p hp _ _ _ ?_ ?_ (by norm_num)
  · rw [dzdz_zoomWRec lam h rc zc u hu p hp]
    ring
  · rw [dzdz_zoomSRec lam h rc zc u hu p hp]
    ring

/-! ### The bound on the rescaled azimuthal vorticity -/

/-- `eq:aniso:zoom:receding:bound`: with `δ_n = lam ^ (2 * h)` the rescaled azimuthal
vorticity obeys `|Θ_n| ≤ C (δ_n² |τ| ^ (-1 + h) + |τ| ^ (-1 - h))`, the two terms coming
from the `∂_Z V_n` and `∂_R W_n` entries of `eq:aniso:zoom:derivatives`. -/
theorem abs_zoomTheta_le (C h lam rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |zoomTheta lam h rc zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h) + (-p.2) ^ (-1 - h)) := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  have hdelta : (0 : ℝ) ≤ (lam ^ (2 * h)) ^ 2 := by positivity
  have hV := abs_dz_zoomVRec_le C h lam rc zc hlam u hb hu p hp
  rw [show (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 1) = -1 + h from by ring] at hV
  have hWS := abs_dr_zoomWRec_add_abs_dr_zoomSRec_le C h lam rc zc hlam u hb hu p hp
  rw [show (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 0) = -1 - h from by ring] at hWS
  have hW : |dr (zoomWRec lam h rc zc u) p| ≤ C * (-p.2) ^ (-1 - h) :=
    le_trans (by linarith only [abs_nonneg (dr (zoomSRec lam h rc zc u) p)]) hWS
  have habs : |(lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) p|
      = (lam ^ (2 * h)) ^ 2 * |dz (zoomVRec lam h rc zc u) p| := by
    rw [abs_mul, abs_of_nonneg hdelta]
  have hsplit : |zoomTheta lam h rc zc u p|
      ≤ (lam ^ (2 * h)) ^ 2 * |dz (zoomVRec lam h rc zc u) p|
        + |dr (zoomWRec lam h rc zc u) p| := by
    rw [zoomTheta_eq lam h rc zc hlam u hu1 p hp, ← habs]
    exact abs_sub _ _
  have hmul : (lam ^ (2 * h)) ^ 2 * |dz (zoomVRec lam h rc zc u) p|
      ≤ (lam ^ (2 * h)) ^ 2 * (C * (-p.2) ^ (-1 + h)) :=
    mul_le_mul_of_nonneg_left hV hdelta
  linarith only [hsplit, hmul, hW]

end CIV
