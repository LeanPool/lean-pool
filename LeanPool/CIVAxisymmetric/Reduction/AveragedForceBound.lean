/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AveragedClassical

/-!
# The `C²` bound of the averaged force (`sec:reduction:core`)

`CIV/Reduction/AveragedClassical.lean` shows that averaging a classical solution's rotated
triples over `φ ∈ [0, 2π]` again yields a classical solution (`isClassicalSolutionOn_angularMean`)
with an axisymmetric force (`isAxisymmetricOn_angularMean_force`). This module proves the
remaining piece design note R8 needs: if the original force is `C²`-bounded then so is its
angular mean, `forceC2Bounded_angularMean`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The `C²` bound of the averaged force -/

section AveragedForceBound

/-! #### Elementary bounds -/

/-- A product of two bounded factors. -/
private theorem abs_mul_le_mul_of_abs_le {a b K M : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ M) :
    |a * b| ≤ K * M := by
  have hK : (0 : ℝ) ≤ K := le_trans (abs_nonneg a) ha
  have hM : (0 : ℝ) ≤ M := le_trans (abs_nonneg b) hb
  rw [abs_mul]
  nlinarith only [ha, hb, abs_nonneg a, abs_nonneg b, hK, hM]

/-- A sum of two terms with a common bound. -/
private theorem abs_add_le_two_mul {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a + b| ≤ 2 * M := by
  have ha' := abs_le.1 ha
  have hb' := abs_le.1 hb
  exact abs_le.2 ⟨by linarith only [ha'.1, hb'.1], by linarith only [ha'.2, hb'.2]⟩

/-- A difference of two terms with a common bound. -/
private theorem abs_sub_le_two_mul {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a - b| ≤ 2 * M := by
  have ha' := abs_le.1 ha
  have hb' := abs_le.1 hb
  exact abs_le.2 ⟨by linarith only [ha'.1, hb'.2], by linarith only [ha'.2, hb'.1]⟩

/-- A component of a rotated vector is bounded by twice a bound on the components. -/
private theorem abs_rotZ_apply_le (φ : ℝ) (V : Vec3) (i : Fin 3) {M : ℝ}
    (h : ∀ m : Fin 3, |V m| ≤ M) : |rotZ φ V i| ≤ 2 * M := by
  have hM : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (h 0)
  fin_cases i
  · show |Real.cos φ * V 0 - Real.sin φ * V 1| ≤ 2 * M
    refine abs_sub_le_two_mul ?_ ?_
    · have := abs_mul_le_mul_of_abs_le (Real.abs_cos_le_one φ) (h 0)
      linarith only [this]
    · have := abs_mul_le_mul_of_abs_le (Real.abs_sin_le_one φ) (h 1)
      linarith only [this]
  · show |Real.sin φ * V 0 + Real.cos φ * V 1| ≤ 2 * M
    refine abs_add_le_two_mul ?_ ?_
    · have := abs_mul_le_mul_of_abs_le (Real.abs_sin_le_one φ) (h 0)
      linarith only [this]
    · have := abs_mul_le_mul_of_abs_le (Real.abs_cos_le_one φ) (h 1)
      linarith only [this]
  · show |V 2| ≤ 2 * M
    have := h 2
    linarith only [this, hM]

/-- Every coordinate of a basis vector has modulus at most one. -/
private theorem abs_basisVec_apply_le_one (j m : Fin 3) : |(basisVec j : Vec3) m| ≤ 1 := by
  rw [basisVec_apply]
  split_ifs <;> norm_num

/-- Every coordinate of a rotated basis vector has modulus at most two. -/
private theorem abs_rotZ_basisVec_apply_le_two (ψ : ℝ) (j c : Fin 3) :
    |rotZ ψ (basisVec j) c| ≤ 2 := by
  have h := abs_rotZ_apply_le ψ (basisVec j) c (abs_basisVec_apply_le_one j)
  linarith only [h]

/-- The coordinate expansion of a directional derivative of a spatial slice. -/
private theorem fderiv_slice_apply_eq_sum (g : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (v : Vec3) :
    fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1 v
      = v 0 * spatialPartial g 0 z + v 1 * spatialPartial g 1 z + v 2 * spatialPartial g 2 z := by
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 + v 2 • basisVec 2 := by
    have h := (sum_smul_basisVec v).symm
    rwa [Fin.sum_univ_three] at h
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]
  rfl

/-- A directional derivative in a direction with coordinates of modulus at most two is
bounded by six times a bound on the Cartesian partial derivatives. -/
private theorem abs_fderiv_slice_apply_le {g : ParabolicPoint → ℝ} (z : ParabolicPoint)
    {v : Vec3} {M : ℝ} (hv : ∀ c : Fin 3, |v c| ≤ 2)
    (hb : ∀ c : Fin 3, |spatialPartial g c z| ≤ M) :
    |fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1 v| ≤ 6 * M := by
  have h0 := abs_le.1 (abs_mul_le_mul_of_abs_le (hv 0) (hb 0))
  have h1 := abs_le.1 (abs_mul_le_mul_of_abs_le (hv 1) (hb 1))
  have h2 := abs_le.1 (abs_mul_le_mul_of_abs_le (hv 2) (hb 2))
  rw [fderiv_slice_apply_eq_sum]
  exact abs_le.2 ⟨by linarith only [h0.1, h1.1, h2.1], by linarith only [h0.2, h1.2, h2.2]⟩

/-- A second directional derivative in directions with coordinates of modulus at most two is
bounded by thirty-six times a bound on the Cartesian second partial derivatives. -/
private theorem abs_hessAt_le {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) (z : ParabolicPoint)
    (hz : z ∈ unitCylinder) {v w : Vec3} {M : ℝ} (hv : ∀ c : Fin 3, |v c| ≤ 2)
    (hw : ∀ c : Fin 3, |w c| ≤ 2)
    (hb : ∀ c d : Fin 3, |hessAt g z.2 z.1 (basisVec c) (basisVec d)| ≤ M) :
    |hessAt g z.2 z.1 v w| ≤ 36 * M := by
  have hvexp : v = v 0 • basisVec 0 + v 1 • basisVec 1 + v 2 • basisVec 2 := by
    have h := (sum_smul_basisVec v).symm
    rwa [Fin.sum_univ_three] at h
  have hwexp : w = w 0 • basisVec 0 + w 1 • basisVec 1 + w 2 • basisVec 2 := by
    have h := (sum_smul_basisVec w).symm
    rwa [Fin.sum_univ_three] at h
  have hterm : ∀ c d : Fin 3,
      |v c * (w d * hessAt g z.2 z.1 (basisVec c) (basisVec d))| ≤ 4 * M := by
    intro c d
    have h := abs_mul_le_mul_of_abs_le (hv c)
      (abs_mul_le_mul_of_abs_le (hw d) (hb c d))
    linarith only [h]
  have t00 := abs_le.1 (hterm 0 0)
  have t01 := abs_le.1 (hterm 0 1)
  have t02 := abs_le.1 (hterm 0 2)
  have t10 := abs_le.1 (hterm 1 0)
  have t11 := abs_le.1 (hterm 1 1)
  have t12 := abs_le.1 (hterm 1 2)
  have t20 := abs_le.1 (hterm 2 0)
  have t21 := abs_le.1 (hterm 2 1)
  have t22 := abs_le.1 (hterm 2 2)
  conv_lhs => rw [hvexp, hwexp]
  simp only [hessAt_add_left, hessAt_smul_left, hessAt_add_right hg hz,
    hessAt_const_mul_right hg hz]
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith only [t00.1, t01.1, t02.1, t10.1, t11.1, t12.1, t20.1, t21.1, t22.1]
  · linarith only [t00.2, t01.2, t02.2, t10.2, t11.2, t12.2, t20.2, t21.2, t22.2]

/-! #### Second derivatives of the rotated field -/

/-- `hessAt` is a constant-coefficient linear combination in its function argument. -/
private theorem hessAt_combo {g₁ g₂ : ParabolicPoint → ℝ} (c d : ℝ)
    (h₁ : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g₁ z) unitCylinder)
    (h₂ : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g₂ z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (v w : Vec3) :
    hessAt (fun y : Vec3 × ℝ => c * g₁ y + d * g₂ y) z.2 z.1 v w
      = c * hessAt g₁ z.2 z.1 v w + d * hessAt g₂ z.2 z.1 v w := by
  have h₁1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g₁ z) unitCylinder := h₁.of_le (by norm_num)
  have h₂1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g₂ z) unitCylinder := h₂.of_le (by norm_num)
  have hpt : ∀ y ∈ vec3Ball (0 : Vec3) 1,
      fderiv ℝ (fun y' : Vec3 => c * g₁ (y', z.2) + d * g₂ (y', z.2)) y w
        = c * fderiv ℝ (fun y' : Vec3 => g₁ (y', z.2)) y w
          + d * fderiv ℝ (fun y' : Vec3 => g₂ (y', z.2)) y w := by
    intro y hy
    have hyz : ((y, z.2) : ParabolicPoint) ∈ unitCylinder := ⟨hy, hz.2⟩
    have hD1 : DifferentiableAt ℝ (fun x : Vec3 => g₁ (x, z.2)) y :=
      differentiableAt_spatialSlice h₁1 hyz
    have hD2 : DifferentiableAt ℝ (fun x : Vec3 => g₂ (x, z.2)) y :=
      differentiableAt_spatialSlice h₂1 hyz
    rw [fderiv_fun_add (hD1.const_mul c) (hD2.const_mul d), fderiv_const_mul hD1,
      fderiv_const_mul hD2]
    rfl
  have hev : (fun y : Vec3 =>
      fderiv ℝ (fun y' : Vec3 => c * g₁ (y', z.2) + d * g₂ (y', z.2)) y w)
      =ᶠ[nhds z.1] fun y : Vec3 => c * fderiv ℝ (fun y' : Vec3 => g₁ (y', z.2)) y w
          + d * fderiv ℝ (fun y' : Vec3 => g₂ (y', z.2)) y w := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy using hpt y hy
  have hD1' := differentiableAt_fderiv_slice h₁ hz w
  have hD2' := differentiableAt_fderiv_slice h₂ hz w
  show fderiv ℝ (fun y : Vec3 =>
      fderiv ℝ (fun y' : Vec3 => c * g₁ (y', z.2) + d * g₂ (y', z.2)) y w) z.1 v = _
  rw [hev.fderiv_eq, fderiv_fun_add (hD1'.const_mul c) (hD2'.const_mul d),
    fderiv_const_mul hD1', fderiv_const_mul hD2']
  rfl

/-- Cartesian mixed second spatial partial derivatives of a jointly smooth scalar field
commute. -/
private theorem spatialSecondPartial_slice_symm {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialSecondPartial g i j z = spatialSecondPartial g j i z := by
  have hopen : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball 0 1
  have hGsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => g (y, z.2)) (vec3Ball (0 : Vec3) 1) :=
    contDiffOn_spatialSlice hg hz.2
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ fun y : Vec3 => g (y, z.2))
      (vec3Ball (0 : Vec3) 1) := hGsm.fderiv_of_isOpen hopen (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ fun y : Vec3 => g (y, z.2)) z.1 :=
    (hfd.differentiableOn (by norm_num) z.1 hz.1).differentiableAt (hopen.mem_nhds hz.1)
  have key : ∀ v w : Vec3, hessAt g z.2 z.1 v w
      = fderiv ℝ (fderiv ℝ fun y : Vec3 => g (y, z.2)) z.1 v w := by
    intro v w
    have hcomp : HasFDerivAt (fun y : Vec3 => (fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y) w)
        ((ContinuousLinearMap.apply ℝ ℝ w).comp
          (fderiv ℝ (fderiv ℝ fun y : Vec3 => g (y, z.2)) z.1)) z.1 :=
      (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp (z.1 : Vec3) hD.hasFDerivAt
    show fderiv ℝ (fun y : Vec3 => (fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y) w) z.1 v = _
    rw [hcomp.fderiv]
    simp
  have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Vec3 => g (y, z.2)) z.1 :=
    hGsm.contDiffAt (hopen.mem_nhds hz.1)
  have hsym := (ContDiffAt.isSymmSndFDerivAt hat (by simp)).eq (basisVec j) (basisVec i)
  show hessAt g z.2 z.1 (basisVec j) (basisVec i) = hessAt g z.2 z.1 (basisVec i) (basisVec j)
  rw [key (basisVec j) (basisVec i), key (basisVec i) (basisVec j), hsym]

/-- A spatial partial derivative of a component of the rotated field is the corresponding
component of the rotation of the directional derivative of the field at the rotated point. -/
private theorem spatialPartial_rotField_apply (φ : ℝ) (f : ParabolicPoint → Vec3)
    (hf : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => f z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialPartial (fun w => rotField φ f w i) j z
      = rotZ φ (fderiv ℝ (fun y : Vec3 => f (y, z.2)) (rotZ (-φ) z.1)
          (rotZ (-φ) (basisVec j))) i := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ f z) unitCylinder :=
    contDiffOn_rotField φ f hf
  show fderiv ℝ (fun y : Vec3 => rotField φ f (y, z.2) i) z.1 (basisVec j) = _
  rw [fderiv_spatialSlice_apply hrot hz i (basisVec j),
    fderiv_rotField_spatial φ f hf hz (basisVec j)]

/-- A second directional derivative of a component of the rotated field is the corresponding
component of the rotation of the second directional derivative of the field at the rotated
point, in the rotated directions. -/
private theorem hessAt_rotField_apply (φ : ℝ) (f : ParabolicPoint → Vec3)
    (hf : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => f z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) (v w : Vec3) :
    hessAt (fun y : Vec3 × ℝ => rotField φ f y i) z.2 z.1 v w
      = rotZ φ (fun m : Fin 3 => hessAt (fun y : Vec3 × ℝ => f y m) z.2 (rotZ (-φ) z.1)
          (rotZ (-φ) v) (rotZ (-φ) w)) i := by
  have hc : ∀ m : Fin 3, ContDiffOn ℝ 2
      (fun y : Vec3 × ℝ => f (rotZ (-φ) y.1, y.2) m) unitCylinder := fun m =>
    contDiffOn_component_comp_rotZ (-φ) f hf m
  have hrot : ∀ m : Fin 3,
      hessAt (fun y : Vec3 × ℝ => f (rotZ (-φ) y.1, y.2) m) z.2 z.1 v w
        = hessAt (fun y : Vec3 × ℝ => f y m) z.2 (rotZ (-φ) z.1) (rotZ (-φ) v)
            (rotZ (-φ) w) := fun m =>
    hessAt_comp_rotZ (-φ) (fun y : Vec3 × ℝ => f y m) z v w
  fin_cases i
  · have hfun : (fun y : Vec3 × ℝ => rotField φ f y 0)
        = fun y : Vec3 × ℝ => Real.cos φ * f (rotZ (-φ) y.1, y.2) 0
            + (-Real.sin φ) * f (rotZ (-φ) y.1, y.2) 1 := by
      funext y
      show Real.cos φ * f (rotZ (-φ) y.1, y.2) 0 - Real.sin φ * f (rotZ (-φ) y.1, y.2) 1 = _
      ring
    show hessAt (fun y : Vec3 × ℝ => rotField φ f y 0) z.2 z.1 v w = _
    rw [hfun, hessAt_combo (Real.cos φ) (-Real.sin φ) (hc 0) (hc 1) hz v w, hrot 0, hrot 1]
    show _ = Real.cos φ * hessAt (fun y : Vec3 × ℝ => f y 0) z.2 (rotZ (-φ) z.1)
          (rotZ (-φ) v) (rotZ (-φ) w)
        - Real.sin φ * hessAt (fun y : Vec3 × ℝ => f y 1) z.2 (rotZ (-φ) z.1) (rotZ (-φ) v)
          (rotZ (-φ) w)
    ring
  · have hfun : (fun y : Vec3 × ℝ => rotField φ f y 1)
        = fun y : Vec3 × ℝ => Real.sin φ * f (rotZ (-φ) y.1, y.2) 0
            + Real.cos φ * f (rotZ (-φ) y.1, y.2) 1 := rfl
    show hessAt (fun y : Vec3 × ℝ => rotField φ f y 1) z.2 z.1 v w = _
    rw [hfun, hessAt_combo (Real.sin φ) (Real.cos φ) (hc 0) (hc 1) hz v w, hrot 0, hrot 1]
    rfl
  · show hessAt (fun y : Vec3 × ℝ => rotField φ f y 2) z.2 z.1 v w = _
    have hfun : (fun y : Vec3 × ℝ => rotField φ f y 2)
        = fun y : Vec3 × ℝ => f (rotZ (-φ) y.1, y.2) 2 := rfl
    rw [hfun, hrot 2]
    rfl

/-! #### Differentiation under the angular integral -/

/-- The angular average of an angle-dependent scalar integrand. -/
@[expose] private def angleAverage (G : ℝ × (Vec3 × ℝ) → ℝ) (z : ParabolicPoint) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi), G (φ, z)

/-- A spatial partial derivative of an angle-dependent integrand, in the point variable. -/
@[expose] private def anglePartial (j : Fin 3) (G : ℝ × (Vec3 × ℝ) → ℝ) : ℝ × (Vec3 × ℝ) → ℝ :=
  fun q => spatialPartial (fun w => G (q.1, w)) j q.2

/-- The parameter domain of the angular integrand is open. -/
private theorem isOpen_univ_prod_unitCylinder :
    IsOpen (X := ℝ × (Vec3 × ℝ)) (Set.prod (β := Vec3 × ℝ) univ unitCylinder) :=
  isOpen_univ.prod isOpen_unitCylinder_prod

/-- A spatial partial derivative of a jointly differentiable integrand is read off the joint
derivative. -/
private theorem anglePartial_eq_fderiv {G : ℝ × (Vec3 × ℝ) → ℝ}
    (hG : ContDiffOn ℝ 1 G (univ ×ˢ unitCylinder)) {q : ℝ × (Vec3 × ℝ)}
    (hq : q ∈ (univ ×ˢ unitCylinder : Set (ℝ × (Vec3 × ℝ)))) (j : Fin 3) :
    anglePartial j G q = fderiv ℝ G q ((0 : ℝ), ((basisVec j : Vec3), (0 : ℝ))) := by
  have hGd : DifferentiableAt ℝ G q :=
    (hG.differentiableOn one_ne_zero).differentiableAt
      (isOpen_univ_prod_unitCylinder.mem_nhds hq)
  have hemb : HasFDerivAt (fun y : Vec3 => ((q.1, (y, q.2.2)) : ℝ × (Vec3 × ℝ)))
      ((0 : Vec3 →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ))) q.2.1 :=
    (hasFDerivAt_const q.1 q.2.1).prodMk
      ((hasFDerivAt_id q.2.1).prodMk (hasFDerivAt_const q.2.2 q.2.1))
  have hcomp : HasFDerivAt (fun y : Vec3 => G (q.1, (y, q.2.2)))
      ((fderiv ℝ G q).comp ((0 : Vec3 →L[ℝ] ℝ).prod
        ((ContinuousLinearMap.id ℝ Vec3).prod (0 : Vec3 →L[ℝ] ℝ)))) q.2.1 :=
    hGd.hasFDerivAt.comp q.2.1 hemb
  show fderiv ℝ (fun y : Vec3 => G (q.1, (y, q.2.2))) q.2.1 (basisVec j) = _
  rw [hcomp.fderiv]
  rfl

/-- The spatial partial derivative of a smooth angular integrand is again smooth. -/
private theorem contDiffOn_anglePartial {G : ℝ × (Vec3 × ℝ) → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (univ ×ˢ unitCylinder)) (j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (anglePartial j G) (univ ×ˢ unitCylinder) := by
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ G) (univ ×ˢ unitCylinder) :=
    hG.fderiv_of_isOpen isOpen_univ_prod_unitCylinder (by norm_num)
  have htarget : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (Vec3 × ℝ) => (fderiv ℝ G q) ((0 : ℝ), ((basisVec j : Vec3), (0 : ℝ))))
      (univ ×ˢ unitCylinder) := hfd.clm_apply contDiffOn_const
  refine htarget.congr ?_
  intro q hq
  exact anglePartial_eq_fderiv (hG.of_le (by norm_num)) hq j

/-- A spatial partial derivative passes under the angular integral. -/
private theorem spatialPartial_angleAverage {G : ℝ × (Vec3 × ℝ) → ℝ}
    (hG : ContDiffOn ℝ 1 G (univ ×ˢ unitCylinder)) (j : Fin 3) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    spatialPartial (angleAverage G) j z = angleAverage (anglePartial j G) z := by
  obtain ⟨x₀, t⟩ := z
  have hx₀ : x₀ ∈ vec3Ball 0 1 := hz.1
  have ht : t ∈ Ioo (-1 : ℝ) 0 := hz.2
  have hball : IsOpen (vec3Ball 0 1) := isOpen_vec3Ball 0 1
  set H : ℝ × Vec3 → ℝ := fun q => G (q.1, (q.2, t)) with hH_def
  have hHsm : ContDiffOn ℝ 1 H (univ ×ˢ vec3Ball 0 1) := by
    have hemb : ContDiffOn ℝ 1 (fun q : ℝ × Vec3 => (q.1, ((q.2, t) : Vec3 × ℝ)))
        (univ ×ˢ vec3Ball 0 1) :=
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
    have hmaps : MapsTo (fun q : ℝ × Vec3 => (q.1, ((q.2, t) : Vec3 × ℝ)))
        (univ ×ˢ vec3Ball 0 1) (univ ×ˢ unitCylinder) := fun q hq => ⟨mem_univ _, hq.2, ht⟩
    exact hG.comp hemb hmaps
  have hfun : (fun y : Vec3 => angleAverage G (y, t))
      = fun y : Vec3 => (2 * Real.pi)⁻¹ * ∫ φ in Ioc 0 (2 * Real.pi), H (φ, y) := by
    funext y
    show (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi), G (φ, (y, t)) = _
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hderiv := (hasFDerivAt_parametric_integral_Ioc hball hx₀ hHsm 0 (2 * Real.pi)).const_mul
    (2 * Real.pi)⁻¹
  have hDint : IntegrableOn (fun φ => fderiv ℝ (fun y => H (φ, y)) x₀) (Ioc 0 (2 * Real.pi)) :=
    (continuous_section_of_continuousOn (continuousOn_fderiv_section_of_contDiffOn hball hHsm)
      hx₀).integrableOn_Ioc
  show fderiv ℝ (fun y : Vec3 => angleAverage G (y, t)) x₀ (basisVec j) = _
  rw [hfun, hderiv.fderiv, smul_apply, smul_eq_mul]
  show _ = (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi), anglePartial j G (φ, (x₀, t))
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ContinuousLinearMap.integral_apply hDint]
  rfl

/-- A uniform bound on the integrand bounds the angular average. -/
private theorem abs_angleAverage_le {G : ℝ × (Vec3 × ℝ) → ℝ} {z : ParabolicPoint} {C : ℝ}
    (h : ∀ φ : ℝ, |G (φ, z)| ≤ C) : |angleAverage G z| ≤ C := by
  have hpos : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hinv : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 hpos
  have hint : ‖∫ φ in (0 : ℝ)..(2 * Real.pi), G (φ, z)‖ ≤ C * |2 * Real.pi - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by
      rw [Real.norm_eq_abs]; exact h x
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpos] at hint
  have hstep : (2 * Real.pi)⁻¹ * |∫ φ in (0 : ℝ)..(2 * Real.pi), G (φ, z)|
      ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) := mul_le_mul_of_nonneg_left hint hinv.le
  have hsimp : (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) = C := by
    field_simp
  rw [hsimp] at hstep
  show |(2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi), G (φ, z)| ≤ C
  rw [abs_mul, abs_of_pos hinv]
  exact hstep

/-! #### Bounds on the rotated force and on the angular mean -/

/-- A component of the rotated force. -/
private theorem abs_rotField_apply_le (φ : ℝ) {f : ParabolicPoint → Vec3} {M : ℝ}
    (hM0 : ∀ w ∈ unitCylinder, ∀ m : Fin 3, |f w m| ≤ M) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) : |rotField φ f z i| ≤ 2 * M := by
  have hz' : (((rotZ (-φ) z.1 : Vec3), z.2) : ParabolicPoint) ∈ unitCylinder :=
    rotZ_mem_unitCylinder (-φ) hz
  exact abs_rotZ_apply_le φ _ i fun m => hM0 _ hz' m

/-- A first spatial partial derivative of a component of the rotated force. -/
private theorem abs_spatialPartial_rotField_le (φ : ℝ) {f : ParabolicPoint → Vec3} {M : ℝ}
    (hf : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hM1 : ∀ w ∈ unitCylinder, ∀ m c : Fin 3, |spatialPartial (fun y => f y m) c w| ≤ M)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i j : Fin 3) :
    |spatialPartial (fun w => rotField φ f w i) j z| ≤ 12 * M := by
  have hz' : (((rotZ (-φ) z.1 : Vec3), z.2) : ParabolicPoint) ∈ unitCylinder :=
    rotZ_mem_unitCylinder (-φ) hz
  rw [spatialPartial_rotField_apply φ f hf hz i j]
  have hbound : ∀ m : Fin 3, |fderiv ℝ (fun y : Vec3 => f (y, z.2)) (rotZ (-φ) z.1)
      (rotZ (-φ) (basisVec j)) m| ≤ 6 * M := by
    intro m
    have hcomp : fderiv ℝ (fun y : Vec3 => f (y, z.2)) (rotZ (-φ) z.1)
          (rotZ (-φ) (basisVec j)) m
        = fderiv ℝ (fun y : Vec3 => f (y, z.2) m) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec j)) :=
      (fderiv_spatialSlice_apply hf hz' m (rotZ (-φ) (basisVec j))).symm
    rw [hcomp]
    exact abs_fderiv_slice_apply_le (g := fun y => f y m) ((rotZ (-φ) z.1 : Vec3), z.2)
      (fun c => abs_rotZ_basisVec_apply_le_two (-φ) j c) fun c => hM1 _ hz' m c
  have h := abs_rotZ_apply_le φ _ i hbound
  linarith only [h]

/-- A second spatial partial derivative of a component of the rotated force. -/
private theorem abs_spatialSecondPartial_rotField_le (φ : ℝ) {f : ParabolicPoint → Vec3} {M : ℝ}
    (hf : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hM2 : ∀ w ∈ unitCylinder, ∀ m c d : Fin 3,
      |spatialSecondPartial (fun y => f y m) c d w| ≤ M)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i j k : Fin 3) :
    |spatialSecondPartial (fun w => rotField φ f w i) j k z| ≤ 72 * M := by
  have hz' : (((rotZ (-φ) z.1 : Vec3), z.2) : ParabolicPoint) ∈ unitCylinder :=
    rotZ_mem_unitCylinder (-φ) hz
  show |hessAt (fun w : Vec3 × ℝ => rotField φ f w i) z.2 z.1 (basisVec k) (basisVec j)|
    ≤ 72 * M
  rw [hessAt_rotField_apply φ f hf hz i (basisVec k) (basisVec j)]
  have hbound : ∀ m : Fin 3, |hessAt (fun y : Vec3 × ℝ => f y m) z.2 (rotZ (-φ) z.1)
      (rotZ (-φ) (basisVec k)) (rotZ (-φ) (basisVec j))| ≤ 36 * M := by
    intro m
    refine abs_hessAt_le (contDiffOn_component hf m) ((rotZ (-φ) z.1 : Vec3), z.2) hz'
      (fun c => abs_rotZ_basisVec_apply_le_two (-φ) k c)
      (fun c => abs_rotZ_basisVec_apply_le_two (-φ) j c) ?_
    intro c d
    exact hM2 _ hz' m d c
  have h := abs_rotZ_apply_le φ _ i hbound
  linarith only [h]

/-! #### The derivatives of the angular mean as angular averages -/

/-- A first spatial partial derivative of the angular mean is the angular average of the
corresponding derivatives of the rotated fields. -/
private theorem spatialPartial_angularMean_eq_angleAverage (f : ParabolicPoint → Vec3)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialPartial (fun w => angularMean f w i) j z
      = angleAverage (anglePartial j fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i) z := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i)
      (univ ×ˢ unitCylinder) := contDiffOn_pi.1 (contDiffOn_rotField_uncurry (⊤ : ℕ∞) hf) i
  have heq : ∀ w ∈ unitCylinder, angularMean f w i
      = angleAverage (fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i) w :=
    fun w hw => angularMean_apply_eq f hf hw i
  have hcongr := spatialPartial_congr_of_eqOn (v := fun w : Vec3 × ℝ => angularMean f w i)
    (u := fun w : Vec3 × ℝ =>
      angleAverage (fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i) w) heq hz j
  exact hcongr.trans (spatialPartial_angleAverage (hG.of_le (by norm_num)) j hz)

/-- A second spatial partial derivative of the angular mean is the angular average of the
corresponding derivatives of the rotated fields. -/
private theorem spatialSecondPartial_angularMean_eq_angleAverage (f : ParabolicPoint → Vec3)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i j k : Fin 3) :
    spatialSecondPartial (fun w => angularMean f w i) j k z
      = angleAverage (anglePartial k (anglePartial j
          fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i)) z := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i)
      (univ ×ˢ unitCylinder) := contDiffOn_pi.1 (contDiffOn_rotField_uncurry (⊤ : ℕ∞) hf) i
  have hG1 := contDiffOn_anglePartial hG j
  have heq : ∀ w ∈ unitCylinder, spatialPartial (fun w' => angularMean f w' i) j w
      = angleAverage (anglePartial j fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i) w :=
    fun w hw => spatialPartial_angularMean_eq_angleAverage f hf hw i j
  have hcongr := spatialPartial_congr_of_eqOn
    (v := fun w : Vec3 × ℝ => spatialPartial (fun w' => angularMean f w' i) j w)
    (u := fun w : Vec3 × ℝ =>
      angleAverage (anglePartial j fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i) w)
    heq hz k
  show spatialPartial (fun w => spatialPartial (fun w' => angularMean f w' i) j w) k z = _
  exact hcongr.trans (spatialPartial_angleAverage (hG1.of_le (by norm_num)) k hz)

/-! #### Reading the multi-index derivatives of order at most two -/

/-- A multi-index derivative of total order at most two is the identity, a first Cartesian
partial derivative, or an iterated second Cartesian partial derivative. -/
private theorem multiPartial_le_two {α : Fin 3 → ℕ} (hα : α 0 + α 1 + α 2 ≤ 2)
    (g : ParabolicPoint → ℝ) :
    multiPartial g α = g ∨ (∃ a : Fin 3, multiPartial g α = spatialPartial g a)
      ∨ ∃ a b : Fin 3, multiPartial g α = spatialPartial (fun w => spatialPartial g b w) a := by
  have hmp : multiPartial g α = (fun k => spatialPartial k 0)^[α 0]
      ((fun k => spatialPartial k 1)^[α 1] ((fun k => spatialPartial k 2)^[α 2] g)) := rfl
  have hcases : (α 0 = 0 ∧ α 1 = 0 ∧ α 2 = 0) ∨ (α 0 = 1 ∧ α 1 = 0 ∧ α 2 = 0)
      ∨ (α 0 = 0 ∧ α 1 = 1 ∧ α 2 = 0) ∨ (α 0 = 0 ∧ α 1 = 0 ∧ α 2 = 1)
      ∨ (α 0 = 2 ∧ α 1 = 0 ∧ α 2 = 0) ∨ (α 0 = 0 ∧ α 1 = 2 ∧ α 2 = 0)
      ∨ (α 0 = 0 ∧ α 1 = 0 ∧ α 2 = 2) ∨ (α 0 = 1 ∧ α 1 = 1 ∧ α 2 = 0)
      ∨ (α 0 = 1 ∧ α 1 = 0 ∧ α 2 = 1) ∨ (α 0 = 0 ∧ α 1 = 1 ∧ α 2 = 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inl (by rw [hmp, h0, h1, h2]; rfl)
  · exact Or.inr (Or.inl ⟨0, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inl ⟨1, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inl ⟨2, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inr ⟨0, 0, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inr ⟨1, 1, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inr ⟨2, 2, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inr ⟨0, 1, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inr ⟨0, 2, by rw [hmp, h0, h1, h2]; rfl⟩)
  · exact Or.inr (Or.inr ⟨1, 2, by rw [hmp, h0, h1, h2]; rfl⟩)

/-- A first Cartesian partial derivative is a multi-index derivative of order one. -/
private theorem exists_multiPartial_first (g : ParabolicPoint → ℝ) (c : Fin 3) :
    ∃ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 ∧ multiPartial g α = spatialPartial g c := by
  fin_cases c
  · exact ⟨![1, 0, 0], by decide, rfl⟩
  · exact ⟨![0, 1, 0], by decide, rfl⟩
  · exact ⟨![0, 0, 1], by decide, rfl⟩

/-- An ordered second Cartesian partial derivative is a multi-index derivative of order two. -/
private theorem exists_multiPartial_second (g : ParabolicPoint → ℝ) {c d : Fin 3} (hdc : d ≤ c) :
    ∃ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 ∧ multiPartial g α = spatialSecondPartial g c d := by
  fin_cases c <;> fin_cases d
  · exact ⟨![2, 0, 0], by decide, rfl⟩
  · exact absurd hdc (by decide)
  · exact absurd hdc (by decide)
  · exact ⟨![1, 1, 0], by decide, rfl⟩
  · exact ⟨![0, 2, 0], by decide, rfl⟩
  · exact absurd hdc (by decide)
  · exact ⟨![1, 0, 1], by decide, rfl⟩
  · exact ⟨![0, 1, 1], by decide, rfl⟩
  · exact ⟨![0, 0, 2], by decide, rfl⟩

/-! #### The `C²` bound -/

/-- The angular mean of a smooth, `C²`-bounded force is again `C²` bounded
(`eq:interior:force:c-two` for the averaged force of design note R8). The spatial derivatives
of the mean are the angular means of the corresponding derivatives of the rotated fields, and
each of those is a bounded linear combination of the derivatives of the force at the rotated
point, so the bound is inherited with an explicit numerical factor. -/
theorem forceC2Bounded_angularMean {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f) : ForceC2Bounded (angularMean f) := by
  obtain ⟨M, hM⟩ := hMf
  have hf1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => f z) unitCylinder := hf.of_le (by norm_num)
  have hf2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => f z) unitCylinder := hf.of_le (by norm_num)
  have hMnn : (0 : ℝ) ≤ |M| := abs_nonneg M
  have hM0 : ∀ w ∈ unitCylinder, ∀ m : Fin 3, |f w m| ≤ |M| := by
    intro w hw m
    have h := hM w hw m (fun _ => 0) (by norm_num)
    have he : multiPartial (fun y => f y m) (fun _ => 0) = fun y => f y m := rfl
    rw [he] at h
    exact le_trans h (le_abs_self M)
  have hM1 : ∀ w ∈ unitCylinder, ∀ m c : Fin 3,
      |spatialPartial (fun y => f y m) c w| ≤ |M| := by
    intro w hw m c
    obtain ⟨α, hα, he⟩ := exists_multiPartial_first (fun y => f y m) c
    have h := hM w hw m α hα
    rw [he] at h
    exact le_trans h (le_abs_self M)
  have hM2 : ∀ w ∈ unitCylinder, ∀ m c d : Fin 3,
      |spatialSecondPartial (fun y => f y m) c d w| ≤ |M| := by
    intro w hw m c d
    rcases le_total d c with hdc | hcd
    · obtain ⟨α, hα, he⟩ := exists_multiPartial_second (fun y => f y m) hdc
      have h := hM w hw m α hα
      rw [he] at h
      exact le_trans h (le_abs_self M)
    · obtain ⟨α, hα, he⟩ := exists_multiPartial_second (fun y => f y m) hcd
      have h := hM w hw m α hα
      rw [he] at h
      have hsym : spatialSecondPartial (fun y => f y m) c d w
          = spatialSecondPartial (fun y => f y m) d c w :=
        spatialSecondPartial_slice_symm (contDiffOn_component hf m) hw c d
      rw [hsym]
      exact le_trans h (le_abs_self M)
  refine ⟨72 * |M|, ?_⟩
  intro z hz i α hα
  rcases multiPartial_le_two hα (fun w => angularMean f w i) with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · rw [h]
    show |angularMean f z i| ≤ 72 * |M|
    have hb : |angularMean f z i| ≤ 2 * |M| := by
      rw [angularMean_apply_eq f hf hz i]
      show |angleAverage (fun q : ℝ × (Vec3 × ℝ) => rotField q.1 f q.2 i) z| ≤ 2 * |M|
      exact abs_angleAverage_le fun φ => abs_rotField_apply_le φ hM0 hz i
    linarith only [hb, hMnn]
  · rw [h]
    have hb : |spatialPartial (fun w => angularMean f w i) a z| ≤ 12 * |M| := by
      rw [spatialPartial_angularMean_eq_angleAverage f hf hz i a]
      exact abs_angleAverage_le fun φ => abs_spatialPartial_rotField_le φ hf1 hM1 hz i a
    linarith only [hb, hMnn]
  · rw [h]
    have hb : |spatialSecondPartial (fun w => angularMean f w i) b a z| ≤ 72 * |M| := by
      rw [spatialSecondPartial_angularMean_eq_angleAverage f hf hz i b a]
      exact abs_angleAverage_le fun φ =>
        abs_spatialSecondPartial_rotField_le φ hf2 hM2 hz i b a
    exact hb

end AveragedForceBound

end CIV
