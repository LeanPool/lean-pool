/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# The Cartesian vorticity equation

The display in the proof of `lem:aniso:closure`: taking the curl of the momentum equation of
a classical solution gives `∂_t ω + (u·∇)ω − Δω = (ω·∇)u + curl f`, a Cartesian identity
holding on the whole open cylinder (not restricted to the meridional plane). The pressure
drops out because mixed second partials commute, the time derivative commutes with the
spatial partials, the Laplacian commutes with the curl by the same commutation, and the
identity `curl((u·∇)u) = (u·∇)ω − (ω·∇)u` is the one place the divergence-free condition is
used.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- A classical spatial partial derivative only sees a scalar field through its values on the
unit cylinder: two fields agreeing there have the same spatial partial derivative there. -/
private theorem spatialPartial_congr_of_eqOn {f g : ParabolicPoint → ℝ}
    (h : ∀ w ∈ unitCylinder, f w = g w) {z : Vec3 × ℝ} (hz : z ∈ unitCylinder) (k : Fin 3) :
    spatialPartial f k z = spatialPartial g k z := by
  have hev : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (isOpen_unitCylinder_prod.mem_nhds hz) h
  have htend : Filter.Tendsto (fun y : Vec3 => (y, z.2)) (nhds z.1) (nhds z) := by
    have hc : Continuous (fun y : Vec3 => (y, z.2)) := continuous_id.prodMk continuous_const
    simpa using hc.tendsto z.1
  have hevSlice : (fun y : Vec3 => f (y, z.2)) =ᶠ[nhds z.1] (fun y : Vec3 => g (y, z.2)) :=
    htend.eventually hev
  change fderiv ℝ (fun y : Vec3 => f (y, z.2)) z.1 (basisVec k)
      = fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1 (basisVec k)
  rw [hevSlice.fderiv_eq]

/-- Reordering the outer two directions of a third-order iterated spatial partial derivative
of a jointly smooth scalar field. -/
private theorem T3_swap_outer {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i j k : Fin 3) :
    spatialPartial (spatialSecondPartial g i j) k z
      = spatialPartial (spatialSecondPartial g i k) j z :=
  spatialSecondPartial_comm (contDiffOn_spatialPartial hg i) hz j k

/-- Reordering the inner two directions of a third-order iterated spatial partial derivative
of a jointly smooth scalar field. -/
private theorem T3_swap_inner {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i j k : Fin 3) :
    spatialPartial (spatialSecondPartial g i j) k z
      = spatialPartial (spatialSecondPartial g j i) k z :=
  spatialPartial_congr_of_eqOn (fun _w hw => spatialSecondPartial_comm hg hw i j) hz k

/-- The Laplacian in the repeated index `j` commutes with an outer spatial partial derivative
in direction `m`: `∂_m(∂_j∂_j g) = ∂_j∂_j(∂_m g)`, the fact that lets the cylindrical Laplacian
pass through the curl. -/
private theorem spatialPartial_spatialSecondPartial_comm {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (j m : Fin 3) :
    spatialPartial (spatialSecondPartial g j j) m z
      = spatialSecondPartial (spatialPartial g m) j j z :=
  (T3_swap_outer hg hz j j m).trans (T3_swap_inner hg hz j m j)

/-- The iterated spatial derivative is linear over subtraction of jointly smooth fields. -/
private theorem spatialSecondPartial_sub {f g : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w) unitCylinder)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) unitCylinder)
    {z : Vec3 × ℝ} (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialSecondPartial (fun w => f w - g w) i j z
      = spatialSecondPartial f i j z - spatialSecondPartial g i j z := by
  change spatialPartial (spatialPartial (fun w => f w - g w) i) j z = _
  have hEqOn : ∀ w ∈ unitCylinder, spatialPartial (fun w => f w - g w) i w
      = spatialPartial f i w - spatialPartial g i w := fun w hw =>
    spatialPartial_sub_of_differentiableAt (i := i)
      (differentiableAt_spatialSlice (hf.of_le (by norm_num)) hw)
      (differentiableAt_spatialSlice (hg.of_le (by norm_num)) hw)
  rw [spatialPartial_congr_of_eqOn hEqOn hz j]
  exact spatialPartial_sub_of_differentiableAt (i := j)
    (differentiableAt_spatialSlice ((contDiffOn_spatialPartial hf i).of_le (by norm_num)) hz)
    (differentiableAt_spatialSlice ((contDiffOn_spatialPartial hg i).of_le (by norm_num)) hz)

/-- The time slice of a jointly smooth scalar field is differentiable at every point of the
unit cylinder. -/
private theorem differentiableAt_timeSlice {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun s : ℝ => g (z.1, s)) z.2 := by
  have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) z :=
    (hg.differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  exact hjoint.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt

/-- The classical time partial derivative is linear over subtraction. -/
private theorem timePartial_sub {f g : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hf : DifferentiableAt ℝ (fun s : ℝ => f (z.1, s)) z.2)
    (hg : DifferentiableAt ℝ (fun s : ℝ => g (z.1, s)) z.2) :
    timePartial (fun w => f w - g w) z = timePartial f z - timePartial g z := by
  change fderiv ℝ (fun s : ℝ => f (z.1, s) - g (z.1, s)) z.2 1 = _
  rw [fderiv_fun_sub hf hg]
  rfl

/-- The one identity in `curl((u·∇)u) = (u·∇)ω − (ω·∇)u` that uses the divergence-free
condition: the quadratic-in-first-derivatives remainder left after peeling off the transport
term from the curl of the convective term is exactly minus the stretching term, once the
divergence vanishes. -/
private theorem curl_convective_identity (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (hdiv : ∑ j, spatialPartial (fun w => u w j) j z = 0) (i : Fin 3) :
    ∑ j, (spatialPartial (fun w => u w j) (i + 1) z * spatialPartial (fun w => u w (i + 2)) j z
        - spatialPartial (fun w => u w j) (i + 2) z * spatialPartial (fun w => u w (i + 1)) j z)
      + ∑ j, curlComp u j z * spatialPartial (fun w => u w i) j z = 0 := by
  simp only [Fin.sum_univ_three] at hdiv ⊢
  fin_cases i
  · simp
    linear_combination
      (norm := (simp only [curlComp_zero, curlComp_one, curlComp_two]; ring))
      (curlComp u (0 : Fin 3) z) * hdiv
  · simp
    linear_combination
      (norm := (simp only [curlComp_zero, curlComp_one, curlComp_two]; ring))
      (curlComp u (1 : Fin 3) z) * hdiv
  · simp
    linear_combination
      (norm := (simp only [curlComp_zero, curlComp_one, curlComp_two]; ring))
      (curlComp u (2 : Fin 3) z) * hdiv

/-- Differentiating the `k`-th momentum equation of a classical solution once more, in the
spatial direction `m`. This is the raw computation behind taking the curl of the momentum
equation: every occurrence of `u`'s component `k` on the right is already the closed form of
`spatialPartial (spatialPartial (fun w => u w k) k) m z` or a Leibniz-rule product, so the two
instances at `(k, m) = (i+2, i+1)` and `(k, m) = (i+1, i+2)` assemble into `curlComp`. -/
private theorem spatialPartial_momentum {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (k m : Fin 3) :
    timePartial (spatialPartial (fun w => u w k) m) z
        + (spatialPartial (fun w => u w 0) m z * spatialPartial (fun w => u w k) 0 z
              + u z 0 * spatialSecondPartial (fun w => u w k) 0 m z
            + (spatialPartial (fun w => u w 1) m z * spatialPartial (fun w => u w k) 1 z
              + u z 1 * spatialSecondPartial (fun w => u w k) 1 m z)
            + (spatialPartial (fun w => u w 2) m z * spatialPartial (fun w => u w k) 2 z
              + u z 2 * spatialSecondPartial (fun w => u w k) 2 m z))
        - (spatialPartial (spatialSecondPartial (fun w => u w k) 0 0) m z
            + spatialPartial (spatialSecondPartial (fun w => u w k) 1 1) m z
            + spatialPartial (spatialSecondPartial (fun w => u w k) 2 2) m z)
        + spatialSecondPartial p k m z
      = spatialPartial (fun w => f w k) m z := by
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1
  have hpTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1
  have hUkTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w k) unitCylinder :=
    contDiffOn_component huTop k
  have hUjTop : ∀ j : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w j) unitCylinder :=
    fun j => contDiffOn_component huTop j
  have hUkjTop : ∀ j : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v k) j w)
        unitCylinder :=
    fun j => contDiffOn_spatialPartial hUkTop j
  have hUkjjTop : ∀ j : Fin 3,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v k) j j w)
        unitCylinder :=
    fun j => contDiffOn_spatialPartial (hUkjTop j) j
  have hUktTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => timePartial (fun v => u v k) w)
      unitCylinder := contDiffOn_timePartial hUkTop
  have hPkTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial p k w) unitCylinder :=
    contDiffOn_spatialPartial hpTop k
  have hEqOn : ∀ w ∈ unitCylinder,
      (timePartial (fun v => u v k) w
          + (u w 0 * spatialPartial (fun v => u v k) 0 w
              + u w 1 * spatialPartial (fun v => u v k) 1 w
              + u w 2 * spatialPartial (fun v => u v k) 2 w)
          - (spatialSecondPartial (fun v => u v k) 0 0 w
              + spatialSecondPartial (fun v => u v k) 1 1 w
              + spatialSecondPartial (fun v => u v k) 2 2 w)
          + spatialPartial p k w)
        = f w k := by
    intro w hw
    have h := hsol.2.2.2.1 w hw k
    rwa [Fin.sum_univ_three, Fin.sum_univ_three] at h
  have hkey := spatialPartial_congr_of_eqOn hEqOn hz m
  rw [← hkey]
  have d0 : DifferentiableAt ℝ (fun y : Vec3 => (u (y, z.2) 0)) z.1 :=
    differentiableAt_spatialSlice ((hUjTop 0).of_le (by norm_num)) hz
  have d1 : DifferentiableAt ℝ (fun y : Vec3 => (u (y, z.2) 1)) z.1 :=
    differentiableAt_spatialSlice ((hUjTop 1).of_le (by norm_num)) hz
  have d2 : DifferentiableAt ℝ (fun y : Vec3 => (u (y, z.2) 2)) z.1 :=
    differentiableAt_spatialSlice ((hUjTop 2).of_le (by norm_num)) hz
  have dk0 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v k) 0 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ((hUkjTop 0).of_le (by norm_num)) hz
  have dk1 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v k) 1 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ((hUkjTop 1).of_le (by norm_num)) hz
  have dk2 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v k) 2 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ((hUkjTop 2).of_le (by norm_num)) hz
  have dkt : DifferentiableAt ℝ (fun y : Vec3 => timePartial (fun v => u v k) (y, z.2)) z.1 :=
    differentiableAt_spatialSlice (hUktTop.of_le (by norm_num)) hz
  have dk00 : DifferentiableAt ℝ
      (fun y : Vec3 => spatialSecondPartial (fun v => u v k) 0 0 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ((hUkjjTop 0).of_le (by norm_num)) hz
  have dk11 : DifferentiableAt ℝ
      (fun y : Vec3 => spatialSecondPartial (fun v => u v k) 1 1 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ((hUkjjTop 1).of_le (by norm_num)) hz
  have dk22 : DifferentiableAt ℝ
      (fun y : Vec3 => spatialSecondPartial (fun v => u v k) 2 2 (y, z.2)) z.1 :=
    differentiableAt_spatialSlice ((hUkjjTop 2).of_le (by norm_num)) hz
  have dpk : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial p k (y, z.2)) z.1 :=
    differentiableAt_spatialSlice (hPkTop.of_le (by norm_num)) hz
  have hB0 : DifferentiableAt ℝ
      (fun y : Vec3 => (fun w => u w 0 * spatialPartial (fun v => u v k) 0 w) (y, z.2)) z.1 :=
    d0.mul dk0
  have hB1 : DifferentiableAt ℝ
      (fun y : Vec3 => (fun w => u w 1 * spatialPartial (fun v => u v k) 1 w) (y, z.2)) z.1 :=
    d1.mul dk1
  have hB2 : DifferentiableAt ℝ
      (fun y : Vec3 => (fun w => u w 2 * spatialPartial (fun v => u v k) 2 w) (y, z.2)) z.1 :=
    d2.mul dk2
  have hB01 : DifferentiableAt ℝ (fun y : Vec3 =>
      (fun w => u w 0 * spatialPartial (fun v => u v k) 0 w
          + u w 1 * spatialPartial (fun v => u v k) 1 w) (y, z.2)) z.1 :=
    hB0.add hB1
  have hC01 : DifferentiableAt ℝ (fun y : Vec3 =>
      (fun w => spatialSecondPartial (fun v => u v k) 0 0 w
          + spatialSecondPartial (fun v => u v k) 1 1 w) (y, z.2)) z.1 :=
    dk00.add dk11
  have hA : DifferentiableAt ℝ (fun y : Vec3 =>
      (fun w => timePartial (fun v => u v k) w
          + (u w 0 * spatialPartial (fun v => u v k) 0 w
              + u w 1 * spatialPartial (fun v => u v k) 1 w
              + u w 2 * spatialPartial (fun v => u v k) 2 w)) (y, z.2)) z.1 :=
    dkt.add (hB01.add hB2)
  have hAC : DifferentiableAt ℝ (fun y : Vec3 =>
      (fun w => timePartial (fun v => u v k) w
          + (u w 0 * spatialPartial (fun v => u v k) 0 w
              + u w 1 * spatialPartial (fun v => u v k) 1 w
              + u w 2 * spatialPartial (fun v => u v k) 2 w)
          - (spatialSecondPartial (fun v => u v k) 0 0 w
              + spatialSecondPartial (fun v => u v k) 1 1 w
              + spatialSecondPartial (fun v => u v k) 2 2 w)) (y, z.2)) z.1 :=
    hA.sub (hC01.add dk22)
  rw [spatialPartial_add_of_differentiableAt (i := m) hAC dpk,
    spatialPartial_sub_of_differentiableAt (i := m) hA (hC01.add dk22),
    spatialPartial_add_of_differentiableAt (i := m) dkt (hB01.add hB2),
    spatialPartial_add_of_differentiableAt (i := m) hB01 hB2,
    spatialPartial_add_of_differentiableAt (i := m) hB0 hB1,
    spatialPartial_add_of_differentiableAt (i := m) hC01 dk22,
    spatialPartial_add_of_differentiableAt (i := m) dk00 dk11,
    spatialPartial_mul_of_differentiableAt (i := m) d0 dk0,
    spatialPartial_mul_of_differentiableAt (i := m) d1 dk1,
    spatialPartial_mul_of_differentiableAt (i := m) d2 dk2,
    spatialPartial_timePartial_comm (g := fun v => u v k) hUkTop hz m]
  change timePartial (spatialPartial (fun v => u v k) m) z
      + (spatialPartial (fun v => u v 0) m z * spatialPartial (fun v => u v k) 0 z
          + u z 0 * spatialPartial (spatialPartial (fun v => u v k) 0) m z
        + (spatialPartial (fun v => u v 1) m z * spatialPartial (fun v => u v k) 1 z
          + u z 1 * spatialPartial (spatialPartial (fun v => u v k) 1) m z)
        + (spatialPartial (fun v => u v 2) m z * spatialPartial (fun v => u v k) 2 z
          + u z 2 * spatialPartial (spatialPartial (fun v => u v k) 2) m z))
      - (spatialPartial (spatialSecondPartial (fun v => u v k) 0 0) m z
          + spatialPartial (spatialSecondPartial (fun v => u v k) 1 1) m z
          + spatialPartial (spatialSecondPartial (fun v => u v k) 2 2) m z)
      + spatialPartial (spatialPartial p k) m z
    = _
  ring

/-- The Cartesian vorticity equation of `lem:aniso:closure`: taking the curl of the momentum
equation of a classical solution gives `∂_t ω + (u·∇)ω − Δω = (ω·∇)u + curl f`, holding at
every point of the whole open cylinder (a Cartesian identity, not restricted to the meridional
plane). The pressure cancels by `spatialSecondPartial_comm`, the time derivative commutes with
the curl by `spatialPartial_timePartial_comm` (through `spatialPartial_momentum`), the
Laplacian commutes with the curl by the same mixed-partial symmetry, and
`curl_convective_identity` supplies the one step, `curl((u·∇)u) = (u·∇)ω − (ω·∇)u`, that uses
the divergence-free condition. -/
theorem cartesian_vorticity_pde
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (i : Fin 3) :
    timePartial (curlComp u i) z + ∑ j, u z j * spatialPartial (curlComp u i) j z
        - ∑ j, spatialSecondPartial (curlComp u i) j j z
      = ∑ j, curlComp u j z * spatialPartial (fun w => u w i) j z + curlComp f i z := by
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1
  have hpTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1
  have hFtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w (i + 2)) unitCylinder :=
    contDiffOn_component huTop (i + 2)
  have hGtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w (i + 1)) unitCylinder :=
    contDiffOn_component huTop (i + 1)
  have hFPtop : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialPartial (fun v => u v (i + 2)) (i + 1) w) unitCylinder :=
    contDiffOn_spatialPartial hFtop (i + 1)
  have hGPtop : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialPartial (fun v => u v (i + 1)) (i + 2) w) unitCylinder :=
    contDiffOn_spatialPartial hGtop (i + 2)
  have hcurlU : curlComp u i = (fun w : ParabolicPoint =>
      spatialPartial (fun v => u v (i + 2)) (i + 1) w
        - spatialPartial (fun v => u v (i + 1)) (i + 2) w) := rfl
  have hcurlF : curlComp f i z
      = spatialPartial (fun v => f v (i + 2)) (i + 1) z
        - spatialPartial (fun v => f v (i + 1)) (i + 2) z := rfl
  have hTime : timePartial (curlComp u i) z
      = timePartial (spatialPartial (fun v => u v (i + 2)) (i + 1)) z
        - timePartial (spatialPartial (fun v => u v (i + 1)) (i + 2)) z := by
    rw [hcurlU]
    exact timePartial_sub (differentiableAt_timeSlice hFPtop hz)
      (differentiableAt_timeSlice hGPtop hz)
  have hSP : ∀ j : Fin 3, spatialPartial (curlComp u i) j z
      = spatialSecondPartial (fun v => u v (i + 2)) j (i + 1) z
        - spatialSecondPartial (fun v => u v (i + 1)) j (i + 2) z := by
    intro j
    rw [hcurlU,
      spatialPartial_sub_of_differentiableAt (i := j)
        (differentiableAt_spatialSlice (hFPtop.of_le (by norm_num)) hz)
        (differentiableAt_spatialSlice (hGPtop.of_le (by norm_num)) hz)]
    change spatialSecondPartial (fun v => u v (i + 2)) (i + 1) j z
        - spatialSecondPartial (fun v => u v (i + 1)) (i + 2) j z = _
    rw [spatialSecondPartial_comm (g := fun v => u v (i + 2)) hFtop hz (i + 1) j,
      spatialSecondPartial_comm (g := fun v => u v (i + 1)) hGtop hz (i + 2) j]
  have hSSP : ∀ j : Fin 3, spatialSecondPartial (curlComp u i) j j z
      = spatialPartial (spatialSecondPartial (fun v => u v (i + 2)) j j) (i + 1) z
        - spatialPartial (spatialSecondPartial (fun v => u v (i + 1)) j j) (i + 2) z := by
    intro j
    rw [hcurlU]
    rw [spatialSecondPartial_sub hFPtop hGPtop hz j j]
    rw [spatialPartial_spatialSecondPartial_comm (g := fun v => u v (i + 2)) hFtop hz j (i + 1),
      spatialPartial_spatialSecondPartial_comm (g := fun v => u v (i + 1)) hGtop hz j (i + 2)]
  have hdiv : ∑ j, spatialPartial (fun w => u w j) j z = 0 := hsol.2.2.2.2 z hz
  have hconv := curl_convective_identity u z hdiv i
  have hpress := spatialSecondPartial_comm hpTop hz (i + 2) (i + 1)
  have hE1 := spatialPartial_momentum hsol hz (i + 2) (i + 1)
  have hE2 := spatialPartial_momentum hsol hz (i + 1) (i + 2)
  rw [hTime, hcurlF, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, hSP, hSP, hSP,
    hSSP, hSSP, hSSP]
  simp only [Fin.sum_univ_three] at hconv
  linear_combination hE1 - hE2 - hconv - hpress

end CIV
