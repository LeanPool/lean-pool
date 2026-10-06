/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatPointwiseBound
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.EllipticLocal
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.VorticityDerivativeEquations
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialGradPairBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CIVAxisymmetric.Reduction.SpatialPartialCongrSpaceTimeSet

/-!
# The local steps of the interior estimates

At a point `(x, s)` whose backward window `B̄(x, 2ρ) × [s - ρ², s]` lies in the unit cylinder,
where the velocity is bounded by `Mu`, the pointwise heat bound applied to the vorticity
equation in divergence form (and to its first and second spatial derivatives) bounds the
vorticity level at `(x, s)` by `C ρ Λ + C / ρ`, where `Λ` bounds the same level on the window.
The factor `ρ` in front of `Λ` is what the weighted absorption consumes. These are the local
steps of the interior estimates in the proof of `lem:aniso:annulus`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The antisymmetric flux is smooth where its field is. -/
theorem contDiffOn_serrinForceFlux {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) (i m : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinForceFlux f i m z) unitCylinder := by
  have hfk : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z k) unitCylinder :=
    fun k => (contDiffOn_pi.mp hf) k
  unfold serrinForceFlux
  split_ifs
  · exact hfk _
  · exact (hfk _).neg
  · exact contDiffOn_const

/-- The antisymmetric flux is bounded by any bound of the field components. -/
theorem abs_serrinForceFlux_le {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ k, |f z k| ≤ B) (i m : Fin 3) : |serrinForceFlux f i m z| ≤ B := by
  unfold serrinForceFlux
  split_ifs
  · exact hB _
  · rw [abs_neg]; exact hB _
  · rw [abs_zero]; exact hB0

/-- Each vorticity component is bounded by the level-zero sum. -/
theorem abs_curlComp_le_vortSum0 (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (i : Fin 3) :
    |curlComp u i z| ≤ vortSum0 u z :=
  Finset.single_le_sum (f := fun k => |curlComp u k z|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- The divergence-form flux of the vorticity equation is bounded by `2 Mu Λ + B`. -/
theorem abs_serrinVortFlux_le {u f : ParabolicPoint → Vec3} {z : ParabolicPoint}
    {Mu Λ B : ℝ} (hB0 : 0 ≤ B) (hu : ∀ k, |u z k| ≤ Mu) (hω : vortSum0 u z ≤ Λ)
    (hf : ∀ k, |f z k| ≤ B) (i m : Fin 3) :
    |serrinVortFlux u f i m z| ≤ 2 * Mu * Λ + B := by
  unfold serrinVortFlux
  have h1 := (abs_curlComp_le_vortSum0 u z m).trans hω
  have h2 := (abs_curlComp_le_vortSum0 u z i).trans hω
  have hMu : 0 ≤ Mu := (abs_nonneg _).trans (hu 0)
  have h3 := abs_serrinForceFlux_le hB0 hf i m
  calc |curlComp u m z * u z i - u z m * curlComp u i z + serrinForceFlux f i m z|
      ≤ |curlComp u m z| * |u z i| + |u z m| * |curlComp u i z| +
          |serrinForceFlux f i m z| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (le_of_eq ?_)) le_rfl)
        rw [abs_mul, abs_mul]
    _ ≤ Λ * Mu + Mu * Λ + B := by
        have hΛ0 : 0 ≤ Λ := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans hω
        exact add_le_add (add_le_add (mul_le_mul h1 (hu i) (abs_nonneg _) hΛ0)
          (mul_le_mul (hu m) h2 (abs_nonneg _) hMu)) h3
    _ = 2 * Mu * Λ + B := by ring

/-- The local step at level zero. -/
theorem LS0_local_level0 : ∃ C : ℝ, 0 < C ∧ ∀ (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
    IsClassicalSolutionOn u p f unitCylinder → ∀ Mf Mu : ℝ,
    (∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) →
    ∀ (x : Vec3) (s ρ Λ : ℝ), 0 < ρ → ρ ≤ 1 →
    (∀ (y : Vec3) (s' : ℝ), vec3EuclideanNorm (y - x) ≤ 2 * ρ → s - ρ ^ 2 ≤ s' → s' ≤ s →
      (y, s') ∈ unitCylinder ∧ (∀ i, |u (y, s') i| ≤ Mu) ∧ vortSum0 u (y, s') ≤ Λ) →
    vortSum0 u (x, s) ≤ C * (1 + Mu) * ρ * Λ + C * (1 + Mu + Mf) / ρ := by
  obtain ⟨CH, hCH, hHB⟩ := serrin_heat_pointwise_bound
  refine ⟨6 * CH, by positivity, ?_⟩
  intro u p f hcl Mf Mu hMf x s ρ Λ hρ hρ1 hwin
  have hs2 : s - ρ ^ 2 ≤ s := by have := sq_nonneg ρ; linarith only [this]
  have hx0 : vec3EuclideanNorm (x - x) ≤ 2 * ρ := by
    rw [sub_self, vec3EuclideanNorm_zero]; positivity
  obtain ⟨hxQ, hux, hωx⟩ := hwin x s hx0 hs2 le_rfl
  have hMu : 0 ≤ Mu := (abs_nonneg _).trans (hux 0)
  have hΛ : 0 ≤ Λ := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans hωx
  have hfb : ∀ z ∈ unitCylinder, ∀ k, |f z k| ≤ Mf := fun z hz k =>
    hMf z hz k 0 (by simp)
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hfb _ hxQ 0)
  have hwinρ : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s,
      z ∈ unitCylinder ∧ (∀ i, |u z i| ≤ Mu) ∧ vortSum0 u z ≤ Λ := by
    intro z hz
    exact hwin z.1 z.2 (hz.1.trans (by linarith only [hρ])) hz.2.1 hz.2.2
  have hcomp : ∀ i, |curlComp u i (x, s)| ≤ CH * (ρ * (2 * Mu * Λ + Mf) + Mu / ρ) := by
    intro i
    exact hHB (curlComp u i) (serrinForceFlux u i) (serrinVortFlux u f i) unitCylinder x s ρ
      (2 * Mu * Λ + Mf) Mu isOpen_unitCylinder_prod hρ hρ1 (fun z hz => (hwinρ z hz).1)
      (contDiffOn_curlComp_unitCylinder hcl.1 i)
      (fun l => contDiffOn_serrinForceFlux hcl.1 i l)
      (fun m => contDiffOn_serrinVortFlux hcl i m)
      (fun z hz => (sum_spatialPartial_serrinForceFlux hcl.1 z hz i).symm)
      (fun z hz => vorticity_divergence_form hcl z hz i)
      (fun z hz m => abs_serrinVortFlux_le hMf0 (hwinρ z hz).2.1 (hwinρ z hz).2.2
        (hfb z (hwinρ z hz).1) i m)
      (fun z hz l => abs_serrinForceFlux_le hMu (hwinρ z hz).2.1 i l)
  have hsum : vortSum0 u (x, s) ≤ 3 * (CH * (ρ * (2 * Mu * Λ + Mf) + Mu / ρ)) := by
    unfold vortSum0
    calc ∑ i, |curlComp u i (x, s)| ≤ ∑ _i : Fin 3, CH * (ρ * (2 * Mu * Λ + Mf) + Mu / ρ) :=
          Finset.sum_le_sum (fun i _ => hcomp i)
      _ = 3 * (CH * (ρ * (2 * Mu * Λ + Mf) + Mu / ρ)) := by simp
  refine hsum.trans ?_
  have hρinv : ρ ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith only [hρ, hρ1]
  have h1 : ρ * Mf ≤ Mf / ρ := by
    rw [div_eq_mul_one_div, mul_comm Mf]
    exact mul_le_mul_of_nonneg_right hρinv hMf0
  have e : 3 * (CH * (ρ * (2 * Mu * Λ + Mf) + Mu / ρ)) =
      6 * CH * Mu * ρ * Λ + 3 * CH * (ρ * Mf) + 3 * CH * (Mu / ρ) := by ring
  have e2 : 6 * CH * (1 + Mu) * ρ * Λ + 6 * CH * (1 + Mu + Mf) / ρ =
      6 * CH * Mu * ρ * Λ + 6 * CH * ρ * Λ + 6 * CH * (1 / ρ) + 6 * CH * (Mu / ρ) +
        6 * CH * (Mf / ρ) := by
    field_simp
    ring
  rw [e, e2]
  have hρΛ : 0 ≤ ρ * Λ := mul_nonneg hρ.le hΛ
  have h1ρ : 0 ≤ 1 / ρ := by positivity
  have hMuρ : 0 ≤ Mu / ρ := by positivity
  have hMfρ : 0 ≤ Mf / ρ := by positivity
  nlinarith only [hCH, h1, hρΛ, h1ρ, hMuρ, hMfρ, mul_le_mul_of_nonneg_left h1 hCH.le,
    mul_nonneg hCH.le hρΛ, mul_nonneg hCH.le h1ρ, mul_nonneg hCH.le hMuρ, mul_nonneg hCH.le hMfρ]

/-- Each first derivative of the vorticity is bounded by the level-one sum. -/
theorem abs_spatialPartial_curlComp_le_vortSum1 (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (i j : Fin 3) : |spatialPartial (curlComp u i) j z| ≤ vortSum1 u z := by
  unfold vortSum1
  calc |spatialPartial (curlComp u i) j z| ≤ ∑ j', |spatialPartial (curlComp u i) j' z| :=
        Finset.single_le_sum (f := fun j' => |spatialPartial (curlComp u i) j' z|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |spatialPartial (curlComp u i') j' z| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |spatialPartial (curlComp u i') j' z|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

/-- Each first derivative of the velocity is bounded by the level-one velocity sum. -/
theorem abs_spatialPartial_le_velSum1 (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (i j : Fin 3) : |spatialPartial (fun w => u w i) j z| ≤ velSum1 u z := by
  unfold velSum1
  calc |spatialPartial (fun w => u w i) j z| ≤ ∑ j', |spatialPartial (fun w => u w i) j' z| :=
        Finset.single_le_sum (f := fun j' => |spatialPartial (fun w => u w i) j' z|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |spatialPartial (fun w => u w i') j' z| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |spatialPartial (fun w => u w i') j' z|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

/-- The spatial derivative of the antisymmetric flux is a signed first derivative of a field
component. -/
theorem abs_spatialPartial_serrinForceFlux_le {f : ParabolicPoint → Vec3} {z : ParabolicPoint}
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k j, |spatialPartial (fun w => f w k) j z| ≤ B)
    (i m j : Fin 3) : |spatialPartial (serrinForceFlux f i m) j z| ≤ B := by
  unfold serrinForceFlux
  split_ifs
  · exact hB _ _
  · have e : spatialPartial (fun w => -f w (i + 1)) j z = -spatialPartial (fun w => f w (i + 1))
    j z := by
      unfold spatialPartial
      rw [fderiv_fun_neg]
      rfl
    rw [e, abs_neg]; exact hB _ _
  · have e : spatialPartial (fun _ => (0 : ℝ)) j z = 0 := by
      unfold spatialPartial; simp
    rw [e, abs_zero]; exact hB0

/-- The spatial derivative of the divergence-form flux, expanded by the product rule. -/
theorem spatialPartial_serrinVortFlux_eq {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hcl : IsClassicalSolutionOn u p f unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i m j : Fin 3) :
    spatialPartial (serrinVortFlux u f i m) j z =
      spatialPartial (curlComp u m) j z * u z i +
        curlComp u m z * spatialPartial (fun w => u w i) j z -
        (spatialPartial (fun w => u w m) j z * curlComp u i z +
          u z m * spatialPartial (curlComp u i) j z) +
        spatialPartial (serrinForceFlux f i m) j z := by
  have hc := contDiffOn_curlComp_unitCylinder hcl.1
  have hu : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z k) unitCylinder :=
    fun k => (contDiffOn_pi.mp hcl.1) k
  have hF := contDiffOn_serrinForceFlux hcl.2.2.1 i m
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => curlComp u m z * u z i) unitCylinder :=
    (hc m).mul (hu i)
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z m * curlComp u i z) unitCylinder :=
    (hu m).mul (hc i)
  have dA := differentiableAt_spatialSlice (hA.of_le (by norm_num)) hz
  have dB := differentiableAt_spatialSlice (hB.of_le (by norm_num)) hz
  have dF := differentiableAt_spatialSlice (hF.of_le (by norm_num)) hz
  have e : serrinVortFlux u f i m = fun w => (fun w => curlComp u m w * u w i - u w m *
      curlComp u i w) w + serrinForceFlux f i m w := rfl
  rw [e, spatialPartial_add_of_differentiableAt (dA.sub dB) dF,
    spatialPartial_sub_of_differentiableAt dA dB,
    spatialPartial_mul_of_contDiffOn (hc m) (hu i) hz j,
    spatialPartial_mul_of_contDiffOn (hu m) (hc i) hz j]
  rfl

/-- A field supported on one index: its divergence is the partial of that component. -/
theorem sum_spatialPartial_single (g : ParabolicPoint → ℝ) (j : Fin 3) (z : ParabolicPoint) :
    ∑ l, spatialPartial (fun w => if l = j then g w else 0) l z = spatialPartial g j z := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp only [hl, ite_false]
    unfold spatialPartial; simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The first-derivative bound of the partial derivative of the force. -/
theorem abs_spatialPartial_force_le {f : ParabolicPoint → Vec3} {Mf : ℝ}
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) {z : ParabolicPoint} (hz : z ∈ unitCylinder)
    (k j : Fin 3) : |spatialPartial (fun w => f w k) j z| ≤ Mf := by
  have h := hMf z hz k (Pi.single j 1) (by fin_cases j <;> simp)
  rwa [multiPartial_single_eq_spatialPartial] at h

/-- The triangle inequality through an intermediate point. -/
theorem vec3EuclideanNorm_sub_le_add (x y z : Vec3) :
    vec3EuclideanNorm (y - x) ≤ vec3EuclideanNorm (y - z) + vec3EuclideanNorm (z - x) := by
  have := vec3EuclideanNorm_add_le (y - z) (z - x)
  rwa [sub_add_sub_cancel] at this

/-- The local step at level one. -/
theorem LS1_local_level1 : ∃ C : ℝ, 0 < C ∧ ∀ (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
    IsClassicalSolutionOn u p f unitCylinder → ∀ Mf Mu Ω₀ : ℝ,
    (∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) →
    ∀ (x : Vec3) (s ρ Λ : ℝ), 0 < ρ → ρ ≤ 1 →
    (∀ (y : Vec3) (s' : ℝ), vec3EuclideanNorm (y - x) ≤ 2 * ρ → s - ρ ^ 2 ≤ s' → s' ≤ s →
      (y, s') ∈ unitCylinder ∧ (∀ i, |u (y, s') i| ≤ Mu) ∧ vortSum0 u (y, s') ≤ Ω₀ ∧
        vortSum1 u (y, s') ≤ Λ) →
    vortSum1 u (x, s) ≤ C * (1 + Mu + Ω₀) * ρ * Λ + C * (1 + Mu + Ω₀ + Mf) ^ 2 / ρ := by
  obtain ⟨CH, hCH, hHB⟩ := serrin_heat_pointwise_bound
  obtain ⟨CE, hCE, hEL⟩ := EL1_local
  refine ⟨18 * CH * (1 + CE), by positivity, ?_⟩
  intro u p f hcl Mf Mu Ω₀ hMf x s ρ Λ hρ hρ1 hwin
  have hs2 : s - ρ ^ 2 ≤ s := by have := sq_nonneg ρ; linarith only [this]
  have hx0 : vec3EuclideanNorm (x - x) ≤ 2 * ρ := by
    rw [sub_self, vec3EuclideanNorm_zero]; positivity
  obtain ⟨hxQ, hux, hω0x, hω1x⟩ := hwin x s hx0 hs2 le_rfl
  have hMu : 0 ≤ Mu := (abs_nonneg _).trans (hux 0)
  have hΩ₀ : 0 ≤ Ω₀ := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans hω0x
  have hΛ : 0 ≤ Λ := (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans hω1x
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf _ hxQ 0 0 (by simp))
  set V : ℝ := CE * (ρ * Λ + Mu / ρ) with hV
  have hV0 : 0 ≤ V := by positivity
  -- the window of radius `ρ` and the elliptic bound at its points
  have hwinρ : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s,
      z ∈ unitCylinder ∧ (∀ i, |u z i| ≤ Mu) ∧ vortSum0 u z ≤ Ω₀ ∧ vortSum1 u z ≤ Λ ∧
        velSum1 u z ≤ V := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hwin z.1 z.2 (hz.1.trans (by linarith only [hρ])) hz.2.1 hz.2.2
    refine ⟨h1, h2, h3, h4, ?_⟩
    have hball : ∀ y : Vec3, vec3EuclideanNorm (y - z.1) ≤ ρ →
        vec3EuclideanNorm (y - x) ≤ 2 * ρ := fun y hy =>
      (vec3EuclideanNorm_sub_le_add x y z.1).trans (by
        linarith only [hy, (show vec3EuclideanNorm (z.1 - x) ≤ ρ from hz.1)])
    exact hEL u unitCylinder z.1 z.2 ρ Mu Λ isOpen_unitCylinder_prod hρ hρ1
      (fun y hy => (hwin y z.2 (hball y hy) hz.2.1 hz.2.2).1) hcl.1 hcl.2.2.2.2
      (fun y hy => (hwin y z.2 (hball y hy) hz.2.1 hz.2.2).2.1)
      (fun y hy => (hwin y z.2 (hball y hy) hz.2.1 hz.2.2).2.2.2)
  have hc := contDiffOn_curlComp_unitCylinder hcl.1
  have hcomp : ∀ i j, |spatialPartial (curlComp u i) j (x, s)| ≤
      CH * (ρ * (2 * Mu * Λ + 2 * Ω₀ * V + Mf) + Ω₀ / ρ) := by
    intro i j
    refine hHB (fun z => spatialPartial (curlComp u i) j z)
      (fun l z => if l = j then curlComp u i z else 0)
      (fun m z => spatialPartial (serrinVortFlux u f i m) j z) unitCylinder x s ρ
      (2 * Mu * Λ + 2 * Ω₀ * V + Mf) Ω₀ isOpen_unitCylinder_prod hρ hρ1
      (fun z hz => (hwinρ z hz).1) (contDiffOn_spatialPartial (hc i) j)
      (fun l => by
        by_cases hl : l = j
        · simp only [hl, ite_true]; exact hc i
        · simp only [hl, ite_false]; exact contDiffOn_const)
      (fun m => contDiffOn_spatialPartial (contDiffOn_serrinVortFlux hcl i m) j)
      (fun z _ => (sum_spatialPartial_single (curlComp u i) j z).symm)
      (fun z hz => vorticity_first_derivative_equation hcl z hz i j) ?_ ?_
    · intro z hz m
      obtain ⟨hzQ, huz, hω0, hω1, hv1⟩ := hwinρ z hz
      rw [spatialPartial_serrinVortFlux_eq hcl hzQ i m j]
      have a1 := (abs_spatialPartial_curlComp_le_vortSum1 u z m j).trans hω1
      have a2 := (abs_curlComp_le_vortSum0 u z m).trans hω0
      have a3 := (abs_spatialPartial_le_velSum1 u z i j).trans hv1
      have a4 := (abs_spatialPartial_le_velSum1 u z m j).trans hv1
      have a5 := (abs_curlComp_le_vortSum0 u z i).trans hω0
      have a6 := (abs_spatialPartial_curlComp_le_vortSum1 u z i j).trans hω1
      have a7 := abs_spatialPartial_serrinForceFlux_le hMf0
        (fun k j' => abs_spatialPartial_force_le hMf hzQ k j') i m j
      calc _ ≤ |spatialPartial (curlComp u m) j z| * |u z i| +
            |curlComp u m z| * |spatialPartial (fun w => u w i) j z| +
            (|spatialPartial (fun w => u w m) j z| * |curlComp u i z| +
              |u z m| * |spatialPartial (curlComp u i) j z|) +
            |spatialPartial (serrinForceFlux f i m) j z| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
              (add_le_add ((abs_add_le _ _).trans (le_of_eq ?_))
                ((abs_add_le _ _).trans (le_of_eq ?_)))) le_rfl)
            · rw [abs_mul, abs_mul]
            · rw [abs_mul, abs_mul]
        _ ≤ Λ * Mu + Ω₀ * V + (V * Ω₀ + Mu * Λ) + Mf := by
            gcongr
            · exact huz i
            · exact huz m
        _ = 2 * Mu * Λ + 2 * Ω₀ * V + Mf := by ring
    · intro z hz l
      by_cases hl : l = j
      · simp only [hl, ite_true]
        exact (abs_curlComp_le_vortSum0 u z i).trans (hwinρ z hz).2.2.1
      · simp only [hl, ite_false, abs_zero]; exact hΩ₀
  have hsum : vortSum1 u (x, s) ≤ 9 * (CH * (ρ * (2 * Mu * Λ + 2 * Ω₀ * V + Mf) + Ω₀ / ρ)) := by
    unfold vortSum1
    calc ∑ i, ∑ j, |spatialPartial (curlComp u i) j (x, s)|
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, CH * (ρ * (2 * Mu * Λ + 2 * Ω₀ * V + Mf) + Ω₀ / ρ) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcomp i j))
      _ = 9 * (CH * (ρ * (2 * Mu * Λ + 2 * Ω₀ * V + Mf) + Ω₀ / ρ)) := by simp; ring
  refine hsum.trans ?_
  -- arithmetic
  have hρinv : ρ ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; nlinarith only [hρ, hρ1]
  have h1ρ : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith only [hρ1]
  set Q : ℝ := (1 + Mu + Ω₀ + Mf) ^ 2 with hQ
  have hQ1 : Ω₀ * Mu + Mf + Ω₀ ≤ Q := by
    rw [hQ]; nlinarith only [hMu, hΩ₀, hMf0, mul_nonneg hMu hΩ₀, mul_nonneg hMu hMf0,
      mul_nonneg hΩ₀ hMf0]
  have eV : ρ * (2 * Ω₀ * V) = 2 * CE * Ω₀ * (ρ * (ρ * Λ)) + 2 * CE * (Ω₀ * Mu) := by
    rw [hV]; field_simp
  have hρρ : ρ * (ρ * Λ) ≤ ρ * Λ := by
    have := mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hρ.le hΛ)
    linarith only [this]
  have hMfρ : ρ * Mf ≤ Mf / ρ := by
    rw [div_eq_mul_one_div, mul_comm Mf]; exact mul_le_mul_of_nonneg_right hρinv hMf0
  have hA : Ω₀ * Mu + Mf + Ω₀ ≤ Q / ρ := by
    calc Ω₀ * Mu + Mf + Ω₀ ≤ Q := hQ1
      _ ≤ Q / ρ := by
        rw [le_div_iff₀ hρ]
        have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
        nlinarith only [hQ0, hρ1, hρ]
  have hsplit : 9 * (CH * (ρ * (2 * Mu * Λ + 2 * Ω₀ * V + Mf) + Ω₀ / ρ)) =
      18 * CH * Mu * (ρ * Λ) + 18 * CH * CE * Ω₀ * (ρ * (ρ * Λ)) +
        9 * CH * (2 * CE * (Ω₀ * Mu) + ρ * Mf + Ω₀ / ρ) := by
    rw [show ρ * (2 * Mu * Λ + 2 * Ω₀ * V + Mf) =
      2 * Mu * (ρ * Λ) + ρ * (2 * Ω₀ * V) + ρ * Mf by ring, eV]
    ring
  rw [hsplit]
  have hT1 : 18 * CH * Mu * (ρ * Λ) + 18 * CH * CE * Ω₀ * (ρ * (ρ * Λ)) ≤
      18 * CH * (1 + CE) * (1 + Mu + Ω₀) * ρ * Λ := by
    have hρΛ : 0 ≤ ρ * Λ := mul_nonneg hρ.le hΛ
    have := mul_le_mul_of_nonneg_left hρρ (by positivity : (0 : ℝ) ≤ 18 * CH * CE * Ω₀)
    nlinarith only [this, hρΛ, mul_nonneg (mul_nonneg hCH.le hCE.le) hρΛ,
      mul_nonneg (mul_nonneg hCH.le hMu) hρΛ, mul_nonneg (mul_nonneg (mul_nonneg hCH.le hCE.le)
      hMu) hρΛ, mul_nonneg (mul_nonneg hCH.le hΩ₀) hρΛ, mul_nonneg hCH.le hρΛ]
  have hT2 : 9 * CH * (2 * CE * (Ω₀ * Mu) + ρ * Mf + Ω₀ / ρ) ≤
      18 * CH * (1 + CE) * Q / ρ := by
    have hΩρ : Ω₀ ≤ Ω₀ / ρ := by
      rw [le_div_iff₀ hρ]; nlinarith only [hΩ₀, hρ1, hρ]
    have hOMρ : Ω₀ * Mu ≤ Ω₀ * Mu / ρ := by
      rw [le_div_iff₀ hρ]; nlinarith only [mul_nonneg hΩ₀ hMu, hρ1, hρ]
    have hinner : 2 * CE * (Ω₀ * Mu) + ρ * Mf + Ω₀ / ρ ≤ 2 * (1 + CE) * (Q / ρ) := by
      have e : Q / ρ = Q * (1 / ρ) := div_eq_mul_one_div _ _
      have hB : Ω₀ * Mu / ρ + Mf / ρ + Ω₀ / ρ ≤ Q / ρ := by
        rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right hQ1 hρ.le
      nlinarith only [hB, hMfρ, hOMρ, hCE.le, mul_nonneg hCE.le (mul_nonneg hΩ₀ hMu),
        div_nonneg (mul_nonneg hΩ₀ hMu) hρ.le, div_nonneg hMf0 hρ.le, div_nonneg hΩ₀ hρ.le,
        mul_le_mul_of_nonneg_left hOMρ hCE.le, mul_nonneg hCE.le (div_nonneg hΩ₀ hρ.le),
        mul_nonneg hCE.le (div_nonneg hMf0 hρ.le), mul_nonneg hCE.le
        (div_nonneg (mul_nonneg hΩ₀ hMu) hρ.le)]
    calc 9 * CH * (2 * CE * (Ω₀ * Mu) + ρ * Mf + Ω₀ / ρ) ≤ 9 * CH * (2 * (1 + CE) * (Q / ρ)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 18 * CH * (1 + CE) * Q / ρ := by ring
  linarith only [hT1, hT2]

/-- The second-derivative bound of the force, in any order of the two partials. -/
theorem abs_spatialSecondPartial_force_le {f : ParabolicPoint → Vec3} {Mf : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) {z : ParabolicPoint} (hz : z ∈ unitCylinder)
    (k j l : Fin 3) :
    |spatialPartial (fun w => spatialPartial (fun w' => f w' k) j w) l z| ≤ Mf := by
  have hfk : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z k) unitCylinder :=
    (contDiffOn_pi.mp hf) k
  have hcomm : ∀ a b : Fin 3,
      spatialPartial (fun w => spatialPartial (fun w' => f w' k) a w) b z =
        spatialPartial (fun w => spatialPartial (fun w' => f w' k) b w) a z :=
    fun a b => spatialSecondPartial_comm hfk hz a b
  -- the multi-index derivative with `α = e_a + e_b`, `a ≤ b`, is `∂_a ∂_b`
  have key : ∀ a b : Fin 3, a ≤ b →
      |spatialPartial (fun w => spatialPartial (fun w' => f w' k) b w) a z| ≤ Mf := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | exact absurd hab (by decide)
      | (have h := hMf z hz k ![2, 0, 0] (by decide); simpa [multiPartial] using h)
      | (have h := hMf z hz k ![1, 1, 0] (by decide); simpa [multiPartial] using h)
      | (have h := hMf z hz k ![1, 0, 1] (by decide); simpa [multiPartial] using h)
      | (have h := hMf z hz k ![0, 2, 0] (by decide); simpa [multiPartial] using h)
      | (have h := hMf z hz k ![0, 1, 1] (by decide); simpa [multiPartial] using h)
      | (have h := hMf z hz k ![0, 0, 2] (by decide); simpa [multiPartial] using h)
  rcases le_total l j with h | h
  · exact key l j h
  · rw [hcomm]; exact key j l h

/-- Each second derivative of the vorticity is bounded by the level-two sum. -/
theorem abs_spatialPartial2_curlComp_le_vortSum2 (u : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (i j l : Fin 3) :
    |spatialPartial (fun w => spatialPartial (curlComp u i) j w) l z| ≤ vortSum2 u z := by
  unfold vortSum2
  calc _ ≤ ∑ l', |spatialPartial (fun w => spatialPartial (curlComp u i) j w) l' z| :=
        Finset.single_le_sum (f := fun l' =>
          |spatialPartial (fun w => spatialPartial (curlComp u i) j w) l' z|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    _ ≤ ∑ j', ∑ l', |spatialPartial (fun w => spatialPartial (curlComp u i) j' w) l' z| :=
        Finset.single_le_sum (f := fun j' => ∑ l',
          |spatialPartial (fun w => spatialPartial (curlComp u i) j' w) l' z|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ j)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ∑ l',
          |spatialPartial (fun w => spatialPartial (curlComp u i') j' w) l' z|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
          (Finset.mem_univ i)

/-- Each second derivative of the velocity is bounded by the level-two velocity sum. -/
theorem abs_spatialPartial2_le_velSum2 (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (i j l : Fin 3) :
    |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l z| ≤ velSum2 u z := by
  unfold velSum2
  calc _ ≤ ∑ l', |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l' z| :=
        Finset.single_le_sum (f := fun l' =>
          |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l' z|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    _ ≤ ∑ j', ∑ l', |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j' w) l' z| :=
        Finset.single_le_sum (f := fun j' => ∑ l',
          |spatialPartial (fun w => spatialPartial (fun w' => u w' i) j' w) l' z|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ j)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ∑ l',
          |spatialPartial (fun w => spatialPartial (fun w' => u w' i') j' w) l' z|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
          (Finset.mem_univ i)

/-- The second derivative of the antisymmetric flux of the force is bounded by `Mf`. -/
theorem abs_spatialPartial2_serrinForceFlux_le {f : ParabolicPoint → Vec3} {Mf : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) (hMf0 : 0 ≤ Mf) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i m j l : Fin 3) :
    |spatialPartial (fun w => spatialPartial (serrinForceFlux f i m) j w) l z| ≤ Mf := by
  have hneg : ∀ (g : ParabolicPoint → ℝ) (a : Fin 3),
      (fun w => spatialPartial (fun w' => -g w') a w) = fun w => -spatialPartial g a w := by
    intro g a; funext w; unfold spatialPartial; rw [fderiv_fun_neg]; rfl
  unfold serrinForceFlux
  split_ifs
  · exact abs_spatialSecondPartial_force_le hf hMf hz _ j l
  · rw [hneg, congrFun (hneg (fun w => spatialPartial (fun z => f z (i + 1)) j w) l) z, abs_neg]
    exact abs_spatialSecondPartial_force_le hf hMf hz _ j l
  · have e : (fun w : ParabolicPoint => spatialPartial (fun _ => (0 : ℝ)) j w) = fun _ => 0 := by
      funext w; unfold spatialPartial; simp
    rw [e]
    have e2 : spatialPartial (fun _ : ParabolicPoint => (0 : ℝ)) l z = 0 := by
      unfold spatialPartial; simp
    rw [e2, abs_zero]; exact hMf0

/-- Bound for the second spatial derivative of the divergence-form flux. -/
theorem abs_spatialPartial2_serrinVortFlux_le {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hcl : IsClassicalSolutionOn u p f unitCylinder) {Mf : ℝ}
    (hMf : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) (hMf0 : 0 ≤ Mf) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) {Mu Ω₀ Ω₁ V₁ L₂ V₂ : ℝ}
    (hu : ∀ k, |u z k| ≤ Mu) (hω0 : ∀ k, |curlComp u k z| ≤ Ω₀)
    (hω1 : ∀ k a, |spatialPartial (curlComp u k) a z| ≤ Ω₁)
    (hv1 : ∀ k a, |spatialPartial (fun w => u w k) a z| ≤ V₁)
    (hω2 : ∀ k a b, |spatialPartial (fun w => spatialPartial (curlComp u k) a w) b z| ≤ L₂)
    (hv2 : ∀ k a b, |spatialPartial (fun w => spatialPartial (fun w' => u w' k) a w) b z| ≤ V₂)
    (i m j l : Fin 3) :
    |spatialPartial (fun w => spatialPartial (serrinVortFlux u f i m) j w) l z| ≤
      2 * Mu * L₂ + 4 * Ω₁ * V₁ + 2 * Ω₀ * V₂ + Mf := by
  have hc := contDiffOn_curlComp_unitCylinder hcl.1
  have huk : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z k) unitCylinder :=
    fun k => (contDiffOn_pi.mp hcl.1) k
  have hdc : ∀ k a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (curlComp u k) a z) unitCylinder :=
    fun k a => contDiffOn_spatialPartial (hc k) a
  have hdu : ∀ k a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w k) a z) unitCylinder :=
    fun k a => contDiffOn_spatialPartial (huk k) a
  have hdF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (serrinForceFlux f i m) j z) unitCylinder :=
    contDiffOn_spatialPartial (contDiffOn_serrinForceFlux hcl.2.2.1 i m) j
  -- the first-derivative expansion holds on the open cylinder, so its derivative can be taken
  set E : ParabolicPoint → ℝ := fun w =>
    (spatialPartial (curlComp u m) j w * u w i +
        curlComp u m w * spatialPartial (fun w' => u w' i) j w) -
      (spatialPartial (fun w' => u w' m) j w * curlComp u i w +
        u w m * spatialPartial (curlComp u i) j w) +
      spatialPartial (serrinForceFlux f i m) j w with hE
  have hcongr : spatialPartial (fun w => spatialPartial (serrinVortFlux u f i m) j w) l z =
      spatialPartial E l z :=
    spatialPartial_congr_of_eqOn_spaceTimeSet (isOpen_vec3Ball 0 1) isOpen_Ioo
      (fun w hw => spatialPartial_serrinVortFlux_eq hcl hw i m j) hz l
  rw [hcongr]
  set P1 : ParabolicPoint → ℝ := fun w => spatialPartial (curlComp u m) j w * u w i with hP1d
  set P2 : ParabolicPoint → ℝ := fun w => curlComp u m w * spatialPartial (fun w' => u w' i) j w
    with hP2d
  set P3 : ParabolicPoint → ℝ := fun w => spatialPartial (fun w' => u w' m) j w * curlComp u i w
    with hP3d
  set P4 : ParabolicPoint → ℝ := fun w => u w m * spatialPartial (curlComp u i) j w with hP4d
  set P5 : ParabolicPoint → ℝ := spatialPartial (serrinForceFlux f i m) j with hP5d
  have hP1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => P1 w) unitCylinder := (hdc m j).mul (huk i)
  have hP2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => P2 w) unitCylinder := (hc m).mul (hdu i j)
  have hP3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => P3 w) unitCylinder := (hdu m j).mul (hc i)
  have hP4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => P4 w) unitCylinder := (huk m).mul (hdc i j)
  have hP5 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => P5 w) unitCylinder := hdF
  have d : ∀ {g : ParabolicPoint → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z)
      unitCylinder → DifferentiableAt ℝ (fun y : Vec3 => g (y, z.2)) z.1 :=
    fun hg => differentiableAt_spatialSlice (hg.of_le (by norm_num)) hz
  have eE : E = fun w => (P1 w + P2 w) - (P3 w + P4 w) + P5 w := rfl
  rw [eE, spatialPartial_add_of_differentiableAt (g := fun w => (P1 w + P2 w) - (P3 w + P4 w))
      (h := P5) (((d hP1).add (d hP2)).sub ((d hP3).add (d hP4))) (d hP5),
    spatialPartial_sub_of_differentiableAt (g := fun w => P1 w + P2 w) (h := fun w => P3 w + P4 w)
      ((d hP1).add (d hP2)) ((d hP3).add (d hP4)),
    spatialPartial_add_of_differentiableAt (g := P1) (h := P2) (d hP1) (d hP2),
    spatialPartial_add_of_differentiableAt (g := P3) (h := P4) (d hP3) (d hP4),
    hP1d, hP2d, hP3d, hP4d,
    spatialPartial_mul_of_contDiffOn (hdc m j) (huk i) hz l,
    spatialPartial_mul_of_contDiffOn (hc m) (hdu i j) hz l,
    spatialPartial_mul_of_contDiffOn (hdu m j) (hc i) hz l,
    spatialPartial_mul_of_contDiffOn (huk m) (hdc i j) hz l]
  have hF2 := abs_spatialPartial2_serrinForceFlux_le hcl.2.2.1 hMf hMf0 hz i m j l
  have hMu0 : 0 ≤ Mu := (abs_nonneg _).trans (hu 0)
  have hΩ0 : 0 ≤ Ω₀ := (abs_nonneg _).trans (hω0 0)
  have hΩ1 : 0 ≤ Ω₁ := (abs_nonneg _).trans (hω1 0 0)
  have hV1 : 0 ≤ V₁ := (abs_nonneg _).trans (hv1 0 0)
  set a1 := spatialPartial (fun w => spatialPartial (curlComp u m) j w) l z
  set a2 := spatialPartial (curlComp u m) j z
  set a3 := spatialPartial (fun w => u w i) l z
  set a4 := spatialPartial (curlComp u m) l z
  set a5 := spatialPartial (fun w' => u w' i) j z
  set a6 := spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) l z
  set b1 := spatialPartial (fun w => spatialPartial (fun w' => u w' m) j w) l z
  set b2 := spatialPartial (fun w' => u w' m) j z
  set b3 := spatialPartial (curlComp u i) l z
  set b4 := spatialPartial (fun w => u w m) l z
  set b5 := spatialPartial (curlComp u i) j z
  set b6 := spatialPartial (fun w => spatialPartial (curlComp u i) j w) l z
  set F2 := spatialPartial (fun w => spatialPartial (serrinForceFlux f i m) j w) l z
  have ha1 : |a1| ≤ L₂ := hω2 m j l
  have ha2 : |a2| ≤ Ω₁ := hω1 m j
  have ha3 : |a3| ≤ V₁ := hv1 i l
  have ha4 : |a4| ≤ Ω₁ := hω1 m l
  have ha5 : |a5| ≤ V₁ := hv1 i j
  have ha6 : |a6| ≤ V₂ := hv2 i j l
  have hb1 : |b1| ≤ V₂ := hv2 m j l
  have hb2 : |b2| ≤ V₁ := hv1 m j
  have hb3 : |b3| ≤ Ω₁ := hω1 i l
  have hb4 : |b4| ≤ V₁ := hv1 m l
  have hb5 : |b5| ≤ Ω₁ := hω1 i j
  have hb6 : |b6| ≤ L₂ := hω2 i j l
  have hui := hu i
  have hum := hu m
  have hωm := hω0 m
  have hωi := hω0 i
  have t1 : |a1 * u z i + a2 * a3| ≤ L₂ * Mu + Ω₁ * V₁ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul ha1 hui (abs_nonneg _) ((abs_nonneg _).trans ha1)
    · exact mul_le_mul ha2 ha3 (abs_nonneg _) hΩ1
  have t2 : |a4 * spatialPartial (fun w' => u w' i) j z + curlComp u m z * a6| ≤
      Ω₁ * V₁ + Ω₀ * V₂ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul ha4 ha5 (abs_nonneg _) hΩ1
    · exact mul_le_mul hωm ha6 (abs_nonneg _) hΩ0
  have t3 : |b1 * curlComp u i z + b2 * b3| ≤ V₂ * Ω₀ + V₁ * Ω₁ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul hb1 hωi (abs_nonneg _) ((abs_nonneg _).trans hb1)
    · exact mul_le_mul hb2 hb3 (abs_nonneg _) hV1
  have t4 : |b4 * spatialPartial (curlComp u i) j z + u z m * b6| ≤ V₁ * Ω₁ + Mu * L₂ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul hb4 hb5 (abs_nonneg _) hV1
    · exact mul_le_mul hum hb6 (abs_nonneg _) hMu0
  calc |a1 * u z i + a2 * a3 + (a4 * spatialPartial (fun w' => u w' i) j z +
        curlComp u m z * a6) - (b1 * curlComp u i z + b2 * b3 +
        (b4 * spatialPartial (curlComp u i) j z + u z m * b6)) + F2|
      ≤ (L₂ * Mu + Ω₁ * V₁ + (Ω₁ * V₁ + Ω₀ * V₂)) +
          (V₂ * Ω₀ + V₁ * Ω₁ + (V₁ * Ω₁ + Mu * L₂)) + Mf := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add t1 t2))
          ((abs_add_le _ _).trans (add_le_add t3 t4)))) hF2)
    _ = 2 * Mu * L₂ + 4 * Ω₁ * V₁ + 2 * Ω₀ * V₂ + Mf := by ring

/-- The local step at level two. -/
theorem LS2_local_level2 : ∃ C : ℝ, 0 < C ∧ ∀ (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
    IsClassicalSolutionOn u p f unitCylinder → ∀ Mf Mu Ω₀ Ω₁ V₁ : ℝ,
    (∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ Mf) →
    ∀ (x : Vec3) (s ρ Λ : ℝ), 0 < ρ → ρ ≤ 1 →
    (∀ (y : Vec3) (s' : ℝ), vec3EuclideanNorm (y - x) ≤ 2 * ρ → s - ρ ^ 2 ≤ s' → s' ≤ s →
      (y, s') ∈ unitCylinder ∧ (∀ i, |u (y, s') i| ≤ Mu) ∧ vortSum0 u (y, s') ≤ Ω₀ ∧
        vortSum1 u (y, s') ≤ Ω₁ ∧ velSum1 u (y, s') ≤ V₁ ∧ vortSum2 u (y, s') ≤ Λ) →
    vortSum2 u (x, s) ≤
      C * (1 + Mu + Ω₀) * ρ * Λ + C * (1 + Mu + Ω₀ + Ω₁ + V₁ + Mf) ^ 2 / ρ := by
  obtain ⟨CH, hCH, hHB⟩ := serrin_heat_pointwise_bound
  obtain ⟨CE, hCE, hEL⟩ := EL2_local
  refine ⟨108 * CH * (1 + CE), by positivity, ?_⟩
  intro u p f hcl Mf Mu Ω₀ Ω₁ V₁ hMf x s ρ Λ hρ hρ1 hwin
  have hs2 : s - ρ ^ 2 ≤ s := by have := sq_nonneg ρ; linarith only [this]
  have hx0 : vec3EuclideanNorm (x - x) ≤ 2 * ρ := by
    rw [sub_self, vec3EuclideanNorm_zero]; positivity
  obtain ⟨hxQ, hux, hω0x, hω1x, hv1x, hω2x⟩ := hwin x s hx0 hs2 le_rfl
  have hMu : 0 ≤ Mu := (abs_nonneg _).trans (hux 0)
  have hΩ₀ : 0 ≤ Ω₀ := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans hω0x
  have hΩ₁ : 0 ≤ Ω₁ := (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans hω1x
  have hV₁ : 0 ≤ V₁ := (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans hv1x
  have hΛ : 0 ≤ Λ := (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)))).trans hω2x
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf _ hxQ 0 0 (by simp))
  set V₂ : ℝ := CE * (ρ * Λ + Mu / ρ ^ 2) with hV₂
  have hV₂0 : 0 ≤ V₂ := by positivity
  have hwinρ : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s,
      z ∈ unitCylinder ∧ (∀ i, |u z i| ≤ Mu) ∧ vortSum0 u z ≤ Ω₀ ∧ vortSum1 u z ≤ Ω₁ ∧
        velSum1 u z ≤ V₁ ∧ vortSum2 u z ≤ Λ ∧ velSum2 u z ≤ V₂ := by
    intro z hz
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      hwin z.1 z.2 (hz.1.trans (by linarith only [hρ])) hz.2.1 hz.2.2
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    have hball : ∀ y : Vec3, vec3EuclideanNorm (y - z.1) ≤ ρ →
        vec3EuclideanNorm (y - x) ≤ 2 * ρ := fun y hy =>
      (vec3EuclideanNorm_sub_le_add x y z.1).trans (by
        linarith only [hy, (show vec3EuclideanNorm (z.1 - x) ≤ ρ from hz.1)])
    exact hEL u unitCylinder z.1 z.2 ρ Mu Λ isOpen_unitCylinder_prod hρ hρ1
      (fun y hy => (hwin y z.2 (hball y hy) hz.2.1 hz.2.2).1) hcl.1 hcl.2.2.2.2
      (fun y hy => (hwin y z.2 (hball y hy) hz.2.1 hz.2.2).2.1)
      (fun y hy => (hwin y z.2 (hball y hy) hz.2.1 hz.2.2).2.2.2.2.2)
  have hc := contDiffOn_curlComp_unitCylinder hcl.1
  have hcomp : ∀ i j l, |spatialPartial (fun w => spatialPartial (curlComp u i) j w) l (x, s)| ≤
      CH * (ρ * (2 * Mu * Λ + 4 * Ω₁ * V₁ + 2 * Ω₀ * V₂ + Mf) + Ω₁ / ρ) := by
    intro i j l
    refine hHB (fun z => spatialPartial (fun w' => spatialPartial (curlComp u i) j w') l z)
      (fun l' z => if l' = l then spatialPartial (curlComp u i) j z else 0)
      (fun m z => spatialPartial (fun w' => spatialPartial (serrinVortFlux u f i m) j w') l z)
      unitCylinder x s ρ (2 * Mu * Λ + 4 * Ω₁ * V₁ + 2 * Ω₀ * V₂ + Mf) Ω₁
      isOpen_unitCylinder_prod hρ hρ1 (fun z hz => (hwinρ z hz).1)
      (contDiffOn_spatialPartial (contDiffOn_spatialPartial (hc i) j) l)
      (fun l' => by
        by_cases hl : l' = l
        · simp only [hl, ite_true]; exact contDiffOn_spatialPartial (hc i) j
        · simp only [hl, ite_false]; exact contDiffOn_const)
      (fun m => contDiffOn_spatialPartial
        (contDiffOn_spatialPartial (contDiffOn_serrinVortFlux hcl i m) j) l)
      (fun z _ => (sum_spatialPartial_single (fun w => spatialPartial (curlComp u i) j w) l z).symm)
      (fun z hz => vorticity_second_derivative_equation hcl z hz i j l) ?_ ?_
    · intro z hz m
      obtain ⟨hzQ, huz, hω0, hω1, hv1, hω2, hv2⟩ := hwinρ z hz
      exact abs_spatialPartial2_serrinVortFlux_le hcl hMf hMf0 hzQ huz
        (fun k => (abs_curlComp_le_vortSum0 u z k).trans hω0)
        (fun k a => (abs_spatialPartial_curlComp_le_vortSum1 u z k a).trans hω1)
        (fun k a => (abs_spatialPartial_le_velSum1 u z k a).trans hv1)
        (fun k a b => (abs_spatialPartial2_curlComp_le_vortSum2 u z k a b).trans hω2)
        (fun k a b => (abs_spatialPartial2_le_velSum2 u z k a b).trans hv2) i m j l
    · intro z hz l'
      by_cases hl : l' = l
      · simp only [hl, ite_true]
        exact (abs_spatialPartial_curlComp_le_vortSum1 u z i j).trans (hwinρ z hz).2.2.2.1
      · simp only [hl, ite_false, abs_zero]; exact hΩ₁
  set T : ℝ := CH * (ρ * (2 * Mu * Λ + 4 * Ω₁ * V₁ + 2 * Ω₀ * V₂ + Mf) + Ω₁ / ρ) with hT
  have hsum : vortSum2 u (x, s) ≤ 27 * T := by
    unfold vortSum2
    calc ∑ i, ∑ j, ∑ l, |spatialPartial (fun w => spatialPartial (curlComp u i) j w) l (x, s)|
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _l : Fin 3, T :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
            Finset.sum_le_sum (fun l _ => hcomp i j l)))
      _ = 27 * T := by simp; ring
  refine hsum.trans ?_
  -- arithmetic
  have hρinv : ρ ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; nlinarith only [hρ, hρ1]
  set Q : ℝ := (1 + Mu + Ω₀ + Ω₁ + V₁ + Mf) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hQ1 : Ω₁ * V₁ + Ω₀ * Mu + Mf + Ω₁ ≤ Q := by
    rw [hQ]
    nlinarith only [hMu, hΩ₀, hΩ₁, hV₁, hMf0, mul_nonneg hΩ₁ hV₁, mul_nonneg hΩ₀ hMu,
      mul_nonneg hMu hΩ₁, mul_nonneg hMu hV₁, mul_nonneg hMu hMf0, mul_nonneg hΩ₀ hΩ₁,
      mul_nonneg hΩ₀ hV₁, mul_nonneg hΩ₀ hMf0, mul_nonneg hΩ₁ hMf0, mul_nonneg hV₁ hMf0]
  have eV : ρ * (2 * Ω₀ * V₂) = 2 * CE * Ω₀ * (ρ * (ρ * Λ)) + 2 * CE * (Ω₀ * Mu / ρ) := by
    rw [hV₂]; field_simp
  have hρρ : ρ * (ρ * Λ) ≤ ρ * Λ := by
    have := mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hρ.le hΛ)
    linarith only [this]
  have hsplit : 27 * T = 54 * CH * Mu * (ρ * Λ) + 54 * CH * CE * Ω₀ * (ρ * (ρ * Λ)) +
      27 * CH * (4 * (ρ * (Ω₁ * V₁)) + 2 * CE * (Ω₀ * Mu / ρ) + ρ * Mf + Ω₁ / ρ) := by
    rw [hT, show ρ * (2 * Mu * Λ + 4 * Ω₁ * V₁ + 2 * Ω₀ * V₂ + Mf) =
      2 * Mu * (ρ * Λ) + 4 * (ρ * (Ω₁ * V₁)) + ρ * (2 * Ω₀ * V₂) + ρ * Mf by ring, eV]
    ring
  rw [hsplit]
  have hρΛ : 0 ≤ ρ * Λ := mul_nonneg hρ.le hΛ
  have hT1 : 54 * CH * Mu * (ρ * Λ) + 54 * CH * CE * Ω₀ * (ρ * (ρ * Λ)) ≤
      108 * CH * (1 + CE) * (1 + Mu + Ω₀) * ρ * Λ := by
    have := mul_le_mul_of_nonneg_left hρρ (by positivity : (0 : ℝ) ≤ 54 * CH * CE * Ω₀)
    nlinarith only [this, hρΛ, mul_nonneg (mul_nonneg hCH.le hCE.le) hρΛ,
      mul_nonneg (mul_nonneg hCH.le hMu) hρΛ, mul_nonneg (mul_nonneg (mul_nonneg hCH.le hCE.le)
      hMu) hρΛ, mul_nonneg (mul_nonneg hCH.le hΩ₀) hρΛ, mul_nonneg hCH.le hρΛ,
      mul_nonneg (mul_nonneg (mul_nonneg hCH.le hCE.le) hΩ₀) hρΛ]
  have hT2 : 27 * CH * (4 * (ρ * (Ω₁ * V₁)) + 2 * CE * (Ω₀ * Mu / ρ) + ρ * Mf + Ω₁ / ρ) ≤
      108 * CH * (1 + CE) * Q / ρ := by
    have hdiv : ∀ a : ℝ, 0 ≤ a → ρ * a ≤ a / ρ := fun a ha => by
      rw [div_eq_mul_one_div, mul_comm a]; exact mul_le_mul_of_nonneg_right hρinv ha
    have h1 := hdiv (Ω₁ * V₁) (mul_nonneg hΩ₁ hV₁)
    have h2 := hdiv Mf hMf0
    have hB : Ω₁ * V₁ / ρ + Ω₀ * Mu / ρ + Mf / ρ + Ω₁ / ρ ≤ Q / ρ := by
      rw [← add_div, ← add_div, ← add_div]; exact div_le_div_of_nonneg_right hQ1 hρ.le
    have hinner : 4 * (ρ * (Ω₁ * V₁)) + 2 * CE * (Ω₀ * Mu / ρ) + ρ * Mf + Ω₁ / ρ ≤
        4 * (1 + CE) * (Q / ρ) := by
      have p1 : 0 ≤ Ω₁ * V₁ / ρ := div_nonneg (mul_nonneg hΩ₁ hV₁) hρ.le
      have p2 : 0 ≤ Ω₀ * Mu / ρ := div_nonneg (mul_nonneg hΩ₀ hMu) hρ.le
      have p3 : 0 ≤ Mf / ρ := div_nonneg hMf0 hρ.le
      have p4 : 0 ≤ Ω₁ / ρ := div_nonneg hΩ₁ hρ.le
      nlinarith only [hB, h1, h2, hCE.le, p1, p2, p3, p4, mul_nonneg hCE.le p1,
        mul_nonneg hCE.le p2, mul_nonneg hCE.le p3, mul_nonneg hCE.le p4]
    calc 27 * CH * (4 * (ρ * (Ω₁ * V₁)) + 2 * CE * (Ω₀ * Mu / ρ) + ρ * Mf + Ω₁ / ρ)
        ≤ 27 * CH * (4 * (1 + CE) * (Q / ρ)) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 108 * CH * (1 + CE) * Q / ρ := by ring
  linarith only [hT1, hT2]

end CIV
