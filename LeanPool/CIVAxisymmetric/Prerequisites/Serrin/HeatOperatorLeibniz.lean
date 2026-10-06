/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation

/-!
# The Leibniz rule for the heat operator

The heat operator `∂ₜ - Δ` obeys a product rule on any open set where both factors are jointly
smooth: `(∂ₜ - Δ)(χ w) = χ (∂ₜ - Δ) w + w (∂ₜ - Δ) χ - 2 ∇χ · ∇w`. This is the pointwise identity
that expands the cutoff-and-heat-kernel product in the interior estimates of the proof of
`lem:aniso:annulus`, before the divergence term coming from `w`'s own equation is substituted in.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- If a scalar field is jointly smooth on an open set `O`, so is each of its classical
spatial partial derivatives, on the same `O`. -/
private theorem contDiffOn_spatialPartial_open {g : ParabolicPoint → ℝ} {O : Set ParabolicPoint}
    (hO : IsOpen (X := Vec3 × ℝ) O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g i z) O := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z : Vec3 × ℝ => g z)) O :=
    hg.fderiv_of_isOpen hO (by norm_num)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => g w) z) (basisVec i, (0 : ℝ))) O :=
    hD.clm_apply contDiffOn_const
  refine hE.congr fun z hz => ?_
  exact spatialPartial_eq_jointFDeriv
    ((hg.differentiableOn (by norm_num) z hz).differentiableAt (hO.mem_nhds hz)) i

/-- Pointwise agreement of two scalar fields on a neighbourhood transports a spatial partial
derivative. -/
private theorem spatialPartial_congr_of_eventuallyEq {v u : ParabolicPoint → ℝ}
    {z : Vec3 × ℝ} (h : ∀ᶠ w : Vec3 × ℝ in nhds z, v w = u w) (j : Fin 3) :
    spatialPartial v j z = spatialPartial u j z := by
  change fderiv ℝ (fun y : Vec3 => v (y, z.2)) z.1 (basisVec j)
    = fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (basisVec j)
  have hcont : Continuous (fun y : Vec3 => ((y, z.2) : Vec3 × ℝ)) := by fun_prop
  have hev : (fun y : Vec3 => v (y, z.2)) =ᶠ[nhds z.1] (fun y : Vec3 => u (y, z.2)) :=
    (hcont.continuousAt (x := z.1)).tendsto.eventually h
  rw [hev.fderiv_eq]

/-- The classical differentiable-slice hypothesis at a point of an open set `O` where a scalar
field is jointly smooth. -/
private theorem differentiableAt_slice_fst_of_contDiffOn {g : ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} (hO : IsOpen (X := Vec3 × ℝ) O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) {z : ParabolicPoint} (hz : z ∈ O) :
    DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) z.1 :=
  ((hg.differentiableOn (by norm_num) z hz).differentiableAt (hO.mem_nhds hz)).comp z.1
    (by fun_prop)

private theorem differentiableAt_slice_snd_of_contDiffOn {g : ParabolicPoint → ℝ}
    {O : Set ParabolicPoint} (hO : IsOpen (X := Vec3 × ℝ) O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) O) {z : ParabolicPoint} (hz : z ∈ O) :
    DifferentiableAt ℝ (fun t : ℝ => g (z.1, t)) z.2 :=
  ((hg.differentiableOn (by norm_num) z hz).differentiableAt (hO.mem_nhds hz)).comp z.2
    (by fun_prop)

/-- The Leibniz rule for the heat operator `∂ₜ - Δ` applied to a product of two functions that
are jointly smooth on a common open set (the corresponding statement, the cutoff-decomposition
step of the
proof of `lem:aniso:annulus`). -/
theorem HB2a_heat_operator_mul {χ w : ParabolicPoint → ℝ} {O : Set ParabolicPoint}
    (hO : IsOpen (X := Vec3 × ℝ) O)
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => χ z) O)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) O) :
    ∀ z ∈ O,
      timePartial (fun v => χ v * w v) z - ∑ i, spatialSecondPartial (fun v => χ v * w v) i i z =
        χ z * (timePartial w z - ∑ i, spatialSecondPartial w i i z) +
          w z * (timePartial χ z - ∑ i, spatialSecondPartial χ i i z) -
          2 * ∑ i, spatialPartial χ i z * spatialPartial w i z := by
  intro z hz
  have hχt := differentiableAt_slice_snd_of_contDiffOn hO hχ hz
  have hwt := differentiableAt_slice_snd_of_contDiffOn hO hw hz
  have htime : timePartial (fun v => χ v * w v) z =
      χ z * timePartial w z + w z * timePartial χ z :=
    timePartial_mul_of_differentiableAt hχt hwt
  have hχO_i : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial χ i z) O :=
    fun i => contDiffOn_spatialPartial_open hO hχ i
  have hwO_i : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial w i z) O :=
    fun i => contDiffOn_spatialPartial_open hO hw i
  have hsecond : ∀ i : Fin 3,
      spatialSecondPartial (fun v => χ v * w v) i i z =
        spatialSecondPartial χ i i z * w z + 2 * spatialPartial χ i z * spatialPartial w i z +
          χ z * spatialSecondPartial w i i z := by
    intro i
    have hmulEqOn : ∀ v ∈ O, spatialPartial (fun u => χ u * w u) i v =
        spatialPartial χ i v * w v + χ v * spatialPartial w i v := by
      intro v hv
      have hχv := differentiableAt_slice_fst_of_contDiffOn hO hχ hv
      have hwv := differentiableAt_slice_fst_of_contDiffOn hO hw hv
      rw [spatialPartial_mul_of_differentiableAt hχv hwv]
      ring
    have hmulEv : ∀ᶠ v : Vec3 × ℝ in nhds z, spatialPartial (fun u => χ u * w u) i v =
        spatialPartial χ i v * w v + χ v * spatialPartial w i v :=
      Filter.eventually_of_mem (hO.mem_nhds hz) hmulEqOn
    have houter : spatialSecondPartial (fun v => χ v * w v) i i z =
        spatialPartial (fun v => spatialPartial χ i v * w v + χ v * spatialPartial w i v) i z :=
      spatialPartial_congr_of_eventuallyEq hmulEv i
    have hχ'v := differentiableAt_slice_fst_of_contDiffOn hO (hχO_i i) hz
    have hw'v := differentiableAt_slice_fst_of_contDiffOn hO (hwO_i i) hz
    have hχv := differentiableAt_slice_fst_of_contDiffOn hO hχ hz
    have hwv := differentiableAt_slice_fst_of_contDiffOn hO hw hz
    have hsplit : spatialPartial (fun v => spatialPartial χ i v * w v + χ v * spatialPartial w i v)
        i z = spatialPartial (fun v => spatialPartial χ i v * w v) i z +
          spatialPartial (fun v => χ v * spatialPartial w i v) i z :=
      spatialPartial_add_of_differentiableAt (hχ'v.mul hwv) (hχv.mul hw'v)
    have hmul1 : spatialPartial (fun v => spatialPartial χ i v * w v) i z =
        spatialPartial χ i z * spatialPartial w i z + w z * spatialSecondPartial χ i i z :=
      spatialPartial_mul_of_differentiableAt hχ'v hwv
    have hmul2 : spatialPartial (fun v => χ v * spatialPartial w i v) i z =
        χ z * spatialSecondPartial w i i z + spatialPartial w i z * spatialPartial χ i z :=
      spatialPartial_mul_of_differentiableAt hχv hw'v
    rw [houter, hsplit, hmul1, hmul2]
    ring
  have hsumsecond : ∑ i : Fin 3, spatialSecondPartial (fun v => χ v * w v) i i z =
      (∑ i : Fin 3, spatialSecondPartial χ i i z) * w z +
        2 * ∑ i : Fin 3, spatialPartial χ i z * spatialPartial w i z +
        χ z * ∑ i : Fin 3, spatialSecondPartial w i i z := by
    rw [Finset.sum_congr rfl (fun i _ => hsecond i)]
    simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
      mul_assoc]
  rw [htime, hsumsecond]
  ring

end CIV
