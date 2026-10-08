/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierContract
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierKernel
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData

/-!
# Scale-independent Sobolev contraction

The physical kernel of the regularized equation contracts the ordered
integer Sobolev energy of each velocity component. The estimate has
constant one and is independent of the mollifier scale.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The regularization kernel contracts the scalar ordered `H^m`
energy (`eq:lps-Hm-energy`). -/
theorem lps_regKernel_sobolevNormSq_le
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α f) 2 volume)
    (m : ℕ) :
    sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε) f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ≤
      sobolevNormSqOn m univ (fun α => wordDeriv α f) := by
  obtain ⟨hsmooth, hcompact, hnonneg, hone⟩ :=
    lps_regUniformMollifierKernel_properties ρ ε hε
  exact lps_sobolevNormSq_convolution_le
    hsmooth hcompact hnonneg hone hf hfL2 m

/-- The regularization kernel contracts the velocity's summed ordered
`H^m` energy (`eq:lps-Hm-energy`). -/
theorem lps_regKernel_vector_sobolevNormSq_le
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {u : Vec3 → Vec3}
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x => u x i)) 2 volume)
    (m : ℕ) :
    (∑ i : Fin 3, sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
          (fun x => u x i) (ContinuousLinearMap.lsmul ℝ ℝ) volume))) ≤
    ∑ i : Fin 3, sobolevNormSqOn m univ
      (fun α => wordDeriv α (fun x => u x i)) := by
  apply Finset.sum_le_sum
  intro i _
  exact lps_regKernel_sobolevNormSq_le ρ ε hε (hu i) (huL2 i) m

/-- On each time slice, the regularized transport velocity is exactly
convolution by the physical scalar kernel (`eq:reg-mollifier` of the CKN manuscript). -/
theorem lps_regUniformMollifiedVelocity_component_convolution
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (x : Vec3) (i : Fin 3) :
    CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i =
      convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
        (fun y : Vec3 => u (y, t) i)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  change CKN.Leray.regUniformMollifiedInitial ρ ε hε
    (fun y : Vec3 => u (y, t)) x i = _
  exact CKN.Leray.regUniformMollifiedInitial_component_convolution
    ρ ε hε hu x i

/-- A smooth velocity slice with square-integrable ordered derivatives
has a smooth mollified slice with the same `L²` derivative property
(`eq:lps-Hm-energy`). -/
theorem lps_regUniformMollifiedVelocity_smooth_memLp
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hsmooth : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume) :
    (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i)) ∧
    (∀ (i : Fin 3) (α : List (Fin 3)), MemLp
      (wordDeriv α
        (fun x : Vec3 => CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i))
      2 volume) := by
  obtain ⟨hκ, hκc, hκnonneg, hκone⟩ :=
    lps_regUniformMollifierKernel_properties ρ ε hε
  have hcomp (i : Fin 3) :
      (fun x : Vec3 => CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i) =
        convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
          (fun y : Vec3 => u (y, t) i)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact lps_regUniformMollifiedVelocity_component_convolution
      ρ ε hε u t hu x i
  constructor
  · intro i
    rw [hcomp i]
    exact hκc.contDiff_convolution_left (n := ⊤)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hκ
      ((huL2 i []).locallyIntegrable (by norm_num))
  · intro i α
    rw [hcomp i]
    exact lps_wordDeriv_convolution_memLp
      hκ hκc hκnonneg hκone (hsmooth i) (huL2 i) α

/-- The actual regularized transport velocity contracts the whole
ordered `H^m` energy on each smooth time slice (`eq:lps-Hm-energy`). -/
theorem lps_regUniformMollifiedVelocity_sobolevNormSq_le
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hsmooth : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume)
    (m : ℕ) :
    (∑ i : Fin 3, sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (fun x : Vec3 => CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i))) ≤
      ∑ i : Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x : Vec3 => u (x, t) i)) := by
  have hcomp (i : Fin 3) :
      (fun x : Vec3 => CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i) =
        convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
          (fun y : Vec3 => u (y, t) i)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact lps_regUniformMollifiedVelocity_component_convolution
      ρ ε hε u t hu x i
  simp_rw [hcomp]
  exact lps_regKernel_vector_sobolevNormSq_le ρ ε hε hsmooth huL2 m

end ESS
