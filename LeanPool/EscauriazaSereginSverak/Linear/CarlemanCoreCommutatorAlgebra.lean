/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanCoreCommDerivatives

/-!
# Algebra of the scalar Carleman commutator

This is the finite-dimensional polynomial identity underlying
`eq:carleman-commutator`. Its variables stand for the coordinate derivatives
of a scalar field and a smooth phase.
-/

public section


open Finset
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

local instance carlemanCoreCommutatorAlgebraNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreCommutatorAlgebraNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- The symmetric part of the time-weighted conjugated heat operator in
`eq:carleman-S`. -/
@[expose] def commutatorSymmetric (φ v : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ :=
  z.2 * scalarLaplacian v z +
    z.2 * (scalarGradSq φ z - timePartial φ z) * v z - v z / 2

/-- The skew part of the time-weighted conjugated heat operator in
`eq:carleman-A`. -/
@[expose] def commutatorSkew (φ v : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ :=
  z.2 * timePartial v z + v z / 2 -
    z.2 * (2 * (∑ i, spatialPartial φ i z * spatialPartial v i z) +
      scalarLaplacian φ z * v z)

/-- The time flux whose derivative appears in the scalar commutator
identity `eq:carleman-commutator`. -/
@[expose] def commutatorTimeFlux (φ v : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ :=
  (scalarGradSq φ z - timePartial φ z) * (z.2 ^ 2 * v z ^ 2) -
    z.2 ^ 2 * scalarGradSq v z -
    (1 / 2) * (z.2 * v z ^ 2)

/-- The spatial flux whose divergence appears in the scalar commutator
identity `eq:carleman-commutator`. -/
@[expose] def commutatorSpaceFlux (φ v : ParabolicPoint → ℝ)
    (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  2 * (z.2 ^ 2 * (spatialPartial v i z * timePartial v z)) +
    z.2 * (v z * spatialPartial v i z) -
    4 * (z.2 ^ 2 * (spatialPartial v i z *
      (∑ j, spatialPartial φ j z * spatialPartial v j z))) +
    2 * (z.2 ^ 2 * (spatialPartial φ i z * scalarGradSq v z)) -
    2 * (z.2 ^ 2 *
      (scalarLaplacian φ z * (v z * spatialPartial v i z))) +
    z.2 ^ 2 * (spatialPartial (scalarLaplacian φ) i z * v z ^ 2) -
    2 * (z.2 ^ 2 * ((scalarGradSq φ z - timePartial φ z) *
      (spatialPartial φ i z * v z ^ 2))) +
    z.2 * (spatialPartial φ i z * v z ^ 2)

private theorem commutator_sym_skew_eq_conj
    (φ v : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    commutatorSymmetric φ v z + commutatorSkew φ v z =
      z.2 * carlemanConj φ v z := by
  unfold commutatorSymmetric commutatorSkew carlemanConj
  ring

private theorem commutator_jet_identity
    (T u ut b bt d Q Qt : ℝ)
    (p pt q qt di ddi : Fin 3 → ℝ)
    (h r : Fin 3 → Fin 3 → ℝ)
    (hr : ∀ i j, r i j = r j i)
    (hh : ∀ i j, h i j = h j i)
    (hQ : Q = (∑ i, p i ^ 2) - b)
    (hQt : Qt = 2 * (∑ i, p i * pt i) - bt)
    (hd : d = ∑ i, h i i) :
    2 * (T * (∑ i, r i i) + T * Q * u - u / 2) *
        (T * ut + u / 2 - T * (2 * (∑ i, p i * q i) + d * u)) =
      4 * T ^ 2 *
          (∑ i, ∑ j, h i j * (q i * q j + p i * p j * u ^ 2)) +
        T ^ 2 * u ^ 2 *
          (bt - 4 * (∑ i, p i * pt i) - (∑ i, ddi i)) +
        T * (∑ i, q i ^ 2) - T * u ^ 2 * Q +
        (-2 * T * (∑ i, q i ^ 2) -
          2 * T ^ 2 * (∑ i, q i * qt i) -
          u ^ 2 / 2 - T * u * ut +
          2 * T * Q * u ^ 2 + T ^ 2 * Qt * u ^ 2 +
          2 * T ^ 2 * Q * u * ut) +
        (∑ i, (
          2 * T ^ 2 * (r i i * ut + q i * qt i) +
          T * (q i ^ 2 + u * r i i) -
          4 * T ^ 2 *
            (r i i * (∑ j, p j * q j) +
              q i * (∑ j, (h j i * q j + p j * r j i))) +
          2 * T ^ 2 *
            (h i i * (∑ j, q j ^ 2) +
              p i * (2 * (∑ j, q j * r j i))) -
          2 * T ^ 2 *
            (di i * u * q i + d * q i ^ 2 + d * u * r i i) +
          T ^ 2 * (ddi i * u ^ 2 + 2 * di i * u * q i) -
          2 * T ^ 2 *
            ((2 * (∑ j, p j * h j i) - pt i) * p i * u ^ 2 +
              Q * h i i * u ^ 2 + 2 * Q * p i * u * q i) +
          T * (h i i * u ^ 2 + 2 * p i * u * q i))) := by
  subst Q
  subst Qt
  subst d
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [hr (Fin.succ 0) 0, hr ((Fin.succ 0).succ) 0,
    hr ((Fin.succ 0).succ) (Fin.succ 0),
    hh (Fin.succ 0) 0, hh ((Fin.succ 0).succ) 0,
    hh ((Fin.succ 0).succ) (Fin.succ 0)]
  ring

private theorem commutator_time_flux_derivative
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) :
    timePartial (commutatorTimeFlux φ v) z =
      -2 * z.2 * scalarGradSq v z -
        2 * z.2 ^ 2 * (∑ i, spatialPartial v i z *
          timePartial (fun y => spatialPartial v i y) z) -
        v z ^ 2 / 2 - z.2 * v z * timePartial v z +
        2 * z.2 * (scalarGradSq φ z - timePartial φ z) * v z ^ 2 +
        z.2 ^ 2 *
          timePartial (fun y => scalarGradSq φ y - timePartial φ y) z *
          v z ^ 2 +
        2 * z.2 ^ 2 * (scalarGradSq φ z - timePartial φ z) *
          v z * timePartial v z := by
  let Q : ParabolicPoint → ℝ := fun y =>
    scalarGradSq φ y - timePartial φ y
  let M : ParabolicPoint → ℝ := fun y => y.2 ^ 2 * v y ^ 2
  let G : ParabolicPoint → ℝ := fun y => y.2 ^ 2 * scalarGradSq v y
  let R : ParabolicPoint → ℝ := fun y => (1 / 2) * (y.2 * v y ^ 2)
  have hQ : DifferentiableAt ℝ Q z :=
    (((contDiffOn_scalarGradSq hU hφ).sub
      (contDiffOn_timePartial hU hφ)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have ht2 : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2 ^ 2) z := by fun_prop
  have ht1 : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2) z := by fun_prop
  have hM : DifferentiableAt ℝ M z := by
    dsimp [M]
    exact ht2.mul (hvd.pow 2)
  have hG : DifferentiableAt ℝ G z := by
    have hgrad : DifferentiableAt ℝ (scalarGradSq v) z :=
      ((contDiffOn_scalarGradSq isOpen_univ hv.contDiffOn).contDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ z))).differentiableAt (by simp)
    exact (by fun_prop : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2 ^ 2) z).mul hgrad
  have hR : DifferentiableAt ℝ R z := by
    dsimp [R]
    exact (differentiableAt_const _).mul (ht1.mul (hvd.pow 2))
  have hQM : DifferentiableAt ℝ (fun y => Q y * M y) z := hQ.mul hM
  have hmain : timePartial (fun y => Q y * M y) z =
      timePartial Q z * M z + Q z * timePartial M z :=
    timePartial_mul_at hQ hM
  have hMderiv := timePartial_time_pow_mul_sq_at 2 hv z
  have hGderiv : timePartial G z =
      2 * z.2 * scalarGradSq v z +
        2 * z.2 ^ 2 * (∑ i, spatialPartial v i z *
          timePartial (fun y => spatialPartial v i y) z) := by
    have ht : DifferentiableAt ℝ
        (fun y : ParabolicPoint => y.2 ^ 2) z := by fun_prop
    have hgrad : DifferentiableAt ℝ (scalarGradSq v) z :=
      ((contDiffOn_scalarGradSq isOpen_univ hv.contDiffOn).contDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ z))).differentiableAt (by simp)
    calc
      _ = timePartial (fun y : ParabolicPoint => y.2 ^ 2) z *
            scalarGradSq v z + z.2 ^ 2 * timePartial (scalarGradSq v) z :=
        timePartial_mul_at ht hgrad
      _ = _ := by
        rw [timePartial_time_pow, timePartial_scalarGradSq_on
          isOpen_univ hv.contDiffOn (Set.mem_univ z)]
        norm_num
        ring
  have hRderiv : timePartial R z =
      v z ^ 2 / 2 + z.2 * v z * timePartial v z := by
    have hbaseDeriv : timePartial (fun y => y.2 * v y ^ 2) z =
        v z ^ 2 + 2 * z.2 * v z * timePartial v z := by
      have heq : (fun y : ParabolicPoint => y.2 * v y ^ 2) =
          (fun y => y.2 ^ 1 * v y ^ 2) := by
        funext y
        simp
      rw [heq]
      simpa using timePartial_time_pow_mul_sq_at 1 hv z
    have hconst : DifferentiableAt ℝ
        (fun _ : ParabolicPoint => (1 / 2 : ℝ)) z := differentiableAt_const _
    have hbase : DifferentiableAt ℝ
        (fun y : ParabolicPoint => y.2 * v y ^ 2) z :=
      ht1.mul (hvd.pow 2)
    have hconst0 : timePartial (fun _ : ParabolicPoint => (1 / 2 : ℝ)) z = 0 := by
      simp [timePartial]
    calc
      _ = timePartial (fun _ : ParabolicPoint => (1 / 2 : ℝ)) z *
            (z.2 * v z ^ 2) +
          (1 / 2) * timePartial (fun y => y.2 * v y ^ 2) z :=
        timePartial_mul_at hconst hbase
      _ = _ := by
        rw [hconst0, hbaseDeriv]
        ring
  change timePartial (fun y => (Q y * M y - G y) - R y) z = _
  calc
    _ = timePartial (fun y => Q y * M y - G y) z - timePartial R z :=
      timePartial_sub_at (hQM.sub hG) hR
    _ = (timePartial (fun y => Q y * M y) z - timePartial G z) -
        timePartial R z := by rw [timePartial_sub_at hQM hG]
    _ = _ := by
      rw [hmain, hMderiv, hGderiv, hRderiv]
      dsimp [Q, M]
      ring

private theorem commutator_flux_term_one
    {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (z : ParabolicPoint) (i : Fin 3) :
    spatialPartial (fun y => 2 * (y.2 ^ 2 *
      (spatialPartial v i y * timePartial v y))) i z =
      2 * z.2 ^ 2 *
        (spatialSecondPartial v i i z * timePartial v z +
          spatialPartial v i z *
            timePartial (fun y => spatialPartial v i y) z) := by
  have hq : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial v i y) z :=
    ((contDiffOn_spatialPartial isOpen_univ hv.contDiffOn i).contDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ
      (fun y : ParabolicPoint => timePartial v y) z :=
    ((contDiffOn_timePartial isOpen_univ hv.contDiffOn).contDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))).differentiableAt (by simp)
  calc
    _ = 2 * z.2 ^ 2 * spatialPartial
          (fun y => spatialPartial v i y * timePartial v y) i z :=
      spatialPartial_const_time_pow_mul_at 2 2 (hq.mul ht) i
    _ = 2 * z.2 ^ 2 *
          (spatialPartial (fun y => spatialPartial v i y) i z *
              timePartial v z +
            spatialPartial v i z *
              spatialPartial (fun y => timePartial v y) i z) := by
      rw [spatialPartial_mul_at hq ht i]
    _ = _ := by
      rw [← timePartial_spatialPartial_comm_on isOpen_univ
        hv.contDiffOn (Set.mem_univ z) i]
      rfl

private theorem commutator_flux_term_two
    {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (z : ParabolicPoint) (i : Fin 3) :
    spatialPartial (fun y => y.2 * (v y * spatialPartial v i y)) i z =
      z.2 * (spatialPartial v i z ^ 2 +
        v z * spatialSecondPartial v i i z) := by
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hq : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial v i y) z :=
    ((contDiffOn_spatialPartial isOpen_univ hv.contDiffOn i).contDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))).differentiableAt (by simp)
  calc
    _ = z.2 * spatialPartial
          (fun y => v y * spatialPartial v i y) i z :=
      by
        have h := spatialPartial_time_pow_mul_at 1 (hvd.mul hq) i
        have heq : (v * fun y => spatialPartial v i y) =
            (fun y => v y * spatialPartial v i y) := by
          funext y
          rfl
        rw [heq] at h
        simpa only [pow_one] using h
    _ = _ := by
      rw [spatialPartial_mul_at hvd hq i]
      unfold spatialSecondPartial
      ring

private theorem commutator_flux_term_three
    (c : ℝ)
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => c * (y.2 ^ 2 *
      (spatialPartial v i y *
        (∑ j, spatialPartial φ j y * spatialPartial v j y)))) i z =
      c * z.2 ^ 2 *
        (spatialSecondPartial v i i z *
            (∑ j, spatialPartial φ j z * spatialPartial v j z) +
          spatialPartial v i z *
            (∑ j, (spatialSecondPartial φ j i z * spatialPartial v j z +
              spatialPartial φ j z * spatialSecondPartial v j i z))) := by
  let dot : ParabolicPoint → ℝ := fun y =>
    ∑ j, spatialPartial φ j y * spatialPartial v j y
  have hdotOn : ContDiffOn ℝ (⊤ : ℕ∞) dot U := by
    dsimp [dot]
    apply ContDiffOn.sum
    intro j _
    exact (contDiffOn_spatialPartial hU hφ j).mul
      (contDiffOn_spatialPartial hU hv.contDiffOn j)
  have hdot : DifferentiableAt ℝ dot z :=
    (hdotOn.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hq : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial v i y) z :=
    ((contDiffOn_spatialPartial hU hv.contDiffOn i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hinner : DifferentiableAt ℝ
      (fun y => spatialPartial v i y * dot y) z := hq.mul hdot
  calc
    _ = c * z.2 ^ 2 * spatialPartial
          (fun y => spatialPartial v i y * dot y) i z :=
      spatialPartial_const_time_pow_mul_at c 2 hinner i
    _ = _ := by
      rw [spatialPartial_mul_at hq hdot i,
        spatialPartial_gradientDot_on hU hφ hv.contDiffOn hz i]
      unfold spatialSecondPartial dot
      ring

private theorem commutator_flux_term_four
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => 2 * (y.2 ^ 2 *
      (spatialPartial φ i y * scalarGradSq v y))) i z =
      2 * z.2 ^ 2 *
        (spatialSecondPartial φ i i z * scalarGradSq v z +
          spatialPartial φ i z *
            (2 * ∑ j, spatialPartial v j z * spatialSecondPartial v j i z)) := by
  have hp : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial φ i y) z :=
    ((contDiffOn_spatialPartial hU hφ i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (scalarGradSq v) z :=
    ((contDiffOn_scalarGradSq hU hv.contDiffOn).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hinner : DifferentiableAt ℝ
      (fun y => spatialPartial φ i y * scalarGradSq v y) z := hp.mul hg
  calc
    _ = 2 * z.2 ^ 2 * spatialPartial
          (fun y => spatialPartial φ i y * scalarGradSq v y) i z :=
      spatialPartial_const_time_pow_mul_at 2 2 hinner i
    _ = _ := by
      rw [spatialPartial_mul_at hp hg i,
        spatialPartial_scalarGradSq_on hU hv.contDiffOn hz i]
      unfold spatialSecondPartial
      ring

private theorem commutator_flux_term_five
    (c : ℝ)
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => c * (y.2 ^ 2 *
      (scalarLaplacian φ y * (v y * spatialPartial v i y)))) i z =
      c * z.2 ^ 2 *
        (spatialPartial (scalarLaplacian φ) i z *
            v z * spatialPartial v i z +
          scalarLaplacian φ z * spatialPartial v i z ^ 2 +
          scalarLaplacian φ z * v z * spatialSecondPartial v i i z) := by
  have hd : DifferentiableAt ℝ (scalarLaplacian φ) z :=
    ((contDiffOn_scalarLaplacian hU hφ).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hq : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial v i y) z :=
    ((contDiffOn_spatialPartial hU hv.contDiffOn i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hinner : DifferentiableAt ℝ
      (fun y => scalarLaplacian φ y * (v y * spatialPartial v i y)) z :=
    hd.mul (hvd.mul hq)
  calc
    _ = c * z.2 ^ 2 * spatialPartial
          (fun y => scalarLaplacian φ y * (v y * spatialPartial v i y)) i z :=
      spatialPartial_const_time_pow_mul_at c 2 hinner i
    _ = _ := by
      have hprod : spatialPartial
          (fun y => scalarLaplacian φ y * (v y * spatialPartial v i y)) i z =
          spatialPartial (scalarLaplacian φ) i z *
            (v z * spatialPartial v i z) +
          scalarLaplacian φ z *
            spatialPartial (fun y => v y * spatialPartial v i y) i z :=
        spatialPartial_mul_at hd (hvd.mul hq) i
      have hvq : spatialPartial (fun y => v y * spatialPartial v i y) i z =
          spatialPartial v i z * spatialPartial v i z +
            v z * spatialPartial (fun y => spatialPartial v i y) i z :=
        spatialPartial_mul_at hvd hq i
      rw [hprod, hvq]
      unfold spatialSecondPartial
      ring

private theorem commutator_flux_term_six
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => y.2 ^ 2 *
      (spatialPartial (scalarLaplacian φ) i y * v y ^ 2)) i z =
      z.2 ^ 2 *
        (spatialSecondPartial (scalarLaplacian φ) i i z * v z ^ 2 +
          2 * spatialPartial (scalarLaplacian φ) i z *
            v z * spatialPartial v i z) := by
  have hd : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial (scalarLaplacian φ) i y) z :=
    ((contDiffOn_spatialPartial hU
      (contDiffOn_scalarLaplacian hU hφ) i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hinner : DifferentiableAt ℝ
      (fun y => spatialPartial (scalarLaplacian φ) i y * v y ^ 2) z :=
    hd.mul (hvd.pow 2)
  calc
    _ = z.2 ^ 2 * spatialPartial
          (fun y => spatialPartial (scalarLaplacian φ) i y * v y ^ 2) i z :=
      spatialPartial_time_pow_mul_at 2 hinner i
    _ = _ := by
      have hprod : spatialPartial
          (fun y => spatialPartial (scalarLaplacian φ) i y * v y ^ 2) i z =
          spatialPartial (fun y => spatialPartial (scalarLaplacian φ) i y) i z *
            v z ^ 2 +
          spatialPartial (scalarLaplacian φ) i z *
            spatialPartial (fun y => v y ^ 2) i z :=
        spatialPartial_mul_at hd (hvd.pow 2) i
      rw [hprod]
      have hsq := spatialPartial_sq_at hvd i
      rw [hsq]
      unfold spatialSecondPartial
      ring

private theorem commutator_flux_term_seven
    (c : ℝ)
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => c * (y.2 ^ 2 *
      ((scalarGradSq φ y - timePartial φ y) *
        (spatialPartial φ i y * v y ^ 2)))) i z =
      c * z.2 ^ 2 *
        ((2 * (∑ j, spatialPartial φ j z *
            spatialSecondPartial φ j i z) -
            timePartial (fun y => spatialPartial φ i y) z) *
            spatialPartial φ i z * v z ^ 2 +
          (scalarGradSq φ z - timePartial φ z) *
            spatialSecondPartial φ i i z * v z ^ 2 +
          2 * (scalarGradSq φ z - timePartial φ z) *
            spatialPartial φ i z * v z * spatialPartial v i z) := by
  let Q : ParabolicPoint → ℝ := fun y =>
    scalarGradSq φ y - timePartial φ y
  have hQ : DifferentiableAt ℝ Q z :=
    (((contDiffOn_scalarGradSq hU hφ).sub
      (contDiffOn_timePartial hU hφ)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hp : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial φ i y) z :=
    ((contDiffOn_spatialPartial hU hφ i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hinner : DifferentiableAt ℝ
      (fun y => Q y * (spatialPartial φ i y * v y ^ 2)) z :=
    hQ.mul (hp.mul (hvd.pow 2))
  calc
    _ = c * z.2 ^ 2 * spatialPartial
          (fun y => Q y * (spatialPartial φ i y * v y ^ 2)) i z :=
      spatialPartial_const_time_pow_mul_at c 2 hinner i
    _ = _ := by
      have hprod : spatialPartial
          (fun y => Q y * (spatialPartial φ i y * v y ^ 2)) i z =
          spatialPartial Q i z * (spatialPartial φ i z * v z ^ 2) +
          Q z * spatialPartial
            (fun y => spatialPartial φ i y * v y ^ 2) i z :=
        spatialPartial_mul_at hQ (hp.mul (hvd.pow 2)) i
      have hprod2 : spatialPartial
          (fun y => spatialPartial φ i y * v y ^ 2) i z =
          spatialPartial (fun y => spatialPartial φ i y) i z * v z ^ 2 +
            spatialPartial φ i z * spatialPartial (fun y => v y ^ 2) i z :=
        spatialPartial_mul_at hp (hvd.pow 2) i
      rw [hprod, hprod2]
      have hsq := spatialPartial_sq_at hvd i
      rw [hsq]
      have hQderiv := spatialPartial_carlemanPotential_on hU hφ hz i
      rw [hQderiv]
      dsimp [Q]
      unfold spatialSecondPartial
      ring

private theorem commutator_flux_term_eight
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => y.2 *
      (spatialPartial φ i y * v y ^ 2)) i z =
      z.2 * (spatialSecondPartial φ i i z * v z ^ 2 +
        2 * spatialPartial φ i z * v z * spatialPartial v i z) := by
  have hp : DifferentiableAt ℝ
      (fun y : ParabolicPoint => spatialPartial φ i y) z :=
    ((contDiffOn_spatialPartial hU hφ i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hinner : DifferentiableAt ℝ
      (fun y => spatialPartial φ i y * v y ^ 2) z :=
    hp.mul (hvd.pow 2)
  calc
    _ = z.2 * spatialPartial
          (fun y => spatialPartial φ i y * v y ^ 2) i z := by
      simpa only [pow_one] using
        (spatialPartial_time_pow_mul_at 1 hinner i)
    _ = _ := by
      have hprod : spatialPartial
          (fun y => spatialPartial φ i y * v y ^ 2) i z =
          spatialPartial (fun y => spatialPartial φ i y) i z * v z ^ 2 +
            spatialPartial φ i z * spatialPartial (fun y => v y ^ 2) i z :=
        spatialPartial_mul_at hp (hvd.pow 2) i
      rw [hprod]
      have hsq := spatialPartial_sq_at hvd i
      rw [hsq]
      unfold spatialSecondPartial
      ring

private theorem commutator_space_flux_derivative
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (commutatorSpaceFlux φ v i) i z =
      2 * z.2 ^ 2 *
          (spatialSecondPartial v i i z * timePartial v z +
            spatialPartial v i z *
              timePartial (fun y => spatialPartial v i y) z) +
        z.2 * (spatialPartial v i z ^ 2 +
          v z * spatialSecondPartial v i i z) -
        4 * z.2 ^ 2 *
          (spatialSecondPartial v i i z *
              (∑ j, spatialPartial φ j z * spatialPartial v j z) +
            spatialPartial v i z *
              (∑ j, (spatialSecondPartial φ j i z * spatialPartial v j z +
                spatialPartial φ j z * spatialSecondPartial v j i z))) +
        2 * z.2 ^ 2 *
          (spatialSecondPartial φ i i z * scalarGradSq v z +
            spatialPartial φ i z *
              (2 * ∑ j, spatialPartial v j z * spatialSecondPartial v j i z)) -
        2 * z.2 ^ 2 *
          (spatialPartial (scalarLaplacian φ) i z *
              v z * spatialPartial v i z +
            scalarLaplacian φ z * spatialPartial v i z ^ 2 +
            scalarLaplacian φ z * v z * spatialSecondPartial v i i z) +
        z.2 ^ 2 *
          (spatialSecondPartial (scalarLaplacian φ) i i z * v z ^ 2 +
            2 * spatialPartial (scalarLaplacian φ) i z *
              v z * spatialPartial v i z) -
        2 * z.2 ^ 2 *
          ((2 * (∑ j, spatialPartial φ j z *
              spatialSecondPartial φ j i z) -
              timePartial (fun y => spatialPartial φ i y) z) *
              spatialPartial φ i z * v z ^ 2 +
            (scalarGradSq φ z - timePartial φ z) *
              spatialSecondPartial φ i i z * v z ^ 2 +
            2 * (scalarGradSq φ z - timePartial φ z) *
              spatialPartial φ i z * v z * spatialPartial v i z) +
        z.2 * (spatialSecondPartial φ i i z * v z ^ 2 +
          2 * spatialPartial φ i z * v z * spatialPartial v i z) := by
  let dot : ParabolicPoint → ℝ := fun y =>
    ∑ j, spatialPartial φ j y * spatialPartial v j y
  let Q : ParabolicPoint → ℝ := fun y =>
    scalarGradSq φ y - timePartial φ y
  let parts : Fin 8 → ParabolicPoint → ℝ := ![
    fun y => 2 * (y.2 ^ 2 * (spatialPartial v i y * timePartial v y)),
    fun y => y.2 * (v y * spatialPartial v i y),
    fun y => -4 * (y.2 ^ 2 * (spatialPartial v i y * dot y)),
    fun y => 2 * (y.2 ^ 2 * (spatialPartial φ i y * scalarGradSq v y)),
    fun y => -2 * (y.2 ^ 2 *
      (scalarLaplacian φ y * (v y * spatialPartial v i y))),
    fun y => y.2 ^ 2 *
      (spatialPartial (scalarLaplacian φ) i y * v y ^ 2),
    fun y => -2 * (y.2 ^ 2 * (Q y * (spatialPartial φ i y * v y ^ 2))),
    fun y => y.2 * (spatialPartial φ i y * v y ^ 2)]
  have hfun : commutatorSpaceFlux φ v i =
      (fun y => ∑ k : Fin 8, parts k y) := by
    funext y
    simp [commutatorSpaceFlux, parts, dot, Q, Fin.sum_univ_succ]
    ring
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hvt : DifferentiableAt ℝ (fun y => timePartial v y) z :=
    ((contDiffOn_timePartial hU hv.contDiffOn).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hq (j : Fin 3) : DifferentiableAt ℝ
      (fun y => spatialPartial v j y) z :=
    ((contDiffOn_spatialPartial hU hv.contDiffOn j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hp (j : Fin 3) : DifferentiableAt ℝ
      (fun y => spatialPartial φ j y) z :=
    ((contDiffOn_spatialPartial hU hφ j).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (scalarLaplacian φ) z :=
    ((contDiffOn_scalarLaplacian hU hφ).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hdi : DifferentiableAt ℝ
      (fun y => spatialPartial (scalarLaplacian φ) i y) z :=
    ((contDiffOn_spatialPartial hU
      (contDiffOn_scalarLaplacian hU hφ) i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (scalarGradSq v) z :=
    ((contDiffOn_scalarGradSq hU hv.contDiffOn).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hQ : DifferentiableAt ℝ Q z :=
    (((contDiffOn_scalarGradSq hU hφ).sub
      (contDiffOn_timePartial hU hφ)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hdotOn : ContDiffOn ℝ (⊤ : ℕ∞) dot U := by
    dsimp [dot]
    apply ContDiffOn.sum
    intro j _
    exact (contDiffOn_spatialPartial hU hφ j).mul
      (contDiffOn_spatialPartial hU hv.contDiffOn j)
  have hdot : DifferentiableAt ℝ dot z :=
    (hdotOn.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have ht2 : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2 ^ 2) z := by fun_prop
  have ht1 : DifferentiableAt ℝ
      (fun y : ParabolicPoint => y.2) z := by fun_prop
  have hpartsDiff (k : Fin 8) : DifferentiableAt ℝ (parts k) z := by
    fin_cases k <;> dsimp [parts] <;>
      first
      | exact (differentiableAt_const _).mul (ht2.mul ((hq i).mul hvt))
      | exact ht1.mul (hvd.mul (hq i))
      | exact (differentiableAt_const _).mul (ht2.mul ((hq i).mul hdot))
      | exact (differentiableAt_const _).mul (ht2.mul ((hp i).mul hg))
      | exact (differentiableAt_const _).mul
          (ht2.mul (hd.mul (hvd.mul (hq i))))
      | exact ht2.mul (hdi.mul (hvd.pow 2))
      | exact (differentiableAt_const _).mul
          (ht2.mul (hQ.mul ((hp i).mul (hvd.pow 2))))
      | exact ht1.mul ((hp i).mul (hvd.pow 2))
  rw [hfun]
  calc
    _ = ∑ k : Fin 8, spatialPartial (parts k) i z :=
      spatialPartial_finsetSum_at Finset.univ parts (fun k _ => hpartsDiff k) i
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      dsimp [parts, dot, Q]
      rw [commutator_flux_term_one hv z i,
        commutator_flux_term_two hv z i,
        commutator_flux_term_three (-4) hU hφ hv hz i,
        commutator_flux_term_four hU hφ hv hz i,
        commutator_flux_term_five (-2) hU hφ hv hz i,
        commutator_flux_term_six hU hφ hv hz i,
        commutator_flux_term_seven (-2) hU hφ hv hz i,
        commutator_flux_term_eight hU hφ hv hz i]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
        Fin.succ_zero_eq_one', Fin.succ_one_eq_two']
      ring

/-- The scalar commutator pairing equals its density plus the derivatives of
compactly supported space-time fluxes. -/
theorem commutator_pointwise_divergence
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) :
    2 * commutatorSymmetric φ v z * commutatorSkew φ v z =
      carlemanCommutatorDensity φ v z +
        timePartial (commutatorTimeFlux φ v) z +
        ∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z := by
  have hr (i j : Fin 3) :
      spatialSecondPartial v i j z = spatialSecondPartial v j i z :=
    spatialSecondPartial_comm_on isOpen_univ hv.contDiffOn
      (Set.mem_univ z) i j
  have hh (i j : Fin 3) :
      spatialSecondPartial φ i j z = spatialSecondPartial φ j i z :=
    spatialSecondPartial_comm_on hU hφ hz i j
  have hQt := timePartial_carlemanPotential_on hU hφ hz
  have hbi := scalarLaplacian_second_diagonal_on hU hφ hz
  have htime := commutator_time_flux_derivative hU hφ hv hz
  have hspace (i : Fin 3) :=
    commutator_space_flux_derivative hU hφ hv hz i
  have hjet := commutator_jet_identity
    z.2 (v z) (timePartial v z) (timePartial φ z)
    (timePartial (fun y => timePartial φ y) z)
    (scalarLaplacian φ z)
    (scalarGradSq φ z - timePartial φ z)
    (timePartial (fun y => scalarGradSq φ y - timePartial φ y) z)
    (fun i => spatialPartial φ i z)
    (fun i => timePartial (fun y => spatialPartial φ i y) z)
    (fun i => spatialPartial v i z)
    (fun i => timePartial (fun y => spatialPartial v i y) z)
    (fun i => spatialPartial (scalarLaplacian φ) i z)
    (fun i => spatialSecondPartial (scalarLaplacian φ) i i z)
    (fun i j => spatialSecondPartial φ i j z)
    (fun i j => spatialSecondPartial v i j z)
    hr hh rfl hQt rfl
  unfold commutatorSymmetric commutatorSkew carlemanCommutatorDensity
  rw [← hbi, htime]
  simp_rw [hspace]
  simpa only [scalarLaplacian, scalarGradSq] using hjet

end ESS
