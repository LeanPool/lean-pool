/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.MixedPartialSymmSpaceTimeSet
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.SliceCalculus
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialCongrSpaceTimeSet
public import LeanPool.CIVAxisymmetric.Reduction.SpatialPartialCongrSpaceTimeSet
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialLinearity
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialFinsetSumLinearity
public import LeanPool.CIVAxisymmetric.Reduction.LaplacianMultiPartialBridge
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus

/-!
# The differentiated forced Navier–Stokes system on `Ω × I`

Joint smoothness of multi-index derivatives, commutation of `∂_t` with `∂^α`, the pressure
Poisson identity `Δp = div f − ∑ᵢⱼ ∂ᵢuⱼ ∂ⱼuᵢ`, and the momentum equation of `eq:nse:forced`
differentiated by `∂^α`, for a classical solution on an open space-time product. These are the
identities behind the one-step estimates in the proof of `thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Iterated spatial partials of a jointly smooth field are jointly smooth. -/
theorem contDiffOn_spatialPartial_iterate_spaceTimeSet {g : ParabolicPoint → ℝ} {Ω : Set Vec3}
    {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) (j : Fin 3)
    (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ((fun k => spatialPartial k j)^[n] g) z)
      (spaceTimeSet Ω I) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact contDiffOn_spatialPartial_spaceTimeSet hΩ hI ih j

/-- Every multi-index derivative of a jointly smooth field is jointly smooth. -/
theorem contDiffOn_multiPartial_spaceTimeSet {g : ParabolicPoint → ℝ} {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) (α : Fin 3 → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => multiPartial g α z) (spaceTimeSet Ω I) :=
  contDiffOn_spatialPartial_iterate_spaceTimeSet hΩ hI
    (contDiffOn_spatialPartial_iterate_spaceTimeSet hΩ hI
      (contDiffOn_spatialPartial_iterate_spaceTimeSet hΩ hI hg 2 (α 2)) 1 (α 1)) 0 (α 0)

/-- `∂_t` commutes with an iterated spatial partial. -/
theorem timePartial_spatialPartial_iterate_eqOn {g : ParabolicPoint → ℝ} {Ω : Set Vec3}
    {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) (j : Fin 3)
    (n : ℕ) :
    Set.EqOn (timePartial ((fun k => spatialPartial k j)^[n] g))
      ((fun k => spatialPartial k j)^[n] (fun w => timePartial g w)) (spaceTimeSet Ω I) := by
  induction n with
  | zero => intro z _; rfl
  | succ n ih =>
    intro z hz
    simp only [Function.iterate_succ_apply']
    rw [← spatialPartial_timePartial_comm_spaceTimeSet hΩ hI
      (contDiffOn_spatialPartial_iterate_spaceTimeSet hΩ hI hg j n) hz j]
    exact spatialPartial_congr_of_eqOn_spaceTimeSet hΩ hI (fun w hw => ih hw) hz j

/-- `∂_t` commutes with `∂^α`. -/
theorem timePartial_multiPartial_spaceTimeSet {g : ParabolicPoint → ℝ} {Ω : Set Vec3}
    {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I))
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet Ω I) (α : Fin 3 → ℕ) :
    timePartial (multiPartial g α) z = multiPartial (fun w => timePartial g w) α z := by
  set S := spaceTimeSet Ω I
  have h2 := contDiffOn_spatialPartial_iterate_spaceTimeSet hΩ hI hg 2 (α 2)
  have h1 := contDiffOn_spatialPartial_iterate_spaceTimeSet hΩ hI h2 1 (α 1)
  have e0 := timePartial_spatialPartial_iterate_eqOn hΩ hI h1 0 (α 0)
  have e1 := timePartial_spatialPartial_iterate_eqOn hΩ hI h2 1 (α 1)
  have e2 := timePartial_spatialPartial_iterate_eqOn hΩ hI hg 2 (α 2)
  have f1 : Set.EqOn ((fun k => spatialPartial k 1)^[α 1]
      (fun w => timePartial ((fun k => spatialPartial k 2)^[α 2] g) w))
      ((fun k => spatialPartial k 1)^[α 1]
        ((fun k => spatialPartial k 2)^[α 2] (fun w => timePartial g w))) S :=
    spatialPartial_iterate_congr_of_eqOn_spaceTimeSet hΩ hI e2 1 (α 1)
  have f0 := spatialPartial_iterate_congr_of_eqOn_spaceTimeSet hΩ hI
    (fun w hw => (e1 hw).trans (f1 hw)) 0 (α 0)
  exact (e0 hz).trans (f0 hz)

/-- A spatial partial of a sum of three smooth fields is the sum of the spatial partials. -/
theorem spatialPartial_fin3_sum_spaceTimeSet {F : Fin 3 → ParabolicPoint → ℝ} {Ω : Set Vec3}
    (hΩ : IsOpen Ω) (t : ℝ)
    (hF : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => F i (x, t)) Ω) {x : Vec3} (hx : x ∈ Ω)
    (j : Fin 3) :
    spatialPartial (fun w => ∑ i, F i w) j (x, t) = ∑ i, spatialPartial (F i) j (x, t) := by
  rw [spatialPartial_eq_multiPartial_single, multiPartial_fin3_sum hΩ t hF _ hx]
  exact Finset.sum_congr rfl fun i _ => (spatialPartial_eq_multiPartial_single _ _ _ _).symm

/-- A field vanishing on `Ω × I` has vanishing spatial partials there. -/
theorem spatialPartial_eq_zero_of_eqOn_zero {F : ParabolicPoint → ℝ} {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hF : ∀ w ∈ spaceTimeSet Ω I, F w = 0)
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet Ω I) (j : Fin 3) :
    spatialPartial F j z = 0 := by
  rw [spatialPartial_congr_of_eqOn_spaceTimeSet (u := fun _ => (0 : ℝ)) hΩ hI hF hz j]
  simp [spatialPartial]

/-- A field vanishing on `Ω × I` has vanishing time partial there. -/
theorem timePartial_eq_zero_of_eqOn_zero {F : ParabolicPoint → ℝ} {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hF : ∀ w ∈ spaceTimeSet Ω I, F w = 0)
    {z : ParabolicPoint} (hz : z ∈ spaceTimeSet Ω I) :
    timePartial F z = 0 := by
  rw [timePartial_congr_of_eqOn_spaceTimeSet (u := fun _ => (0 : ℝ)) hΩ hI hF hz]
  simp [timePartial]

/-- The pressure Poisson identity `Δp = div f − ∑ᵢⱼ ∂ᵢuⱼ ∂ⱼuᵢ` for a classical solution of
`eq:nse:forced` on `Ω × I`. -/
theorem pressure_poisson_spaceTimeSet {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet Ω I)) {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet Ω I) :
    ∑ j, spatialSecondPartial p j j z =
      ∑ i, spatialPartial (fun w => f w i) i z -
        ∑ i, ∑ j, spatialPartial (fun w => u w j) i z * spatialPartial (fun w => u w i) j z := by
  obtain ⟨hu, hp, hf, hmom, hdiv⟩ := hsol
  set S := spaceTimeSet Ω I with hS
  obtain ⟨x, t⟩ := z
  have hx : x ∈ Ω := hz.1
  have ht : t ∈ I := hz.2
  have hui : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w i) S :=
    fun i => contDiffOn_pi.1 hu i
  have hfi : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w i) S :=
    fun i => contDiffOn_pi.1 hf i
  have d1 : ∀ (g : ParabolicPoint → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S →
      ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial g j w) S :=
    fun g hg j => contDiffOn_spatialPartial_spaceTimeSet hΩ hI hg j
  have sl : ∀ (g : ParabolicPoint → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => g (y, t)) Ω :=
    fun g hg => contDiffOn_slice_of_spaceTimeSet hg ht
  have dA : ∀ (g : ParabolicPoint → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S →
      DifferentiableAt ℝ (fun y : Vec3 => g (y, t)) x :=
    fun g hg => ((sl g hg).differentiableOn (by simp) x hx).differentiableAt (hΩ.mem_nhds hx)
  have hO : IsOpen (X := Vec3 × ℝ) S := hΩ.prod hI
  have dT : ∀ (g : ParabolicPoint → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S →
      DifferentiableAt ℝ (fun s : ℝ => g (x, s)) t := by
    intro g hg
    have h1 : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) (x, t) :=
      (hg.differentiableOn (by simp) (x, t) hz).differentiableAt (hO.mem_nhds hz)
    exact h1.comp t ((differentiableAt_const x).prodMk differentiableAt_id)
  -- the divergence `D` and its vanishing derivatives
  set D : ParabolicPoint → ℝ := fun w => ∑ i, spatialPartial (fun w' => u w' i) i w with hD
  have hD0 : ∀ w ∈ S, D w = 0 := fun w hw => hdiv w hw
  have hDj : ∀ j, spatialPartial D j (x, t) = 0 :=
    fun j => spatialPartial_eq_zero_of_eqOn_zero hΩ hI hD0 hz j
  have hDjj : ∀ j, spatialPartial (fun w => spatialPartial D j w) j (x, t) = 0 :=
    fun j => spatialPartial_eq_zero_of_eqOn_zero hΩ hI
      (fun w hw => spatialPartial_eq_zero_of_eqOn_zero hΩ hI hD0 hw j) hz j
  have hDt : timePartial D (x, t) = 0 := timePartial_eq_zero_of_eqOn_zero hΩ hI hD0 hz
  -- smoothness bookkeeping
  have hdu : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialPartial (fun w' => u w' i) j w) S := fun i j => d1 _ (hui i) j
  have hddu : ∀ i j k, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ =>
      spatialPartial (fun w' => spatialPartial (fun w'' => u w'' i) j w') k w) S :=
    fun i j k => d1 _ (hdu i j) k
  have hconv : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => u w j * spatialPartial (fun w' => u w' i) j w) S :=
    fun i j => (hui j).mul (hdu i j)
  have hlap : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) S :=
    fun i => ContDiffOn.sum fun j _ => hddu i j j
  have hconvS : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) S :=
    fun i => ContDiffOn.sum fun j _ => hconv i j
  have htu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => timePartial (fun w' => u w' i) w) S :=
    fun i => contDiffOn_timePartial_spaceTimeSet hΩ hI (hui i)
  -- differentiate the momentum equation
  have hM : ∀ i, spatialPartial (fun w => timePartial (fun w' => u w' i) w) i (x, t) +
      spatialPartial (fun w => ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) i (x, t) -
      spatialPartial (fun w => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) i (x, t) +
      spatialSecondPartial p i i (x, t) = spatialPartial (fun w => f w i) i (x, t) := by
    intro i
    have h := spatialPartial_congr_of_eqOn_spaceTimeSet hΩ hI
      (v := fun w => timePartial (fun w' => u w' i) w +
        ∑ j, u w j * spatialPartial (fun w' => u w' i) j w -
        ∑ j, spatialSecondPartial (fun w' => u w' i) j j w + spatialPartial p i w)
      (u := fun w => f w i) (fun w hw => hmom w hw i) hz i
    have e1 : spatialPartial (fun w => timePartial (fun w' => u w' i) w +
          ∑ j, u w j * spatialPartial (fun w' => u w' i) j w -
          ∑ j, spatialSecondPartial (fun w' => u w' i) j j w + spatialPartial p i w) i (x, t) =
        spatialPartial (fun w => timePartial (fun w' => u w' i) w +
          ∑ j, u w j * spatialPartial (fun w' => u w' i) j w -
          ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) i (x, t) +
        spatialPartial (fun w => spatialPartial p i w) i (x, t) :=
      spatialPartial_add_of_differentiableAt
        (((dA _ (htu i)).add (dA _ (hconvS i))).sub (dA _ (hlap i))) (dA _ (d1 _ hp i))
    have e2 : spatialPartial (fun w => timePartial (fun w' => u w' i) w +
          ∑ j, u w j * spatialPartial (fun w' => u w' i) j w -
          ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) i (x, t) =
        spatialPartial (fun w => timePartial (fun w' => u w' i) w +
          ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) i (x, t) -
        spatialPartial (fun w => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) i (x, t) :=
      spatialPartial_sub_of_differentiableAt ((dA _ (htu i)).add (dA _ (hconvS i)))
        (dA _ (hlap i))
    have e3 : spatialPartial (fun w => timePartial (fun w' => u w' i) w +
          ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) i (x, t) =
        spatialPartial (fun w => timePartial (fun w' => u w' i) w) i (x, t) +
        spatialPartial (fun w => ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) i (x, t) :=
      spatialPartial_add_of_differentiableAt (dA _ (htu i)) (dA _ (hconvS i))
    have e4 : spatialSecondPartial p i i (x, t) =
        spatialPartial (fun w => spatialPartial p i w) i (x, t) := rfl
    linarith only [h, e1, e2, e3, e4]
  -- the time term
  have hA : ∑ i, spatialPartial (fun w => timePartial (fun w' => u w' i) w) i (x, t) = 0 := by
    have h1 : ∀ i, spatialPartial (fun w => timePartial (fun w' => u w' i) w) i (x, t) =
        timePartial (spatialPartial (fun w' => u w' i) i) (x, t) :=
      fun i => spatialPartial_timePartial_comm_spaceTimeSet hΩ hI (hui i) hz i
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    rw [← hDt, hD]
    simp only [Fin.sum_univ_three]
    have e1 : timePartial (fun w => spatialPartial (fun w' => u w' 0) 0 w +
          spatialPartial (fun w' => u w' 1) 1 w + spatialPartial (fun w' => u w' 2) 2 w)
          ((x, t) : ParabolicPoint) =
        timePartial (fun w => spatialPartial (fun w' => u w' 0) 0 w +
          spatialPartial (fun w' => u w' 1) 1 w) ((x, t) : ParabolicPoint) +
        timePartial (spatialPartial (fun w' => u w' 2) 2) ((x, t) : ParabolicPoint) :=
      timePartial_add_of_differentiableAt (z := ((x, t) : ParabolicPoint))
        ((dT _ (hdu 0 0)).add (dT _ (hdu 1 1))) (dT _ (hdu 2 2))
    have e2 : timePartial (fun w => spatialPartial (fun w' => u w' 0) 0 w +
          spatialPartial (fun w' => u w' 1) 1 w) ((x, t) : ParabolicPoint) =
        timePartial (spatialPartial (fun w' => u w' 0) 0) ((x, t) : ParabolicPoint) +
        timePartial (spatialPartial (fun w' => u w' 1) 1) ((x, t) : ParabolicPoint) :=
      timePartial_add_of_differentiableAt (z := ((x, t) : ParabolicPoint))
        (dT _ (hdu 0 0)) (dT _ (hdu 1 1))
    rw [e1, e2]
  -- the viscous term
  have hC : ∑ i, spatialPartial (fun w => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) i
      (x, t) = 0 := by
    have h1 : ∀ i j, spatialPartial (fun w => spatialSecondPartial (fun w' => u w' i) j j w) i
        (x, t) = spatialPartial (fun w => spatialPartial
          (fun w' => spatialPartial (fun w'' => u w'' i) i w') j w) j (x, t) := by
      intro i j
      have e1 := spatialPartial_comm_spaceTimeSet
        (g := fun w => spatialPartial (fun w' => u w' i) j w)
        hΩ t (sl _ (hdu i j)) hx j i
      have e2 : spatialPartial (fun w => spatialPartial
            (fun w' => spatialPartial (fun w'' => u w'' i) j w') i w) j (x, t) =
          spatialPartial (fun w => spatialPartial
            (fun w' => spatialPartial (fun w'' => u w'' i) i w') j w) j (x, t) :=
        spatialPartial_congr_of_eqOn_spaceTimeSet hΩ hI
          (fun w hw => spatialPartial_comm_spaceTimeSet hΩ w.2
            (contDiffOn_slice_of_spaceTimeSet (hui i) hw.2) hw.1 j i) hz j
      exact e1.trans e2
    have h2 : ∀ i, spatialPartial (fun w => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) i
        (x, t) = ∑ j, spatialPartial (fun w => spatialSecondPartial (fun w' => u w' i) j j w) i
          (x, t) :=
      fun i => spatialPartial_fin3_sum_spaceTimeSet hΩ t (fun j => sl _ (hddu i j j)) hx i
    have hlin : ∀ j, ∑ i, spatialPartial (fun w => spatialPartial
          (fun w' => spatialPartial (fun w'' => u w'' i) i w') j w) j (x, t) =
        spatialPartial (fun w => spatialPartial D j w) j (x, t) := by
      intro j
      have heq : ∀ w ∈ S, spatialPartial D j w = ∑ i, spatialPartial
          (fun w' => spatialPartial (fun w'' => u w'' i) i w') j w := by
        intro w hw
        have := spatialPartial_fin3_sum_spaceTimeSet (F := fun i w' =>
          spatialPartial (fun w'' => u w'' i) i w') hΩ w.2
          (fun i => contDiffOn_slice_of_spaceTimeSet (hdu i i) hw.2) hw.1 j
        exact this
      rw [spatialPartial_congr_of_eqOn_spaceTimeSet hΩ hI heq hz j]
      exact (spatialPartial_fin3_sum_spaceTimeSet hΩ t
        (fun i => sl _ (hddu i i j)) hx j).symm
    simp_rw [h2, h1]
    rw [Finset.sum_comm]
    simp_rw [hlin, hDjj]
    simp
  -- the convective term
  have hB : ∑ i, spatialPartial (fun w => ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) i
      (x, t) = ∑ i, ∑ j, spatialPartial (fun w => u w j) i (x, t) *
        spatialPartial (fun w => u w i) j (x, t) := by
    have h1 : ∀ i, spatialPartial (fun w => ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) i
        (x, t) = ∑ j, (u (x, t) j * spatialPartial (fun w => spatialPartial
          (fun w' => u w' i) j w) i (x, t) + spatialPartial (fun w' => u w' i) j (x, t) *
            spatialPartial (fun w => u w j) i (x, t)) := by
      intro i
      rw [spatialPartial_fin3_sum_spaceTimeSet hΩ t (fun j => sl _ (hconv i j)) hx i]
      exact Finset.sum_congr rfl fun j _ =>
        spatialPartial_mul_of_differentiableAt (dA _ (hui j)) (dA _ (hdu i j))
    have h2 : ∀ j, ∑ i, spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) i (x, t)
        = 0 := by
      intro j
      rw [← hDj j, hD, spatialPartial_fin3_sum_spaceTimeSet hΩ t (fun i => sl _ (hdu i i)) hx j]
      exact Finset.sum_congr rfl fun i _ =>
        spatialPartial_comm_spaceTimeSet hΩ t (sl _ (hui i)) hx j i
    simp_rw [h1, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => u (x, t) j *
      spatialPartial (fun w => spatialPartial (fun w' => u w' i) j w) i (x, t))]
    simp_rw [← Finset.mul_sum, h2, mul_zero, Finset.sum_const_zero, zero_add]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hM i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [hA, hB, hC] at hsum
  linarith only [hsum]

/-- `∂^α (a - b) = ∂^α a - ∂^α b` on a time slice. -/
theorem multiPartial_sub_slice {a b : ParabolicPoint → ℝ} {Ω : Set Vec3} (hΩ : IsOpen Ω) (t : ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => a (x, t)) Ω)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => b (x, t)) Ω) (α : Fin 3 → ℕ) {x : Vec3}
    (hx : x ∈ Ω) :
    multiPartial (fun w => a w - b w) α (x, t) =
      multiPartial a α (x, t) - multiPartial b α (x, t) := by
  have hfun : (fun w => a w - b w) = fun w => a w + (-1) * b w := by
    funext w; ring
  have hb' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => (-1) * b (x, t)) Ω := contDiffOn_const.mul hb
  rw [hfun, multiPartial_add hΩ t ha hb' α hx, multiPartial_const_smul hΩ t hb α (-1) hx]
  ring

/-- The momentum equation of `eq:nse:forced` differentiated by `∂^α`. -/
theorem momentum_multiPartial_spaceTimeSet {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet Ω I)) {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet Ω I) (α : Fin 3 → ℕ) (i : Fin 3) :
    timePartial (multiPartial (fun w => u w i) α) z -
        ∑ j, spatialSecondPartial (multiPartial (fun w => u w i) α) j j z =
      multiPartial (fun w => f w i) α z -
        ∑ j, multiPartial (fun w => u w j * spatialPartial (fun w' => u w' i) j w) α z -
          multiPartial p (α + Pi.single i 1) z := by
  obtain ⟨hu, hp, hf, hmom, _⟩ := hsol
  set S := spaceTimeSet Ω I with hS
  obtain ⟨x, t⟩ := z
  have hx : x ∈ Ω := hz.1
  have ht : t ∈ I := hz.2
  have hui : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w i) S :=
    fun i => contDiffOn_pi.1 hu i
  have hfi : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w i) S :=
    fun i => contDiffOn_pi.1 hf i
  have d1 : ∀ (g : ParabolicPoint → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S →
      ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial g j w) S :=
    fun g hg j => contDiffOn_spatialPartial_spaceTimeSet hΩ hI hg j
  have sl : ∀ (g : ParabolicPoint → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) S →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => g (y, t)) Ω :=
    fun g hg => contDiffOn_slice_of_spaceTimeSet hg ht
  have hconv : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => u w j * spatialPartial (fun w' => u w' i) j w) S :=
    fun j => (hui j).mul (d1 _ (hui i) j)
  have hconvS : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) S :=
    ContDiffOn.sum fun j _ => hconv j
  have hlap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) S :=
    ContDiffOn.sum fun j _ => d1 _ (d1 _ (hui i) j) j
  have hT : timePartial (multiPartial (fun w => u w i) α) ((x, t) : ParabolicPoint) =
      multiPartial (fun w => timePartial (fun w' => u w' i) w) α ((x, t) : ParabolicPoint) :=
    timePartial_multiPartial_spaceTimeSet hΩ hI (hui i) hz α
  have hL : ∑ j, spatialSecondPartial (multiPartial (fun w => u w i) α) j j
        ((x, t) : ParabolicPoint) =
      multiPartial (fun w => ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) α
        ((x, t) : ParabolicPoint) :=
    sum_spatialSecondPartial_multiPartial_spaceTimeSet hΩ t (sl _ (hui i)) hx α
  have hE : multiPartial (fun w => timePartial (fun w' => u w' i) w) α ((x, t) : ParabolicPoint) =
      multiPartial (fun w => ((f w i - ∑ j, u w j * spatialPartial (fun w' => u w' i) j w) +
        ∑ j, spatialSecondPartial (fun w' => u w' i) j j w) - spatialPartial p i w) α
        ((x, t) : ParabolicPoint) :=
    multiPartial_congr_of_eqOn_spaceTimeSet hΩ hI (fun w hw => by
      have := hmom w hw i
      show timePartial (fun w' => u w' i) w = _
      linarith only [this]) α hz
  have s1 := sl _ (hfi i)
  have s2 := sl _ hconvS
  have s3 := sl _ hlap
  have s4 := sl _ (d1 _ hp i)
  have hfc : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => f (y, t) i -
      ∑ j, u (y, t) j * spatialPartial (fun w' => u w' i) j (y, t)) Ω := s1.sub s2
  have hfcl : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => (f (y, t) i -
      ∑ j, u (y, t) j * spatialPartial (fun w' => u w' i) j (y, t)) +
      ∑ j, spatialSecondPartial (fun w' => u w' i) j j (y, t)) Ω := hfc.add s3
  rw [multiPartial_sub_slice hΩ t hfcl s4 α hx, multiPartial_add hΩ t hfc s3 α hx,
    multiPartial_sub_slice hΩ t s1 s2 α hx,
    multiPartial_fin3_sum hΩ t (fun j => sl _ (hconv j)) α hx,
    multiPartial_spatialPartial_spaceTimeSet hΩ t (sl _ hp) hx α i] at hE
  rw [hT, hL, hE]
  ring_nf
  exact sub_right_comm _ _ _

end CIV
