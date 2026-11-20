/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusFullVelocityConcrete
public import LeanPool.FastDynamo.Global.TorusBackgroundWeightedEnergy

/-!
# The background velocity `u^bg_n = u - u^loc_n` and its operator

`eq:background-velocity` removes from the global velocity
`u = Σ_m u_m^loc + Σ_m u_m^ax` **only the selected cell's local profile**; every other cell and
every added axial velocity is retained:

`u^bg_n = u - u_n^loc = Σ_{m ≠ n} u_m^loc + Σ_{m ≥ 0} u_m^ax`.

This module builds that field as a `TransverseRealW1Inf`, proves it transversally
divergence-free, defines

`A^bg_{ε,n} = horizontalInductionOperator u^bg_n ε K_n`

(`eq:background-operator`) and proves the
support-and-size half of `eq:background-local-coefficients`:

* writing `𝒞_n = ⋃_{m ≠ n} supp u_m^loc` (as in the proof of `prop:background-resolvent`), the
  horizontal velocity `w = (u^bg_n)_⊥` (an abbreviation of these Lean files)
  and its gradient `∇_⊥ w` vanish off `𝒞_n` (the added axial velocities are purely `e₃`-valued,
  so they contribute nothing to either);
* `|∇_⊥ w| ≤ C 1_{𝒞_n}` with the profile constant `parameterizedHelicalFirstDerivativeBound`,
  which is the `stretching` field of `BackgroundCoercivity`;
* on the core of a nonselected cell `m`, `|w| ≤ C ℓ_m`; combined with `|β_n| = |F(r_m)|` there
  and `|rF(r)| ≤ 1` this is `|β_n w| ≤ C ℓ_n ≤ C δ_-^{-1/2}√ε 1_{𝒞_n}`, the `transport` field of
  `BackgroundCoercivity` (the `β_n` half is supplied by
  `Global/TorusBackgroundMultiplier.lean`).

The axial coordinate is left intact by design: `(u^bg_n)_3 = (u^ax)_3 + Σ_{m≠n}(u_m^loc)_3`,
and `2πK_n (u^ax)_3 = τ s_n` is what makes the phase inequality
`eq:background-phase-positive` `τ`-free after division.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ScaleFamily.TorusCellPlacement

open AxialWeakTransfer FullVelocityConcrete
open EuclideanCellSourceCertificate

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-! ## The added axial velocity is purely axial -/

section Axial

variable {supportRadius : ℝ} (P : TorusCellPlacement (r := r) supportRadius)

/-- One descended axial cell has vanishing horizontal components: it is a multiple of `e₃`. -/
theorem axialOffsetTorus_apply_eq_zero_of_ne_two (tau : ℝ) (n : ℕ)
    (q : TransverseTorus) {i : Fin 3} (hi : i ≠ 2) :
    P.axialOffsetTorus tau n q i = 0 := by
  classical
  rw [axialOffsetTorus, torusPeriodizedExtension]
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [dite_eq_left hq]
    simp [axialOffsetEuclidean, hi]
  · rw [dite_eq_right hq]
    simp

/-- One descended axial cell derivative has vanishing horizontal components. -/
theorem axialOffsetTorusDerivative_apply_eq_zero_of_ne_two
    (tau : ℝ) (n : ℕ) (j : Fin 2) (q : TransverseTorus) {i : Fin 3} (hi : i ≠ 2) :
    P.axialOffsetTorusDerivative tau n j q i = 0 := by
  classical
  rw [axialOffsetTorusDerivative, torusPeriodizedExtension]
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [dite_eq_left hq]
    simp [axialOffsetEuclideanDerivative, hi]
  · rw [dite_eq_right hq]
    simp

/-- The whole added axial velocity `Σ_m u_m^ax` has vanishing horizontal components
(`eq:axial-offset`). -/
theorem axialOffsetGlobalTorus_apply_eq_zero_of_ne_two (tau : ℝ)
    (q : TransverseTorus) {i : Fin 3} (hi : i ≠ 2) :
    P.axialOffsetGlobalTorus tau q i = 0 := by
  by_cases hb : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hb
    rw [P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau hn]
    exact P.axialOffsetTorus_apply_eq_zero_of_ne_two tau n q hi
  · push Not at hb
    rw [P.axialOffsetGlobalTorus_eq_zero_of_outside_buffers tau hb]
    simp

/-- Every transverse derivative of the added axial velocity has vanishing horizontal
components. -/
theorem axialOffsetGlobalTorusDerivative_apply_eq_zero_of_ne_two
    (tau : ℝ) (j : Fin 2) (q : TransverseTorus) {i : Fin 3} (hi : i ≠ 2) :
    P.axialOffsetGlobalTorusDerivative tau j q i = 0 := by
  by_cases hb : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hb
    rw [P.axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer tau hn j]
    exact P.axialOffsetTorusDerivative_apply_eq_zero_of_ne_two tau n j q hi
  · push Not at hb
    rw [P.axialOffsetGlobalTorusDerivative_eq_zero_of_outside_buffers tau hb j]
    simp

/-- Distinct placed buffer discs on the torus are disjoint, in either order. -/
theorem notMem_torusBufferDisk_of_mem_of_ne {n m : ℕ} (hmn : m ≠ n)
    {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk m) :
    q ∉ P.torusBufferDisk n := by
  intro hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hlt)) hq hn
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hgt)) hn hq

/-! ## The nonselected cores `𝒞_n` -/

/-- `𝒞_n = ⋃_{m ≠ n} supp u_m^loc`, the union of the nonselected cores
(proof of `prop:background-resolvent`). -/
def nonselectedCores (n : ℕ) : Set TransverseTorus :=
  ⋃ m : ℕ, ⋃ _ : m ≠ n, P.torusLocalCoreDisk m

/-- Membership in `𝒞_n` is membership in some nonselected core. -/
theorem mem_nonselectedCores_iff (n : ℕ) (q : TransverseTorus) :
    q ∈ P.nonselectedCores n ↔ ∃ m : ℕ, m ≠ n ∧ q ∈ P.torusLocalCoreDisk m := by
  simp [nonselectedCores]

/-- Every nonselected core sits inside `𝒞_n`. -/
theorem torusLocalCoreDisk_subset_nonselectedCores {n m : ℕ} (hmn : m ≠ n) :
    P.torusLocalCoreDisk m ⊆ P.nonselectedCores n := fun _ hq ↦
  (P.mem_nonselectedCores_iff n _).mpr ⟨m, hmn, hq⟩

/-- `𝒞_n` is measurable, being a countable union of measurable placed cores. -/
theorem measurableSet_nonselectedCores (n : ℕ) :
    MeasurableSet (P.nonselectedCores n) :=
  MeasurableSet.iUnion fun m ↦
    MeasurableSet.iUnion fun _ ↦ P.measurableSet_torusLocalCoreDisk m

end Axial

/-! ## The background velocity -/

section Velocity

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ) (htau : 0 ≤ tau)

/-- The selected cell's local profile `u_n^loc` as a `W^{1,∞}` graph element. -/
def selectedLocalCell (n : ℕ) : TransverseRealW1Inf :=
  (parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete

/-- **`eq:background-velocity`**:
`u^bg_n = u - u_n^loc`.  Only the selected cell's local profile is removed; every other cell
and every added axial velocity stays. -/
def selectedBackgroundVelocity (n : ℕ) : TransverseRealW1Inf :=
  parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau -
    selectedLocalCell h P angularSpeed axialSpeed n

/-- Restoring the selected cell returns the global velocity. -/
theorem selectedBackgroundVelocity_add_selectedLocalCell (n : ℕ) :
    selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n +
        selectedLocalCell h P angularSpeed axialSpeed n =
      parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau := by
  rw [selectedBackgroundVelocity, sub_add_cancel]

/-- The background velocity is transversally divergence-free: both the global velocity and the
removed cell are. -/
theorem selectedBackgroundVelocity_isTransverseDivergenceFree (n : ℕ) :
    IsTransverseDivergenceFree
      (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) := by
  have hfull := parameterizedFullGlobalW1Inf_isTransverseDivergenceFree
    h P angularSpeed axialSpeed tau htau
  have hcell := (parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete_isTransverseDivergenceFree
  unfold IsTransverseDivergenceFree at hfull hcell ⊢
  rw [selectedBackgroundVelocity, selectedLocalCell, map_sub, map_sub]
  have hrearrange :
      (transverseW1InfComplexDerivCoordLInf (0 : Fin 2) (0 : Fin 3)
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) -
        transverseW1InfComplexDerivCoordLInf (0 : Fin 2) (0 : Fin 3)
          ((parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete)) +
      (transverseW1InfComplexDerivCoordLInf (1 : Fin 2) (1 : Fin 3)
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) -
        transverseW1InfComplexDerivCoordLInf (1 : Fin 2) (1 : Fin 3)
          ((parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete)) =
      (transverseW1InfComplexDerivCoordLInf (0 : Fin 2) (0 : Fin 3)
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) +
        transverseW1InfComplexDerivCoordLInf (1 : Fin 2) (1 : Fin 3)
          (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau)) -
      (transverseW1InfComplexDerivCoordLInf (0 : Fin 2) (0 : Fin 3)
          ((parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete) +
        transverseW1InfComplexDerivCoordLInf (1 : Fin 2) (1 : Fin 3)
          ((parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete)) := by
    abel
  rw [hrearrange, hfull, hcell, sub_zero]

/-- **`eq:background-operator`**:
`A^bg_{ε,n} h = ε(Δ_⊥ - (2πK_n)²)h - (u^bg_n)_⊥·∇_⊥h - 2πiK_n (u^bg_n)_3 h + (h·∇_⊥)(u^bg_n)_⊥`
on `L²(T²;ℂ²)` with domain `H²(T²;ℂ²)`. -/
def selectedBackgroundOperator (epsilon : ℝ) (K : ℤ) (n : ℕ) :
    DomainOperator TransverseC2L2 TransverseC2H2 :=
  horizontalInductionOperator
    (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) epsilon K

/-- The background operator is the horizontal operator of the background velocity. -/
theorem selectedBackgroundOperator_eq (epsilon : ℝ) (K : ℤ) (n : ℕ) :
    selectedBackgroundOperator h P angularSpeed axialSpeed tau htau epsilon K n =
      horizontalInductionOperator
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)
        epsilon K :=
  rfl

/-! ## Pointwise representatives of the background coefficients -/

/-- The helical part `Σ_{m ≠ n} u_m^loc` of `u^bg_n`, as a pointwise torus field. -/
def selectedBackgroundHelicalSource (n : ℕ) (q : TransverseTorus) : C3 :=
  parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q -
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource q

/-- One displayed transverse derivative of the helical part of `u^bg_n`. -/
def selectedBackgroundHelicalFirstDerivative (n : ℕ) (j : Fin 2)
    (q : TransverseTorus) : C3 :=
  parameterizedHelicalGlobalTorusFirstDerivative h P angularSpeed axialSpeed j q -
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative j q

/-- The pointwise complex representative of `u^bg_n`: the helical part plus every added
axial velocity. -/
def selectedBackgroundTorusSource (n : ℕ) (q : TransverseTorus) : C3 :=
  selectedBackgroundHelicalSource h P angularSpeed axialSpeed n q +
    complexifyR3 (P.axialOffsetGlobalTorus tau q)

/-- The pointwise complex representative of one displayed derivative of `u^bg_n`. -/
def selectedBackgroundTorusFirstDerivative (n : ℕ) (j : Fin 2)
    (q : TransverseTorus) : C3 :=
  selectedBackgroundHelicalFirstDerivative h P angularSpeed axialSpeed n j q +
    complexifyR3 (P.axialOffsetGlobalTorusDerivative tau j q)

/-- The complexified value of `u^bg_n` is represented a.e. by
`selectedBackgroundTorusSource`. -/
theorem transverseW1InfComplexValue_selectedBackgroundVelocity_coe_ae (n : ℕ) :
    (transverseW1InfComplexValueLInf
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) :
      TransverseTorus → C3) =ᵐ[transverseMeasure]
      selectedBackgroundTorusSource h P angularSpeed axialSpeed tau n := by
  have hbridge : transverseW1InfComplexValueLInf
      ((parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete) =
      complexifyR3LInf (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).transverseValueLInf := rfl
  rw [selectedBackgroundVelocity, selectedLocalCell, map_sub]
  filter_upwards [Lp.coeFn_sub
      (transverseW1InfComplexValueLInf
        (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau))
      (transverseW1InfComplexValueLInf
        ((parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete)),
    transverseW1InfComplexValue_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).complexifyR3LInf_transverseValueLInf_coe_ae]
    with q hsub hfull hcell
  rw [hsub]
  change (transverseW1InfComplexValueLInf
      (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) :
        TransverseTorus → C3) q -
    (transverseW1InfComplexValueLInf
      ((parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete) :
        TransverseTorus → C3) q = _
  rw [hfull, hbridge, hcell]
  simp only [selectedBackgroundTorusSource, selectedBackgroundHelicalSource,
    parameterizedFullGlobalTorusSource]
  abel

/-- The complexified `j`-th derivative of `u^bg_n` is represented a.e. by
`selectedBackgroundTorusFirstDerivative`. -/
theorem transverseW1InfComplexDeriv_selectedBackgroundVelocity_coe_ae
    (n : ℕ) (j : Fin 2) :
    (transverseW1InfComplexDerivLInf j
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) :
      TransverseTorus → C3) =ᵐ[transverseMeasure]
      selectedBackgroundTorusFirstDerivative h P angularSpeed axialSpeed tau n j := by
  have hbridge : transverseW1InfComplexDerivLInf j
      ((parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete) =
      complexifyR3LInf ((parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).transverseFirstDerivativeLInf j) := rfl
  rw [selectedBackgroundVelocity, selectedLocalCell, map_sub]
  filter_upwards [Lp.coeFn_sub
      (transverseW1InfComplexDerivLInf j
        (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau))
      (transverseW1InfComplexDerivLInf j
        ((parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete)),
    transverseW1InfComplexDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau j,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).complexifyR3LInf_transverseFirstDerivativeLInf_coe_ae j]
    with q hsub hfull hcell
  rw [hsub]
  change (transverseW1InfComplexDerivLInf j
      (parameterizedFullGlobalW1Inf h P angularSpeed axialSpeed tau htau) :
        TransverseTorus → C3) q -
    (transverseW1InfComplexDerivLInf j
      ((parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).toTransverseRealW1InfConcrete) :
        TransverseTorus → C3) q = _
  rw [hfull, hbridge, hcell]
  simp only [selectedBackgroundTorusFirstDerivative,
    selectedBackgroundHelicalFirstDerivative,
    parameterizedFullGlobalTorusFirstDerivative]
  abel

/-! ## Support and size of the background coefficients (`eq:background-local-coefficients`) -/

/-- Off the nonselected cores the assembled helical velocity is exactly the removed cell, so
the helical part of `u^bg_n` vanishes there. -/
theorem parameterizedHelicalGlobalTorusSource_eq_selected_of_notMem (n : ℕ)
    {q : TransverseTorus} (hq : q ∉ P.nonselectedCores n) :
    parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q =
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource q := by
  by_cases hn : q ∈ P.torusBufferDisk n
  · exact parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hn
  · have hcelln : (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource q = 0 :=
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
          (fun hc ↦ hn (P.torusLocalCoreDisk_subset_torusBufferDisk n hc))
    rw [hcelln]
    by_cases hb : ∃ m : ℕ, q ∈ P.torusBufferDisk m
    · obtain ⟨m, hm⟩ := hb
      have hmn : m ≠ n := fun hEq ↦ hn (hEq ▸ hm)
      rw [parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
        h P angularSpeed axialSpeed hm]
      exact (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed m).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
          (fun hc ↦ hq (P.torusLocalCoreDisk_subset_nonselectedCores hmn hc))
    · push Not at hb
      exact parameterizedHelicalGlobalTorusSource_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed hb

/-- The same statement for the displayed derivatives. -/
theorem parameterizedHelicalGlobalTorusFirstDerivative_eq_selected_of_notMem
    (n : ℕ) (j : Fin 2) {q : TransverseTorus} (hq : q ∉ P.nonselectedCores n) :
    parameterizedHelicalGlobalTorusFirstDerivative h P angularSpeed axialSpeed j q =
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusFirstDerivative j q := by
  by_cases hn : q ∈ P.torusBufferDisk n
  · exact parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hn j
  · have hcelln : (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusFirstDerivative j q = 0 :=
      (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
        n).torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk j
          (fun hc ↦ hn (P.torusLocalCoreDisk_subset_torusBufferDisk n hc))
    rw [hcelln]
    by_cases hb : ∃ m : ℕ, q ∈ P.torusBufferDisk m
    · obtain ⟨m, hm⟩ := hb
      have hmn : m ≠ n := fun hEq ↦ hn (hEq ▸ hm)
      rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
        h P angularSpeed axialSpeed hm j]
      exact (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
        m).torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk j
          (fun hc ↦ hq (P.torusLocalCoreDisk_subset_nonselectedCores hmn hc))
    · push Not at hb
      exact parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed hb j

/-- The helical part `Σ_{m≠n} u_m^loc` of `u^bg_n` vanishes off the nonselected cores. -/
theorem selectedBackgroundHelicalSource_eq_zero_of_notMem (n : ℕ)
    {q : TransverseTorus} (hq : q ∉ P.nonselectedCores n) :
    selectedBackgroundHelicalSource h P angularSpeed axialSpeed n q = 0 := by
  rw [selectedBackgroundHelicalSource,
    parameterizedHelicalGlobalTorusSource_eq_selected_of_notMem
      h P angularSpeed axialSpeed n hq, sub_self]

/-- Its displayed derivatives vanish off the nonselected cores as well. -/
theorem selectedBackgroundHelicalFirstDerivative_eq_zero_of_notMem
    (n : ℕ) (j : Fin 2) {q : TransverseTorus} (hq : q ∉ P.nonselectedCores n) :
    selectedBackgroundHelicalFirstDerivative h P angularSpeed axialSpeed n j q = 0 := by
  rw [selectedBackgroundHelicalFirstDerivative,
    parameterizedHelicalGlobalTorusFirstDerivative_eq_selected_of_notMem
      h P angularSpeed axialSpeed n j hq, sub_self]

/-- On the core of a nonselected cell `m` the helical part of `u^bg_n` is exactly `u_m^loc`. -/
theorem selectedBackgroundHelicalSource_eq_cell_of_mem_core (n : ℕ) {m : ℕ}
    (hmn : m ≠ n) {q : TransverseTorus} (hq : q ∈ P.torusLocalCoreDisk m) :
    selectedBackgroundHelicalSource h P angularSpeed axialSpeed n q =
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed m).torusSource q := by
  have hbuffer := P.torusLocalCoreDisk_subset_torusBufferDisk m hq
  have hnotn := P.notMem_torusBufferDisk_of_mem_of_ne hmn hbuffer
  rw [selectedBackgroundHelicalSource,
    parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hbuffer,
    (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
        (fun hc ↦ hnotn (P.torusLocalCoreDisk_subset_torusBufferDisk n hc)),
    sub_zero]

/-- The same statement for the displayed derivatives. -/
theorem selectedBackgroundHelicalFirstDerivative_eq_cell_of_mem_core
    (n : ℕ) (j : Fin 2) {m : ℕ} (hmn : m ≠ n) {q : TransverseTorus}
    (hq : q ∈ P.torusLocalCoreDisk m) :
    selectedBackgroundHelicalFirstDerivative h P angularSpeed axialSpeed n j q =
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed m).torusFirstDerivative j q := by
  have hbuffer := P.torusLocalCoreDisk_subset_torusBufferDisk m hq
  have hnotn := P.notMem_torusBufferDisk_of_mem_of_ne hmn hbuffer
  rw [selectedBackgroundHelicalFirstDerivative,
    parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hbuffer j,
    (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed
      n).torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk j
        (fun hc ↦ hnotn (P.torusLocalCoreDisk_subset_torusBufferDisk n hc)),
    sub_zero]

/-- **`eq:background-local-coefficients`, amplitude half**:
`|u^bg_n| ≤ C ℓ_m` on the core of the nonselected cell `m`.  With `|β_n| = |F(r_m)|` there and
`|rF(r)| ≤ 1` this gives `|β_n w| ≤ C ℓ_n ≤ C δ_-^{-1/2}√ε`. -/
theorem norm_selectedBackgroundHelicalSource_le_of_mem_core (n : ℕ) {m : ℕ}
    (hmn : m ≠ n) {q : TransverseTorus} (hq : q ∈ P.torusLocalCoreDisk m) :
    ‖selectedBackgroundHelicalSource h P angularSpeed axialSpeed n q‖ ≤
      parameterizedHelicalValueBound h angularSpeed axialSpeed *
        P.scaleFamily.ell m := by
  rw [selectedBackgroundHelicalSource_eq_cell_of_mem_core
    h P angularSpeed axialSpeed n hmn hq]
  exact (parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed m).norm_torusSource_le q

/-- **`eq:background-local-coefficients`, gradient half**:
`|∇_⊥ w| ≤ C 1_{𝒞_n}`. -/
theorem norm_selectedBackgroundHelicalFirstDerivative_le_indicator
    (n : ℕ) (j : Fin 2) (q : TransverseTorus) :
    ‖selectedBackgroundHelicalFirstDerivative h P angularSpeed axialSpeed n j q‖ ≤
      (P.nonselectedCores n).indicator
        (fun _ ↦ parameterizedHelicalFirstDerivativeBound
          h angularSpeed axialSpeed) q := by
  by_cases hq : q ∈ P.nonselectedCores n
  · rw [Set.indicator_of_mem hq]
    obtain ⟨m, hmn, hqm⟩ := (P.mem_nonselectedCores_iff n q).mp hq
    rw [selectedBackgroundHelicalFirstDerivative_eq_cell_of_mem_core
      h P angularSpeed axialSpeed n j hmn hqm]
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed m).norm_torusFirstDerivative_le j q
  · rw [Set.indicator_of_notMem hq,
      selectedBackgroundHelicalFirstDerivative_eq_zero_of_notMem
        h P angularSpeed axialSpeed n j hq, norm_zero]

/-! ## The coefficient hypotheses of `BackgroundCoercivity` -/

/-- The two horizontal fibre indices are not the axial one. -/
theorem castSucc_ne_two (j : Fin 2) : (j.castSucc : Fin 3) ≠ 2 := by
  fin_cases j <;> decide

/-- A purely axial vector has vanishing horizontal projection. -/
theorem horizontalProjPoint_complexifyR3_eq_zero {v : R3}
    (hv : ∀ i : Fin 3, i ≠ 2 → v i = 0) :
    horizontalProjPoint (complexifyR3 v) = 0 := by
  apply PiLp.ext
  intro j
  rw [horizontalProjPoint_apply]
  simp [complexifyR3_apply, hv j.castSucc (castSucc_ne_two j)]

/-- The horizontal velocity gradient coefficient `(∂_j u^bg_n)_⊥` is represented a.e. by the
horizontal projection of the pointwise derivative. -/
theorem transverseW1InfHorizontalDeriv_selectedBackgroundVelocity_coe_ae
    (n : ℕ) (j : Fin 2) :
    (transverseW1InfHorizontalDerivLInf j
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) :
      TransverseTorus → C2) =ᵐ[transverseMeasure] fun q ↦
      horizontalProjPoint
        (selectedBackgroundTorusFirstDerivative h P angularSpeed axialSpeed tau n j q) := by
  filter_upwards [horizontalProjLInf_coe_ae (transverseW1InfComplexDerivLInf j
      (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)),
    transverseW1InfComplexDeriv_selectedBackgroundVelocity_coe_ae
      h P angularSpeed axialSpeed tau htau n j] with q hproj hderiv
  change ((horizontalProjLInf (transverseW1InfComplexDerivLInf j
      (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) :
        TransverseC2LInf) : TransverseTorus → C2) q = _
  rw [hproj, hderiv]

/-- **The `stretching` hypothesis of `BackgroundCoercivity`**:
`|(∂_j u^bg_n)_⊥| ≤ C 1_{𝒞_n}` almost everywhere
(`eq:background-local-coefficients`). -/
theorem norm_transverseW1InfHorizontalDeriv_selectedBackgroundVelocity_le
    (n : ℕ) (j : Fin 2) :
    ∀ᵐ q ∂transverseMeasure,
      ‖(transverseW1InfHorizontalDerivLInf j
          (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) q‖ ≤
        (P.nonselectedCores n).indicator
          (fun _ ↦ parameterizedHelicalFirstDerivativeBound
            h angularSpeed axialSpeed) q := by
  filter_upwards [transverseW1InfHorizontalDeriv_selectedBackgroundVelocity_coe_ae
    h P angularSpeed axialSpeed tau htau n j] with q hq
  rw [hq, selectedBackgroundTorusFirstDerivative, map_add,
    horizontalProjPoint_complexifyR3_eq_zero
      (fun i hi ↦ P.axialOffsetGlobalTorusDerivative_apply_eq_zero_of_ne_two tau j q hi),
    add_zero]
  exact le_trans (norm_horizontalProjPoint_le _)
    (norm_selectedBackgroundHelicalFirstDerivative_le_indicator
      h P angularSpeed axialSpeed n j q)

/-- Every scalar coordinate of `u^bg_n` is represented a.e. by the corresponding coordinate of
the pointwise field. -/
theorem transverseW1InfComplexValueCoord_selectedBackgroundVelocity_coe_ae
    (n : ℕ) (i : Fin 3) :
    (transverseW1InfComplexValueCoordLInf i
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) :
      TransverseTorus → ℂ) =ᵐ[transverseMeasure] fun q ↦
      selectedBackgroundTorusSource h P angularSpeed axialSpeed tau n q i := by
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (transverseW1InfComplexValueLInf
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)),
    transverseW1InfComplexValue_selectedBackgroundVelocity_coe_ae
      h P angularSpeed axialSpeed tau htau n] with q hproj hvalue
  calc ((transverseCoordLInf i (transverseW1InfComplexValueLInf
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) :
          TransverseScalarLInf) : TransverseTorus → ℂ) q
      = EuclideanSpace.proj i ((transverseW1InfComplexValueLInf
          (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) :
            TransverseTorus → C3) q) := hproj
    _ = selectedBackgroundTorusSource h P angularSpeed axialSpeed tau n q i := by
        rw [hvalue]
        rfl

/-- Each horizontal coordinate of `u^bg_n` equals that of the helical part: the added axial
velocities are purely `e₃`-valued. -/
theorem selectedBackgroundTorusSource_castSucc_eq (n : ℕ) (i : Fin 2)
    (q : TransverseTorus) :
    selectedBackgroundTorusSource h P angularSpeed axialSpeed tau n q i.castSucc =
      selectedBackgroundHelicalSource h P angularSpeed axialSpeed n q i.castSucc := by
  rw [selectedBackgroundTorusSource]
  have haxial : complexifyR3 (P.axialOffsetGlobalTorus tau q) i.castSucc = 0 := by
    simp [complexifyR3_apply,
      P.axialOffsetGlobalTorus_apply_eq_zero_of_ne_two tau q (castSucc_ne_two i)]
  simp [haxial]

/-- **The support half of the `transport` hypothesis**: every horizontal coordinate of
`u^bg_n` vanishes off the nonselected cores. -/
theorem transverseW1InfComplexValueCoord_selectedBackgroundVelocity_eq_zero_of_notMem
    (n : ℕ) (i : Fin 2) :
    ∀ᵐ q ∂transverseMeasure, q ∉ P.nonselectedCores n →
      (transverseW1InfComplexValueCoordLInf i.castSucc
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) q = 0 := by
  filter_upwards [transverseW1InfComplexValueCoord_selectedBackgroundVelocity_coe_ae
    h P angularSpeed axialSpeed tau htau n i.castSucc] with q hq hnot
  rw [hq, selectedBackgroundTorusSource_castSucc_eq,
    selectedBackgroundHelicalSource_eq_zero_of_notMem
      h P angularSpeed axialSpeed n hnot]
  rfl

/-- **The amplitude half of the `transport` hypothesis**: on the core of the nonselected cell
`m` every horizontal coordinate of `u^bg_n` is bounded by `C ℓ_m`
(`eq:background-local-coefficients`). -/
theorem norm_transverseW1InfComplexValueCoord_selectedBackgroundVelocity_le_of_mem_core
    (n : ℕ) {m : ℕ} (hmn : m ≠ n) (i : Fin 2) :
    ∀ᵐ q ∂transverseMeasure, q ∈ P.torusLocalCoreDisk m →
      ‖(transverseW1InfComplexValueCoordLInf i.castSucc
          (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n)) q‖ ≤
        parameterizedHelicalValueBound h angularSpeed axialSpeed *
          P.scaleFamily.ell m := by
  filter_upwards [transverseW1InfComplexValueCoord_selectedBackgroundVelocity_coe_ae
    h P angularSpeed axialSpeed tau htau n i.castSucc] with q hq hcore
  rw [hq, selectedBackgroundTorusSource_castSucc_eq]
  refine le_trans (PiLp.norm_apply_le _ i.castSucc) ?_
  exact norm_selectedBackgroundHelicalSource_le_of_mem_core
    h P angularSpeed axialSpeed n hmn hcore

/-- The axial coefficient of `u^bg_n` splits into the added axial velocity `(u^ax)_3`, which
carries the phase `τ s_n` of `eq:background-phase-positive`, and the local axial
components `Σ_{m≠n}(u_m^loc)_3` of `eq:background-local-coefficients`. -/
theorem transverseW1InfComplexValueCoord_two_selectedBackgroundVelocity_coe_ae
    (n : ℕ) :
    (transverseW1InfComplexValueCoordLInf 2
        (selectedBackgroundVelocity h P angularSpeed axialSpeed tau htau n) :
      TransverseTorus → ℂ) =ᵐ[transverseMeasure] fun q ↦
      selectedBackgroundHelicalSource h P angularSpeed axialSpeed n q 2 +
        ((P.axialOffsetGlobalTorus tau q 2 : ℝ) : ℂ) := by
  filter_upwards [transverseW1InfComplexValueCoord_selectedBackgroundVelocity_coe_ae
    h P angularSpeed axialSpeed tau htau n 2] with q hq
  rw [hq, selectedBackgroundTorusSource]
  simp [complexifyR3_apply]

end Velocity

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
