/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartFourierWeakTransfer
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The concrete transverse global velocity

This module assembles the rescaled parameterized helical cells on the
transverse torus.  The cell derivatives are uniformly bounded but do not
converge in the `L∞` norm.  Instead, pairwise-disjoint buffer support gives a
pointwise locally single-valued sum, uniformly bounded finite-sum derivatives,
and dominated convergence of every Fourier coefficient.  These are the raw
analytic inputs for the global `TransverseRealW1Inf` bundle of
`Global/TorusFullVelocityConcrete.lean`; this module does not itself construct
that bundle, nor the paper's added axial velocities `u_n^ax` (`eq:axial-offset`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped BigOperators ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

section ConcreteFamily

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed : ℝ)

/-- The Euclidean certificate underlying the `n`th concrete torus cell. -/
def parameterizedHelicalEuclideanCellCertificate (n : ℕ) :
    EuclideanCellSourceCertificate P n :=
  parameterizedHelicalCellSourceCertificate
    h P angularSpeed axialSpeed n

/-- The torus source of cell `m` vanishes at every point of a different cell's buffer disc `n`,
because distinct placed buffer discs are pairwise disjoint and the source lives in its own local
core.
-/
private theorem torusSource_eq_zero_on_distinct_buffer
    {m n : ℕ} (hmn : m ≠ n) {q : TransverseTorus}
    (hq : q ∈ P.torusBufferDisk n) :
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed m).torusSource q = 0 := by
  let C := parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed m
  apply C.torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
  intro hcore
  have hbuffer : q ∈ P.torusBufferDisk m :=
    P.torusLocalCoreDisk_subset_torusBufferDisk m hcore
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hlt))
      hbuffer hq
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hgt))
      hq hbuffer

/-- Each stored torus first derivative of cell `m` vanishes at every point of a different cell's
buffer disc `n`, by the same disjointness of placed buffers.
-/
private theorem torusFirstDerivative_eq_zero_on_distinct_buffer
    {m n : ℕ} (hmn : m ≠ n) {q : TransverseTorus}
    (hq : q ∈ P.torusBufferDisk n) (j : Fin 2) :
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed m).torusFirstDerivative j q = 0 := by
  let C := parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed m
  apply C.torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk
  intro hcore
  have hbuffer : q ∈ P.torusBufferDisk m :=
    P.torusLocalCoreDisk_subset_torusBufferDisk m hcore
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hlt))
      hbuffer hq
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hgt))
      hq hbuffer

/-- The pointwise complex sum of all concrete transverse cell values. -/
def parameterizedHelicalGlobalTorusSource (q : TransverseTorus) : C3 :=
  ∑' n : ℕ,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource q

/-- The pointwise complex sum of one coordinate derivative from every cell. -/
def parameterizedHelicalGlobalTorusFirstDerivative
    (j : Fin 2) (q : TransverseTorus) : C3 :=
  ∑' n : ℕ,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative j q

/-- At every torus point the family of cell values is summable: either the point lies in exactly one
buffer disc, in which case at most one term is nonzero, or it lies in none and every term
vanishes.
-/
theorem summable_parameterizedHelical_torusSource_at
    (q : TransverseTorus) :
    Summable (fun n : ℕ ↦
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource q) := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    apply summable_of_ne_finset_zero (s := {n})
    intro m hm
    simp only [Finset.mem_singleton] at hm
    exact torusSource_eq_zero_on_distinct_buffer
      h P angularSpeed axialSpeed hm hn
  · push Not at hbuffer
    convert (summable_zero : Summable (fun _ : ℕ ↦ (0 : C3))) using 1
    funext n
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
        (fun hcore ↦ hbuffer n
          (P.torusLocalCoreDisk_subset_torusBufferDisk n hcore))

/-- At every torus point the family of stored cell first derivatives is summable, for the same
reason of pairwise-disjoint buffer support.
-/
theorem summable_parameterizedHelical_torusFirstDerivative_at
    (j : Fin 2) (q : TransverseTorus) :
    Summable (fun n : ℕ ↦
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusFirstDerivative j q) := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    apply summable_of_ne_finset_zero (s := {n})
    intro m hm
    simp only [Finset.mem_singleton] at hm
    exact torusFirstDerivative_eq_zero_on_distinct_buffer
      h P angularSpeed axialSpeed hm hn j
  · push Not at hbuffer
    convert (summable_zero : Summable (fun _ : ℕ ↦ (0 : C3))) using 1
    funext n
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk
        j (fun hcore ↦ hbuffer n
          (P.torusLocalCoreDisk_subset_torusBufferDisk n hcore))

/-- Inside the `n`-th buffer disc the assembled global torus velocity is exactly the single cell
`n`; every other term of the sum vanishes there.
-/
theorem parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
    {n : ℕ} {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk n) :
    parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q =
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource q := by
  unfold parameterizedHelicalGlobalTorusSource
  exact tsum_eq_single n fun m hmn ↦
    torusSource_eq_zero_on_distinct_buffer
      h P angularSpeed axialSpeed hmn hq

/-- Inside the `n`-th buffer disc each stored first derivative of the assembled global velocity is
exactly that of the single cell `n`.
-/
theorem parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
    {n : ℕ} {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk n)
    (j : Fin 2) :
    parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed j q =
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusFirstDerivative j q := by
  unfold parameterizedHelicalGlobalTorusFirstDerivative
  exact tsum_eq_single n fun m hmn ↦
    torusFirstDerivative_eq_zero_on_distinct_buffer
      h P angularSpeed axialSpeed hmn hq j

/-- Outside every buffer disc the assembled global torus velocity vanishes. -/
theorem parameterizedHelicalGlobalTorusSource_eq_zero_of_outside_buffers
    {q : TransverseTorus} (hq : ∀ n : ℕ, q ∉ P.torusBufferDisk n) :
    parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q = 0 := by
  unfold parameterizedHelicalGlobalTorusSource
  have hz : ∀ n : ℕ,
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource q = 0 := by
    intro n
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
        (fun hcore ↦ hq n
          (P.torusLocalCoreDisk_subset_torusBufferDisk n hcore))
  simp_rw [hz]
  exact tsum_zero

/-- Outside every buffer disc each stored first derivative of the assembled global velocity
vanishes.
-/
theorem parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
    {q : TransverseTorus} (hq : ∀ n : ℕ, q ∉ P.torusBufferDisk n)
    (j : Fin 2) :
    parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed j q = 0 := by
  unfold parameterizedHelicalGlobalTorusFirstDerivative
  have hz : ∀ n : ℕ,
      (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusFirstDerivative j q = 0 := by
    intro n
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk
        j (fun hcore ↦ hq n
          (P.torusLocalCoreDisk_subset_torusBufferDisk n hcore))
  simp_rw [hz]
  exact tsum_zero

/-- The assembled global torus velocity is measurable, being a pointwise sum of measurable cell
values.
-/
theorem measurable_parameterizedHelicalGlobalTorusSource :
    Measurable
      (parameterizedHelicalGlobalTorusSource
        h P angularSpeed axialSpeed) := by
  apply Measurable.tsum
  intro n
  exact (parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n).measurable_torusSource

/-- Each stored first derivative of the assembled global torus velocity is measurable. -/
theorem measurable_parameterizedHelicalGlobalTorusFirstDerivative
    (j : Fin 2) :
    Measurable
      (parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed j) := by
  apply Measurable.tsum
  intro n
  exact (parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n).measurable_torusFirstDerivative j

/-- The assembled global torus velocity is bounded pointwise by the fixed profile bound times the
largest core scale `ell 0`; locality means only one cell contributes at a time and the cell
scales are decreasing.
-/
theorem norm_parameterizedHelicalGlobalTorusSource_le
    (q : TransverseTorus) :
    ‖parameterizedHelicalGlobalTorusSource
        h P angularSpeed axialSpeed q‖ ≤
      parameterizedHelicalValueBound h angularSpeed axialSpeed *
        P.scaleFamily.ell 0 := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hn]
    calc
      ‖(parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).torusSource q‖ ≤
          parameterizedHelicalValueBound h angularSpeed axialSpeed *
            P.scaleFamily.ell n :=
        (parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).norm_torusSource_le q
      _ ≤ parameterizedHelicalValueBound h angularSpeed axialSpeed *
          P.scaleFamily.ell 0 :=
        mul_le_mul_of_nonneg_left (P.scaleFamily.ell_le_ell_zero n)
          (parameterizedHelicalValueBound_nonneg
            h angularSpeed axialSpeed)
  · push Not at hbuffer
    rw [parameterizedHelicalGlobalTorusSource_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed hbuffer, norm_zero]
    exact mul_nonneg
      (parameterizedHelicalValueBound_nonneg h angularSpeed axialSpeed)
      (P.scaleFamily.ell_pos 0).le

/-- Each stored first derivative of the assembled global torus velocity is bounded pointwise by the
fixed profile derivative bound, uniformly in the cell index; the derivative bound carries no
factor of the cell scale.
-/
theorem norm_parameterizedHelicalGlobalTorusFirstDerivative_le
    (j : Fin 2) (q : TransverseTorus) :
    ‖parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed j q‖ ≤
      parameterizedHelicalFirstDerivativeBound
        h angularSpeed axialSpeed := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hn j]
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).norm_torusFirstDerivative_le j q
  · push Not at hbuffer
    rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed hbuffer j, norm_zero]
    exact parameterizedHelicalFirstDerivativeBound_nonneg
      h angularSpeed axialSpeed

/-- Every component of the assembled global torus velocity is pointwise real, as each cell value is.
-/
theorem parameterizedHelicalGlobalTorusSource_pointwiseReal
    (q : TransverseTorus) (i : Fin 3) :
    (parameterizedHelicalGlobalTorusSource
      h P angularSpeed axialSpeed q i).im = 0 := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hn]
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource_pointwiseReal q i
  · push Not at hbuffer
    rw [parameterizedHelicalGlobalTorusSource_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed hbuffer]
    simp

/-- Every component of each stored first derivative of the assembled global torus velocity is
pointwise real.
-/
theorem parameterizedHelicalGlobalTorusFirstDerivative_pointwiseReal
    (j : Fin 2) (q : TransverseTorus) (i : Fin 3) :
    (parameterizedHelicalGlobalTorusFirstDerivative
      h P angularSpeed axialSpeed j q i).im = 0 := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hn j]
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative_pointwiseReal j q i
  · push Not at hbuffer
    rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
      h P angularSpeed axialSpeed hbuffer j]
    simp

/-- The assembled global torus velocity is pointwise transversely divergence free: the stored
derivatives satisfy `∂₀v₀ + ∂₁v₁ = 0` at every torus point, inherited from each individual cell.
-/
theorem parameterizedHelicalGlobalTorusFirstDerivative_transverseDivergence
    (q : TransverseTorus) :
    parameterizedHelicalGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed 0 q 0 +
      parameterizedHelicalGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed 1 q 1 = 0 := by
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
        h P angularSpeed axialSpeed hn 0,
      parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
        h P angularSpeed axialSpeed hn 1]
    exact (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative_transverseDivergence q
  · push Not at hbuffer
    rw [parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed hbuffer 0,
      parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed hbuffer 1]
    simp

/-- The finite initial sum of concrete torus cell values. -/
def parameterizedHelicalPartialTorusSource
    (N : ℕ) (q : TransverseTorus) : C3 :=
  ∑ n ∈ Finset.range N,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusSource q

/-- The finite initial sum of one displayed cell derivative. -/
def parameterizedHelicalPartialTorusFirstDerivative
    (j : Fin 2) (N : ℕ) (q : TransverseTorus) : C3 :=
  ∑ n ∈ Finset.range N,
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).torusFirstDerivative j q

/-- Each finite initial sum of cell values is measurable. -/
theorem measurable_parameterizedHelicalPartialTorusSource (N : ℕ) :
    Measurable
      (parameterizedHelicalPartialTorusSource
        h P angularSpeed axialSpeed N) := by
  unfold parameterizedHelicalPartialTorusSource
  exact Finset.measurable_fun_sum (Finset.range N) fun n _ ↦
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).measurable_torusSource

/-- Each finite initial sum of stored cell first derivatives is measurable. -/
theorem measurable_parameterizedHelicalPartialTorusFirstDerivative
    (j : Fin 2) (N : ℕ) :
    Measurable
      (parameterizedHelicalPartialTorusFirstDerivative
        h P angularSpeed axialSpeed j N) := by
  unfold parameterizedHelicalPartialTorusFirstDerivative
  exact Finset.measurable_fun_sum (Finset.range N) fun n _ ↦
    (parameterizedHelicalEuclideanCellCertificate
      h P angularSpeed axialSpeed n).measurable_torusFirstDerivative j

/-- At every torus point the finite initial sums of cell values converge to the assembled global
velocity.
-/
theorem tendsto_parameterizedHelicalPartialTorusSource
    (q : TransverseTorus) :
    Tendsto (fun N : ℕ ↦
      parameterizedHelicalPartialTorusSource
        h P angularSpeed axialSpeed N q) atTop
      (𝓝 (parameterizedHelicalGlobalTorusSource
        h P angularSpeed axialSpeed q)) := by
  exact (summable_parameterizedHelical_torusSource_at
    h P angularSpeed axialSpeed q).hasSum.tendsto_sum_nat

/-- At every torus point the finite initial sums of stored cell first derivatives converge to the
corresponding derivative of the assembled global velocity.
-/
theorem tendsto_parameterizedHelicalPartialTorusFirstDerivative
    (j : Fin 2) (q : TransverseTorus) :
    Tendsto (fun N : ℕ ↦
      parameterizedHelicalPartialTorusFirstDerivative
        h P angularSpeed axialSpeed j N q) atTop
      (𝓝 (parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed j q)) := by
  exact (summable_parameterizedHelical_torusFirstDerivative_at
    h P angularSpeed axialSpeed j q).hasSum.tendsto_sum_nat

/-- Every finite initial sum of cell values obeys the same pointwise bound as the full sum,
uniformly in the number of terms: at any point at most one summand is nonzero.
-/
theorem norm_parameterizedHelicalPartialTorusSource_le
    (N : ℕ) (q : TransverseTorus) :
    ‖parameterizedHelicalPartialTorusSource
        h P angularSpeed axialSpeed N q‖ ≤
      parameterizedHelicalValueBound h angularSpeed axialSpeed *
        P.scaleFamily.ell 0 := by
  unfold parameterizedHelicalPartialTorusSource
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    by_cases hnN : n ∈ Finset.range N
    · rw [Finset.sum_eq_single n]
      · exact (parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).norm_torusSource_le q |>.trans
          (mul_le_mul_of_nonneg_left (P.scaleFamily.ell_le_ell_zero n)
            (parameterizedHelicalValueBound_nonneg
              h angularSpeed axialSpeed))
      · intro m hm hmn
        exact torusSource_eq_zero_on_distinct_buffer
          h P angularSpeed axialSpeed hmn hn
      · exact fun hnot ↦ (hnot hnN).elim
    · rw [Finset.sum_eq_zero]
      · simpa using mul_nonneg
          (parameterizedHelicalValueBound_nonneg h angularSpeed axialSpeed)
          (P.scaleFamily.ell_pos 0).le
      · intro m hm
        have hmn : m ≠ n := by
          intro hmn
          subst m
          exact hnN hm
        exact torusSource_eq_zero_on_distinct_buffer
          h P angularSpeed axialSpeed hmn hn
  · push Not at hbuffer
    rw [Finset.sum_eq_zero]
    · simpa using mul_nonneg
        (parameterizedHelicalValueBound_nonneg h angularSpeed axialSpeed)
        (P.scaleFamily.ell_pos 0).le
    · intro n hn
      exact (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
          (fun hcore ↦ hbuffer n
            (P.torusLocalCoreDisk_subset_torusBufferDisk n hcore))

/-- Every finite initial sum of stored cell first derivatives obeys the fixed profile derivative
bound, uniformly in the number of terms. This uniformity is what makes dominated convergence
applicable even though the derivative series does not converge in `L∞`.
-/
theorem norm_parameterizedHelicalPartialTorusFirstDerivative_le
    (j : Fin 2) (N : ℕ) (q : TransverseTorus) :
    ‖parameterizedHelicalPartialTorusFirstDerivative
        h P angularSpeed axialSpeed j N q‖ ≤
      parameterizedHelicalFirstDerivativeBound
        h angularSpeed axialSpeed := by
  unfold parameterizedHelicalPartialTorusFirstDerivative
  by_cases hbuffer : ∃ n : ℕ, q ∈ P.torusBufferDisk n
  · obtain ⟨n, hn⟩ := hbuffer
    by_cases hnN : n ∈ Finset.range N
    · rw [Finset.sum_eq_single n]
      · exact (parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).norm_torusFirstDerivative_le j q
      · intro m hm hmn
        exact torusFirstDerivative_eq_zero_on_distinct_buffer
          h P angularSpeed axialSpeed hmn hn j
      · exact fun hnot ↦ (hnot hnN).elim
    · rw [Finset.sum_eq_zero]
      · simpa using parameterizedHelicalFirstDerivativeBound_nonneg
          h angularSpeed axialSpeed
      · intro m hm
        have hmn : m ≠ n := by
          intro hmn
          subst m
          exact hnN hm
        exact torusFirstDerivative_eq_zero_on_distinct_buffer
          h P angularSpeed axialSpeed hmn hn j
  · push Not at hbuffer
    rw [Finset.sum_eq_zero]
    · simpa using parameterizedHelicalFirstDerivativeBound_nonneg
        h angularSpeed axialSpeed
    · intro n hn
      exact (parameterizedHelicalEuclideanCellCertificate
        h P angularSpeed axialSpeed n).torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk
          j (fun hcore ↦ hbuffer n
            (P.torusLocalCoreDisk_subset_torusBufferDisk n hcore))

/-! ## Fourier passage from finite sums to the disjoint infinite sum -/

/-- The scalar integrand computing one Fourier coefficient of a raw complex
torus vector field. -/
def parameterizedHelicalFourierIntegrand
    (frequency : TransverseFrequency) (i : Fin 3)
    (v : TransverseTorus → C3) (q : TransverseTorus) : ℂ :=
  UnitAddTorus.mFourier (-frequency) q * v q i

/-- The Fourier integrand `e_{-k}(q) · v(q)_i` is measurable whenever the field `v` is. -/
theorem measurable_parameterizedHelicalFourierIntegrand
    (frequency : TransverseFrequency) (i : Fin 3)
    {v : TransverseTorus → C3} (hv : Measurable v) :
    Measurable (parameterizedHelicalFourierIntegrand frequency i v) := by
  unfold parameterizedHelicalFourierIntegrand
  exact (UnitAddTorus.mFourier (-frequency)).continuous.measurable.mul
    ((EuclideanSpace.proj (𝕜 := ℂ) i).measurable.comp hv)

/-- The Fourier integrand is bounded pointwise by `‖v q‖`, since the character has modulus one and
each coordinate is bounded by the vector norm.
-/
theorem norm_parameterizedHelicalFourierIntegrand_le
    (frequency : TransverseFrequency) (i : Fin 3)
    (v : TransverseTorus → C3) (q : TransverseTorus) :
    ‖parameterizedHelicalFourierIntegrand frequency i v q‖ ≤ ‖v q‖ := by
  unfold parameterizedHelicalFourierIntegrand
  rw [norm_mul]
  calc
    ‖UnitAddTorus.mFourier (-frequency) q‖ * ‖v q i‖ ≤
        1 * ‖v q i‖ := by
      gcongr
      calc
        ‖UnitAddTorus.mFourier (-frequency) q‖ ≤
            ‖UnitAddTorus.mFourier (-frequency)‖ :=
          (UnitAddTorus.mFourier (-frequency)).norm_coe_le_norm q
        _ = 1 := UnitAddTorus.mFourier_norm
    _ ≤ ‖v q‖ := by
      simpa using PiLp.norm_apply_le (v q) i

/-- For a single cell the Fourier integrand of the torus source is integrable on the transverse
torus, being dominated by the constant `valueBound · ell_n` on a finite measure space.
-/
theorem integrable_parameterizedHelicalFourierIntegrand_torusSource
    (frequency : TransverseFrequency) (i : Fin 3) (n : ℕ) :
    Integrable
      (parameterizedHelicalFourierIntegrand frequency i
        (parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).torusSource)
      transverseMeasure := by
  let C := parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n
  refine Integrable.mono'
    (integrable_const (C.valueBound * P.scaleFamily.ell n))
    (measurable_parameterizedHelicalFourierIntegrand frequency i
      C.measurable_torusSource).aestronglyMeasurable ?_
  filter_upwards with q
  exact (norm_parameterizedHelicalFourierIntegrand_le
    frequency i C.torusSource q).trans (C.norm_torusSource_le q)

/-- For a single cell the Fourier integrand of a stored torus first derivative is integrable, being
dominated by the constant `firstDerivativeBound`.
-/
theorem integrable_parameterizedHelicalFourierIntegrand_torusFirstDerivative
    (frequency : TransverseFrequency) (i : Fin 3)
    (j : Fin 2) (n : ℕ) :
    Integrable
      (parameterizedHelicalFourierIntegrand frequency i
        ((parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).torusFirstDerivative j))
      transverseMeasure := by
  let C := parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n
  refine Integrable.mono'
    (integrable_const C.firstDerivativeBound)
    (measurable_parameterizedHelicalFourierIntegrand frequency i
      (C.measurable_torusFirstDerivative j)).aestronglyMeasurable ?_
  filter_upwards with q
  exact (norm_parameterizedHelicalFourierIntegrand_le frequency i
    (C.torusFirstDerivative j) q).trans
      (C.norm_torusFirstDerivative_le j q)

/-- Every Fourier coefficient of the finite initial sums converges to the corresponding coefficient
of the assembled global velocity. This is dominated convergence with the uniform bound of
`norm_parameterizedHelicalPartialTorusSource_le`, and is the substitute for `L∞` convergence of
the series.
-/
theorem tendsto_integral_parameterizedHelicalPartialTorusSource
    (frequency : TransverseFrequency) (i : Fin 3) :
    Tendsto (fun N : ℕ ↦
      ∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalPartialTorusSource
            h P angularSpeed axialSpeed N) q ∂transverseMeasure)
      atTop
      (𝓝 (∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalGlobalTorusSource
            h P angularSpeed axialSpeed) q ∂transverseMeasure)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ : TransverseTorus ↦
      parameterizedHelicalValueBound h angularSpeed axialSpeed *
        P.scaleFamily.ell 0)
  · intro N
    exact (measurable_parameterizedHelicalFourierIntegrand frequency i
      (measurable_parameterizedHelicalPartialTorusSource
        h P angularSpeed axialSpeed N)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact Filter.Eventually.of_forall fun q ↦
      (norm_parameterizedHelicalFourierIntegrand_le frequency i
        (parameterizedHelicalPartialTorusSource
          h P angularSpeed axialSpeed N) q).trans
        (norm_parameterizedHelicalPartialTorusSource_le
          h P angularSpeed axialSpeed N q)
  · exact Filter.Eventually.of_forall fun q ↦ by
      have hv := tendsto_parameterizedHelicalPartialTorusSource
        h P angularSpeed axialSpeed q
      have hproj : Tendsto (EuclideanSpace.proj (𝕜 := ℂ) i)
          (𝓝 (parameterizedHelicalGlobalTorusSource
            h P angularSpeed axialSpeed q))
          (𝓝 ((parameterizedHelicalGlobalTorusSource
            h P angularSpeed axialSpeed q) i)) :=
        (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt
      have hcoord := hproj.comp hv
      change Tendsto (fun N : ℕ ↦
          parameterizedHelicalPartialTorusSource
            h P angularSpeed axialSpeed N q i) atTop
        (𝓝 (parameterizedHelicalGlobalTorusSource
          h P angularSpeed axialSpeed q i)) at hcoord
      have hmono : Tendsto
          (fun _ : ℕ ↦ UnitAddTorus.mFourier (-frequency) q) atTop
          (𝓝 (UnitAddTorus.mFourier (-frequency) q)) :=
        tendsto_const_nhds
      simpa only [parameterizedHelicalFourierIntegrand, Function.comp_apply] using
        hmono.mul hcoord

/-- Every Fourier coefficient of the finite initial sums of stored derivatives converges to the
corresponding coefficient of the assembled global derivative, again by dominated convergence
with a uniform pointwise bound.
-/
theorem tendsto_integral_parameterizedHelicalPartialTorusFirstDerivative
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    Tendsto (fun N : ℕ ↦
      ∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalPartialTorusFirstDerivative
            h P angularSpeed axialSpeed j N) q ∂transverseMeasure)
      atTop
      (𝓝 (∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalGlobalTorusFirstDerivative
            h P angularSpeed axialSpeed j) q ∂transverseMeasure)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ : TransverseTorus ↦
      parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed)
  · intro N
    exact (measurable_parameterizedHelicalFourierIntegrand frequency i
      (measurable_parameterizedHelicalPartialTorusFirstDerivative
        h P angularSpeed axialSpeed j N)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact Filter.Eventually.of_forall fun q ↦
      (norm_parameterizedHelicalFourierIntegrand_le frequency i
        (parameterizedHelicalPartialTorusFirstDerivative
          h P angularSpeed axialSpeed j N) q).trans
        (norm_parameterizedHelicalPartialTorusFirstDerivative_le
          h P angularSpeed axialSpeed j N q)
  · exact Filter.Eventually.of_forall fun q ↦ by
      have hv := tendsto_parameterizedHelicalPartialTorusFirstDerivative
        h P angularSpeed axialSpeed j q
      have hproj : Tendsto (EuclideanSpace.proj (𝕜 := ℂ) i)
          (𝓝 (parameterizedHelicalGlobalTorusFirstDerivative
            h P angularSpeed axialSpeed j q))
          (𝓝 ((parameterizedHelicalGlobalTorusFirstDerivative
            h P angularSpeed axialSpeed j q) i)) :=
        (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt
      have hcoord := hproj.comp hv
      change Tendsto (fun N : ℕ ↦
          parameterizedHelicalPartialTorusFirstDerivative
            h P angularSpeed axialSpeed j N q i) atTop
        (𝓝 (parameterizedHelicalGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed j q i)) at hcoord
      have hmono : Tendsto
          (fun _ : ℕ ↦ UnitAddTorus.mFourier (-frequency) q) atTop
          (𝓝 (UnitAddTorus.mFourier (-frequency) q)) :=
        tendsto_const_nhds
      simpa only [parameterizedHelicalFourierIntegrand, Function.comp_apply] using
        hmono.mul hcoord

end ConcreteFamily

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
