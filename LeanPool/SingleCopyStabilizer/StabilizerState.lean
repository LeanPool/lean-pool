/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Measurement
public import LeanPool.SingleCopyStabilizer.Projection


/-!
# Stabilizer label spaces imply the operational computational distribution

This file joins finite-dimensional symplectic algebra to the explicit complex
amplitude Pauli action. The public state premises are normalization, actual
Pauli eigenvector equations, isotropy, and maximal label-space dimension.
Uniform measurement distributions are conclusions, not premises.
-/

@[expose] public section


noncomputable section

namespace LeanPool.SingleCopyStabilizer

attribute [local instance] Classical.propDecidable

open Measurement
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every label in L represents an actual Pauli eigenvector equation for ψ. -/
def HasEigenlabels (ψ : Amplitude ι) (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) : Prop :=
  ∀ a ∈ L, ∃ ζ, IsPauliEigenvector ψ a.1 a.2 ζ

/-- A normalized amplitude together with its maximal isotropic eigenlabel
space. Eigenvalue phases remain existential and are not discarded from the
underlying quantum equations. -/
structure PureStabilizerState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The actual pure-state amplitudes. -/
  amplitude : Amplitude ι
  normalized : IsNormalized amplitude
  /-- The maximal isotropic space of actual Pauli eigenlabels. -/
  labels : Submodule (ZMod 2) (Label (ZMod 2) ι)
  isotropic : IsIsotropic labels
  maximal : Module.finrank (ZMod 2) labels = Fintype.card ι
  eigenlabels : HasEigenlabels amplitude labels

omit [DecidableEq ι] in
theorem measurement_orthogonalSubgroup_eq (D : Submodule (ZMod 2) (Bits ι)) :
    orthogonalSubgroup (D : Set (Bits ι)) = (dotOrthogonal D).toAddSubgroup := by
  classical
  ext u
  change u ∈ orthogonalSet (D : Set (Bits ι)) ↔ u ∈ dotOrthogonal D
  rw [mem_dotOrthogonal]
  change (∀ s ∈ D, s ⬝ᵥ u = 0) ↔ (∀ s ∈ D, u ⬝ᵥ s = 0)
  simp only [dotProduct_comm]

omit [DecidableEq ι] in
theorem eigenlabels_diagonal (ψ : Amplitude ι)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L) :
    ∀ s ∈ (diagonalSpace L : Set (Bits ι)), ∃ ζ, IsPauliEigenvector ψ 0 s ζ := by
  classical
  intro s hs
  exact heig (0, s) hs

omit [DecidableEq ι] in
/-- Supported outcome differences annihilate diagonal labels for any
eigenlabel space, without a maximality or stabilizer-state promise. -/
theorem eigenlabels_supported_difference (ψ : Amplitude ι)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L)
    (x y : Bits ι) (hx : ψ x ≠ 0) (hy : ψ y ≠ 0) :
    x - y ∈ dotOrthogonal (diagonalSpace L) := by
  classical
  have h := supported_difference_orthogonal ψ (diagonalSpace L : Set (Bits ι))
    (eigenlabels_diagonal ψ L heig) x y hx hy
  rw [mem_dotOrthogonal]
  intro s hs
  rw [dotProduct_comm]
  exact h s hs

omit [DecidableEq ι] in
/-- For maximal isotropic eigenlabels the geometric X-projection theorem
turns every supported difference into an actual stabilizer X direction. -/
theorem stabilizer_supported_difference (ψ : Amplitude ι)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L)
    (hiso : IsIsotropic L) (hdim : Module.finrank (ZMod 2) L = Fintype.card ι)
    (x y : Bits ι) (hx : ψ x ≠ 0) (hy : ψ y ≠ 0) :
    ∃ v, (x - y, v) ∈ L := by
  classical
  apply (mem_xProjection L (x - y)).mp
  rw [lagrangian_xProjection_eq L hiso hdim]
  exact eigenlabels_supported_difference ψ L heig x y hx hy

/-- The paper's affine uniform-support theorem, now derived from actual
amplitude eigenvector equations and maximal isotropic label-space dimension. -/
theorem stabilizer_uniform_bornWeight (ψ : Amplitude ι) (hnorm : IsNormalized ψ)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L)
    (hiso : IsIsotropic L) (hdim : Module.finrank (ZMod 2) L = Fintype.card ι) :
    ∃ z, ∀ x, bornWeight ψ x =
      if x ∈ affineCoset (xProjection L).toAddSubgroup z then
        1 / (Nat.card (xProjection L) : ℝ) else 0 := by
  classical
  have heq : orthogonalSubgroup (diagonalSpace L : Set (Bits ι)) =
      (xProjection L).toAddSubgroup := by
    rw [measurement_orthogonalSubgroup_eq, lagrangian_xProjection_eq L hiso hdim]
  have hX : ∀ u ∈ orthogonalSubgroup (diagonalSpace L : Set (Bits ι)),
      ∃ v ζ, IsPauliEigenvector ψ u v ζ := by
    intro u hu
    rw [heq] at hu
    obtain ⟨v, huv⟩ := (mem_xProjection L u).mp hu
    obtain ⟨ζ, hζ⟩ := heig (u, v) huv
    exact ⟨v, ζ, hζ⟩
  have h := uniform_bornWeight_of_complete_eigenlabels ψ hnorm
    (diagonalSpace L : Set (Bits ι)) (eigenlabels_diagonal ψ L heig) hX
  have hcard : Nat.card (xProjection L).toAddSubgroup = Nat.card (xProjection L) :=
    Nat.card_congr {
      toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [heq, hcard] using h

theorem PureStabilizerState.uniform_bornWeight (S : PureStabilizerState ι) :
    ∃ z, ∀ x, bornWeight S.amplitude x =
      if x ∈ affineCoset (xProjection S.labels).toAddSubgroup z then
        1 / (Nat.card (xProjection S.labels) : ℝ) else 0 :=
  stabilizer_uniform_bornWeight S.amplitude S.normalized S.labels S.eigenlabels
    S.isotropic S.maximal

omit [DecidableEq ι] in
/-- Full diagonal dimension forces any two supported outcomes to coincide. -/
theorem full_diagonal_support_unique (ψ : Amplitude ι)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L)
    (hfull : Module.finrank (ZMod 2) (diagonalSpace L) = Fintype.card ι)
    (x y : Bits ι) (hx : ψ x ≠ 0) (hy : ψ y ≠ 0) : x = y := by
  classical
  have h := eigenlabels_supported_difference ψ L heig x y hx hy
  have htop := diagonalSpace_eq_top_of_full_dimension L hfull
  rw [mem_dotOrthogonal, htop] at h
  have hzero : x - y = 0 := by
    funext i
    simpa using h (Pi.single i 1) (by simp)
  exact sub_eq_zero.mp hzero

/-- The termination readout is a point mass when diagonal rank is full.
This theorem needs neither isotropy nor maximality beyond the stated full
diagonal-rank condition. -/
theorem full_diagonal_bornWeight_point_mass (ψ : Amplitude ι) (hnorm : IsNormalized ψ)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L)
    (hfull : Module.finrank (ZMod 2) (diagonalSpace L) = Fintype.card ι) :
    ∃ z, ∀ x, bornWeight ψ x = if x = z then 1 else 0 := by
  obtain ⟨z, hz⟩ := normalized_has_nonzero_amplitude ψ hnorm
  have hzero : ∀ x, x ≠ z → ψ x = 0 := by
    intro x hx
    by_contra hnx
    exact hx (full_diagonal_support_unique ψ L heig hfull x z hnx hz)
  have hmass : bornWeight ψ z = 1 := by
    calc
      bornWeight ψ z = ∑ x, bornWeight ψ x := by
        symm
        apply Finset.sum_eq_single z
        · intro x _ hx
          exact (bornWeight_eq_zero ψ x).mpr (hzero x hx)
        · simp
      _ = 1 := hnorm
  refine ⟨z, ?_⟩
  intro x
  by_cases hx : x = z
  · simpa [hx] using hmass
  · simp [hx, bornWeight, hzero x hx]

/-- Full diagonal rank identifies the amplitude with a basis vector times
a unit-modulus scalar, making the global-phase qualification explicit. -/
theorem full_diagonal_basis_amplitude (ψ : Amplitude ι) (hnorm : IsNormalized ψ)
    (L : Submodule (ZMod 2) (Label (ZMod 2) ι)) (heig : HasEigenlabels ψ L)
    (hfull : Module.finrank (ZMod 2) (diagonalSpace L) = Fintype.card ι) :
    ∃ z c, Complex.normSq c = 1 ∧ ψ = fun x => if x = z then c else 0 := by
  obtain ⟨z, hp⟩ := full_diagonal_bornWeight_point_mass ψ hnorm L heig hfull
  refine ⟨z, ψ z, ?_, ?_⟩
  · simpa [bornWeight] using hp z
  · funext x
    by_cases hx : x = z
    · simp [hx]
    · have hzero : bornWeight ψ x = 0 := by simpa [hx] using hp x
      simp [hx, (bornWeight_eq_zero ψ x).mp hzero]

/-- Two independent fresh computational measurements followed by subtraction.
The second distribution is constant in the first outcome, so this is an
independent product experiment expressed with mathlib's PMF bind/map. -/
def bornDifferencePMF (ψ : Amplitude ι) (hnorm : IsNormalized ψ) : PMF (Bits ι) :=
  (bornPMF ψ hnorm).bind (fun x => PMF.map (fun y => x - y) (bornPMF ψ hnorm))

omit [DecidableEq ι] [Fintype ι] in
theorem pmf_map_sub_left_apply (p : PMF (Bits ι)) (x u : Bits ι) :
    PMF.map (fun y => x - y) p u = p (x - u) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (x - u)]
  · simp
  · intro y hy
    apply ite_eq_right
    intro heq
    have hxy : x - u = y := by rw [heq]; simp
    exact hy hxy.symm

/-- The PMF subtraction pushforward equals the usual finite convolution
formula, derived from bind and map rather than assumed. -/
theorem bornDifferencePMF_apply (ψ : Amplitude ι) (hnorm : IsNormalized ψ)
    (u : Bits ι) :
    bornDifferencePMF ψ hnorm u =
      ENNReal.ofReal (∑ x, bornWeight ψ x * bornWeight ψ (x - u)) := by
  classical
  calc
    bornDifferencePMF ψ hnorm u =
        ∑ x, ENNReal.ofReal (bornWeight ψ x) *
          ENNReal.ofReal (bornWeight ψ (x - u)) := by
      simp only [bornDifferencePMF, PMF.bind_apply, pmf_map_sub_left_apply,
        tsum_fintype, bornPMF_apply]
    _ = ENNReal.ofReal (∑ x, bornWeight ψ x * bornWeight ψ (x - u)) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun x _ => mul_nonneg (bornWeight_nonneg ψ x) (bornWeight_nonneg ψ (x - u)))]
      apply Finset.sum_congr rfl
      intro x _
      exact (ENNReal.ofReal_mul (bornWeight_nonneg ψ x)).symm

/-- Finite convolution of one uniform affine distribution removes its affine
offset and gives the uniform distribution on its direction subgroup. -/
theorem uniform_affine_difference_mass (ψ : Amplitude ι)
    (V : AddSubgroup (Bits ι)) (z : Bits ι)
    (hp : ∀ x, bornWeight ψ x =
      if x ∈ affineCoset V z then 1 / (Nat.card V : ℝ) else 0)
    (u : Bits ι) :
    (∑ x, bornWeight ψ x * bornWeight ψ (x - u)) =
      if u ∈ V then 1 / (Nat.card V : ℝ) else 0 := by
  classical
  have hc : (Nat.card V : ℝ) ≠ 0 := by
    simp only [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  by_cases hu : u ∈ V
  · rw [ite_eq_left hu]
    have hshift (x : Bits ι) : x - u ∈ affineCoset V z ↔ x ∈ affineCoset V z := by
      rw [mem_affineCoset, mem_affineCoset]
      constructor
      · intro hx
        have h := V.add_mem hx hu
        convert h using 1; abel
      · intro hx
        have h := V.sub_mem hx hu
        convert h using 1; abel
    have hprod (x : Bits ι) : bornWeight ψ x * bornWeight ψ (x - u) =
        if x ∈ affineCoset V z then (1 / (Nat.card V : ℝ)) ^ 2 else 0 := by
      rw [hp x, hp (x - u)]
      simp only [hshift x]
      split_ifs <;> ring
    calc
      (∑ x, bornWeight ψ x * bornWeight ψ (x - u)) =
          ∑ x ∈ affineCoset V z, (1 / (Nat.card V : ℝ)) ^ 2 := by
        simp_rw [hprod]
        rw [← Finset.sum_filter]
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = (Nat.card V : ℝ) * (1 / (Nat.card V : ℝ)) ^ 2 := by
        simp [affineCoset_card, nsmul_eq_mul]
      _ = 1 / (Nat.card V : ℝ) := by field_simp
  · rw [ite_eq_right hu]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ affineCoset V z
    · have hy : x - u ∉ affineCoset V z := by
        intro hy
        apply hu
        have h := V.sub_mem ((mem_affineCoset V z x).mp hx)
          ((mem_affineCoset V z (x - u)).mp hy)
        convert h using 1; abel
      rw [hp x, hp (x - u), ite_eq_left hx, ite_eq_right hy, mul_zero]
    · rw [hp x, ite_eq_right hx, zero_mul]

/-- Actual independent Born-measurement differences of a stabilizer state
have the uniform PMF on its X projection. The only assumptions are the
quantum eigenvector equations and maximal isotropic label-space structure. -/
theorem stabilizer_bornDifferencePMF_uniform (ψ : Amplitude ι)
    (hnorm : IsNormalized ψ) (L : Submodule (ZMod 2) (Label (ZMod 2) ι))
    (heig : HasEigenlabels ψ L) (hiso : IsIsotropic L)
    (hdim : Module.finrank (ZMod 2) L = Fintype.card ι) (u : Bits ι) :
    bornDifferencePMF ψ hnorm u = if u ∈ xProjection L then
      ENNReal.ofReal (1 / (Nat.card (xProjection L) : ℝ)) else 0 := by
  classical
  obtain ⟨z, hp⟩ := stabilizer_uniform_bornWeight ψ hnorm L heig hiso hdim
  rw [bornDifferencePMF_apply,
    uniform_affine_difference_mass ψ (xProjection L).toAddSubgroup z hp u]
  split_ifs <;> simp_all

theorem PureStabilizerState.bornDifferencePMF_uniform (S : PureStabilizerState ι)
    (u : Bits ι) : bornDifferencePMF S.amplitude S.normalized u =
      if u ∈ xProjection S.labels then
        ENNReal.ofReal (1 / (Nat.card (xProjection S.labels) : ℝ)) else 0 :=
  stabilizer_bornDifferencePMF_uniform S.amplitude S.normalized S.labels
    S.eigenlabels S.isotropic S.maximal u

end LeanPool.SingleCopyStabilizer
