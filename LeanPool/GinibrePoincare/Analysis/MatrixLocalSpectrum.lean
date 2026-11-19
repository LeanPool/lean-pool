/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixLocalSpectrum.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralProjector
public import Mathlib.Topology.Compactness.Lindelof

/-! # Actual smooth local labeling of the full simple spectrum -/

@[expose] public section
open scoped Topology ContDiff
open Matrix Filter
namespace GinibrePoincare
noncomputable section

theorem matrixEigenbasis_eigenvalue_isRoot {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (eig : Fin n → ℂ) (b : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (hG : ∀ i, G *ᵥ b i = eig i • b i) (i : Fin n) : G.charpoly.eval (eig i) = 0 := by
  have hv : Module.End.HasEigenvector G.toLin' (eig i) (b i) := by
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      simpa only [Matrix.toLin'_apply] using hG i
    · exact b.ne_zero i
  have hs := (Module.End.hasEigenvalue_iff_mem_spectrum).mp
    (Module.End.hasEigenvalue_of_hasEigenvector hv)
  rw [Matrix.spectrum_toLin'] at hs
  exact (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hs).eq_zero

/-- An open neighborhood of each simple-spectrum matrix has a genuine C¹
labeling of its `n` distinct eigenvalues. -/
theorem matrixSimpleSpectrum_exists_smooth_local_labeling (n : ℕ)
    (G : GinibreMatrixCoordinates n) (hs : (Matrix.of G).charpoly.Separable) :
    ∃ U : Set (GinibreMatrixCoordinates n), ∃ labels : GinibreMatrixCoordinates n → Fin n → ℂ,
      IsOpen U ∧ G ∈ U ∧ ContDiffOn ℂ 1 labels U ∧
        ∀ A ∈ U, Function.Injective (labels A) ∧
          ∀ i, (Matrix.of A).charpoly.eval (labels A i) = 0 := by
  obtain ⟨eig, b, hi, hb⟩ := matrixSimpleSpectrum_exists_eigenbasis n (Matrix.of G) hs
  have hr := matrixEigenbasis_eigenvalue_isRoot (Matrix.of G) eig b hb
  choose branch hbase hdiff hroot hderiv using fun i =>
    matrixSimpleSpectrum_exists_local_eigenvalue_with_derivative n G (eig i) hs (hr i)
  let labels : GinibreMatrixCoordinates n → Fin n → ℂ := fun A i => branch i A
  have hd : ContDiffAt ℂ 1 labels G := contDiffAt_pi.mpr fun i =>
    (hdiff i).of_le (by simp)
  have hdiffNear := hd.eventually (by norm_num)
  have hrootNear : ∀ᶠ A in 𝓝 G, ∀ i, (Matrix.of A).charpoly.eval (labels A i) = 0 :=
    eventually_all.mpr hroot
  have hneNear : ∀ᶠ A in 𝓝 G, ∀ i j : Fin n, i ≠ j → labels A i ≠ labels A j := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · filter_upwards with A
      exact fun h => (h hij).elim
    · have hh := ((hdiff i).continuousAt.ne_iff_eventually_ne (hdiff j).continuousAt).mp
        (show branch i G ≠ branch j G by simpa only [hbase] using hi.ne hij)
      filter_upwards [hh] with A hA
      exact fun _ => hA
  have hnear : ∀ᶠ A in 𝓝 G, ContDiffAt ℂ 1 labels A ∧
      Function.Injective (labels A) ∧ ∀ i, (Matrix.of A).charpoly.eval (labels A i) = 0 := by
    filter_upwards [hdiffNear, hrootNear, hneNear] with A hdA hrA hnA
    exact ⟨hdA, fun i j hij => by_contra fun h => hnA i j h hij, hrA⟩
  obtain ⟨U, hUsub, hUopen, hGU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, labels, hUopen, hGU, fun A hA => (hUsub hA).1.contDiffWithinAt, ?_⟩
  intro A hA
  exact (hUsub hA).2

/-- A global measurable labeling built from a countable cover by smooth branches. -/
theorem matrix_exists_measurable_simple_labeling (n : ℕ) :
    ∃ labels : GinibreMatrixCoordinates n → Fin n → ℂ, Measurable labels ∧
      ∀ A, (Matrix.of A).charpoly.Separable → Function.Injective (labels A) ∧
        ∀ i, (Matrix.of A).charpoly.eval (labels A i) = 0 := by
  classical
  let S : Set (GinibreMatrixCoordinates n) := {A | (Matrix.of A).charpoly.Separable}
  have hpatch : ∀ A : GinibreMatrixCoordinates n,
      ∃ U : Set (GinibreMatrixCoordinates n), ∃ f : GinibreMatrixCoordinates n → Fin n → ℂ,
        IsOpen U ∧ (A ∈ S → A ∈ U) ∧ ContDiffOn ℂ 1 f U ∧
        ∀ B ∈ U, Function.Injective (f B) ∧ ∀ i, (Matrix.of B).charpoly.eval (f B i) = 0 := by
    intro A
    by_cases hA : A ∈ S
    · obtain ⟨U, f, ho, hm, hd, hr⟩ :=
        matrixSimpleSpectrum_exists_smooth_local_labeling n A hA
      exact ⟨U, f, ho, fun _ => hm, hd, hr⟩
    · exact ⟨∅, 0, isOpen_empty, fun h => (hA h).elim, by simp, by simp⟩
  choose U f ho hm hd hr using hpatch
  have hcover : S ⊆ ⋃ A, U A := fun A hA => Set.mem_iUnion.mpr ⟨A, hm A hA⟩
  obtain ⟨r, hc, hcov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U ho
      hcover
  let e := Set.enumerateCountable hc (0 : GinibreMatrixCoordinates n)
  let V : Set (GinibreMatrixCoordinates n) := ⋃ k : ℕ, U (e k)
  have hV : IsOpen V := isOpen_iUnion fun k => ho (e k)
  have hSV : S ⊆ V := by
    intro A hA
    obtain ⟨B, hAB⟩ := Set.mem_iUnion.mp (hcov hA)
    obtain ⟨hB, hAB⟩ := Set.mem_iUnion.mp hAB
    obtain ⟨k, hk⟩ := Set.subset_range_enumerate hc 0 hB
    exact Set.mem_iUnion.mpr ⟨k, by simpa only [e, hk] using hAB⟩
  let p : ℕ → GinibreMatrixCoordinates n → Prop
    | 0, A => A ∉ V
    | k + 1, A => A ∈ U (e k)
  let g : ℕ → GinibreMatrixCoordinates n → Fin n → ℂ
    | 0 => 0
    | k + 1 => (U (e k)).piecewise (f (e k)) 0
  have hp : ∀ A, ∃ k, p k A := by
    intro A
    by_cases hA : A ∈ V
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hA
      exact ⟨k + 1, hk⟩
    · exact ⟨0, hA⟩
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    cases k with
    | zero => exact measurable_const
    | succ k =>
      exact (hd (e k)).continuousOn.measurable_piecewise
        continuous_const.continuousOn (ho (e k)).measurableSet
  have hpm : ∀ k, MeasurableSet {A | p k A} := by
    intro k
    cases k with
    | zero => exact hV.measurableSet.compl
    | succ k => exact (ho (e k)).measurableSet
  refine ⟨fun A => g (Nat.find (hp A)) A, Measurable.find hgm hpm hp, ?_⟩
  intro A hA
  have hfind := Nat.find_spec (hp A)
  cases heq : Nat.find (hp A) with
  | zero =>
      rw [heq] at hfind
      exact (hfind (hSV hA)).elim
  | succ k =>
      rw [heq] at hfind
      simpa [heq, g, Set.piecewise, (show A ∈ U (e k) from hfind)] using hr (e k) A hfind

end
end GinibrePoincare
