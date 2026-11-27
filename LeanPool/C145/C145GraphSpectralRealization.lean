/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145WeightedGraph
public import LeanPool.C145.C145OrientedEigenframe
public import LeanPool.C145.C145FixedHorizonSmallInverse

/-! Connected symmetric nonnegative weighted graphs with an actual cyclic port
admit the oriented spectral interface of the accepted fixed-horizon inverse.
The port is real and may have either sign; the ground column's sign is derived.
-/

@[expose] public section

noncomputable section
namespace C145.GraphSpectralRealization
open scoped BigOperators Topology ContDiff
open Matrix C145.WeightedGraph C145.CyclicSpectral C145.OrientedEigenframe

/-- The negative Laplacian shifted by the common decay rate. -/
def generator {n : ℕ} (μ : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := -μ • 1 - laplacian W

theorem generator_symm {n : ℕ} (μ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hs : W.IsSymm) :
    (generator μ W).IsSymm :=
  ((Matrix.isSymm_one).smul (-μ)).sub (laplacian_symm W hs)

theorem generator_eigenvector {n : ℕ} (μ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ) (a : ℝ) (h : laplacian W *ᵥ x = a • x) :
    generator μ W *ᵥ x = (-(μ + a)) • x := by
  rw [generator, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h]
  module

/-- A spectral realization with an orthonormal eigenframe and oriented port overlaps. -/
structure OrientedRealization {n : ℕ} (μ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : Fin (n + 1) → ℝ) where
  /-- The vertex-coordinate columns of the modal eigenframe. -/
  Q : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- The decay rates of the modal columns. -/
  rates : Fin (n + 1) → ℝ
  /-- The common vertex value in the ground eigenvector. -/
  c : ℝ
  orthonormal : C145PhysicalFrame.ColumnOrthonormal Q
  ground : ∀ v, Q v 0 = c
  simple : Function.Injective rates
  ground_rate : rates 0 = μ
  higher : ∀ i : Fin n, μ < rates i.succ
  positive_overlap : ∀ i, 0 < C145.Pulse.modalOverlap Q b i
  eigenvectors : ∀ i, generator μ W *ᵥ (fun v => Q v i) =
    (-rates i) • (fun v => Q v i)
  original_generator : C145CoordinatePermutation.spectralGenerator rates Q = generator μ W
  original_laplacian : C145CoordinatePermutation.decayLaplacian μ rates Q = laplacian W

theorem connected_cyclic_graph_has_oriented_spectral_realization {n : ℕ}
    (μ : ℝ) (_hμ : 0 < μ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hs : W.IsSymm) (hn : ∀ v u, 0 ≤ W v u)
    (hc : (supportGraph W hs).Connected)
    (b : Fin (n + 1) → ℝ) (hcyc : KrylovCyclic (generator μ W) b) :
    Nonempty (OrientedRealization μ W b) := by
  let hp := laplacian_posSemidef W hs hn
  let hL := hp.isHermitian
  let U : Fin (n + 1) → Fin (n + 1) → ℝ := fun v i => (hL.eigenvectorBasis i) v
  let a : Fin (n + 1) → ℝ := hL.eigenvalues
  have hU : C145PhysicalFrame.ColumnOrthonormal U := hermitian_frame _ hL
  have heL : ∀ i, laplacian W *ᵥ (fun v => U v i) = a i • (fun v => U v i) :=
    hL.mulVec_eigenvectorBasis
  have heA : ∀ i, generator μ W *ᵥ (fun v => U v i) =
      (-(μ + a i)) • (fun v => U v i) := fun i => generator_eigenvector μ W _ _ (heL i)
  have hsimpleA := eigenvalues_injective_of_cyclic (generator μ W)
    (generator_symm μ W hs) b hcyc U _ hU heA
  have hsimple : Function.Injective a := by
    intro i j hij; apply hsimpleA; dsimp; rw [hij]
  have ha : ∀ i, 0 ≤ a i := hp.eigenvalues_nonneg
  have hdet : (laplacian W).det = 0 := by
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (i := (0 : Fin (n + 1))) (laplacian_const W 1)
    simp
  have hprod : ∏ i, a i = 0 := by
    simpa [Matrix.IsHermitian.det_eq_prod_eigenvalues hL, a] using hdet
  obtain ⟨g, _, hg⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hgroundL : laplacian W *ᵥ (fun v => U v g) = 0 := by
    rw [heL, hg, zero_smul]
  have hconst := laplacian_kernel_const W hs hn hc (fun v => U v g) hgroundL
  have hUne : ∀ i, (fun v => U v i) ≠ 0 := by
    intro i hz
    have hh := hU i i
    have hz' : ∀ v, U v i = 0 := congrFun hz
    simp [hz'] at hh
  have hOverlap : ∀ i, (fun v => U v i) ⬝ᵥ b ≠ 0 := fun i =>
    eigenvector_overlap_ne_zero (generator μ W) (generator_symm μ W hs)
      b _ hcyc _ (heA i) (hUne i)
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 g
  let s : Fin (n + 1) → ℝ := fun i => orientation ((fun v => U v (e i)) ⬝ᵥ b)
  let Q : Fin (n + 1) → Fin (n + 1) → ℝ := fun v i => s i * U v (e i)
  let rates : Fin (n + 1) → ℝ := fun i => μ + a (e i)
  have he0 : e 0 = g := by simp [e]
  have hQ : C145PhysicalFrame.ColumnOrthonormal Q :=
    oriented_frame U hU e s (fun i => orientation_sq _)
  have hQr : ∀ i, generator μ W *ᵥ (fun v => Q v i) =
      (-rates i) • (fun v => Q v i) := by
    intro i
    change generator μ W *ᵥ (s i • (fun v => U v (e i))) = _
    rw [Matrix.mulVec_smul, heA]
    dsimp [rates, Q]
    ext v; simp; ring
  have hgen := generator_eq_of_eigenframe (generator μ W) Q rates hQ hQr
  refine ⟨⟨Q, rates, s 0 * U 0 g, hQ, ?_, ?_, ?_, ?_, ?_, hQr, hgen, ?_⟩⟩
  · intro v; dsimp [Q]; rw [he0, hconst v 0]
  · intro i j hij; apply e.injective; apply hsimple; dsimp [rates] at hij; linarith
  · dsimp [rates]; rw [he0, hg, add_zero]
  · intro i
    have hne : a (e i.succ) ≠ 0 := by
      intro h; have hh := hsimple (h.trans hg.symm)
      have : i.succ = 0 := e.injective (hh.trans he0.symm)
      exact Fin.succ_ne_zero i this
    have hp' : 0 < a (e i.succ) := lt_of_le_of_ne (ha _) (Ne.symm hne)
    dsimp [rates]; linarith
  · intro i
    change 0 < ∑ v, b v * (s i * U v (e i))
    have heq : (∑ v, b v * (s i * U v (e i))) =
        s i * ((fun v => U v (e i)) ⬝ᵥ b) := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _; ring
    rw [heq]
    exact oriented_pos ((fun v => U v (e i)) ⬝ᵥ b) (hOverlap (e i))
  · funext v u
    change -C145CoordinatePermutation.spectralGenerator rates Q v u -
      μ * (if v = u then 1 else 0) = _
    rw [hgen]
    simp [generator, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

/-- Exact normalization and positive actual ground overlap determine the signed
ground orientation from the signed port mean. Neither is assumed positive. -/
theorem OrientedRealization.signed_ground {n : ℕ} {μ : ℝ}
    {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : Fin (n + 1) → ℝ}
    (S : OrientedRealization μ W b) :
    (n + 1 : ℝ) * S.c ^ 2 = 1 ∧ S.c ≠ 0 ∧
      0 < S.c * (∑ v, b v) ∧ (∑ v, b v) ≠ 0 := by
  have heq : C145.Pulse.modalOverlap S.Q b 0 = S.c * (∑ v, b v) := by
    unfold C145.Pulse.modalOverlap
    simp_rw [S.ground]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _; ring
  have hp := S.positive_overlap 0
  rw [heq] at hp
  refine ⟨C145PhysicalFrame.ground_normalization S.Q S.c S.orthonormal S.ground,
    C145PhysicalFrame.ground_ne_zero S.Q S.c S.orthonormal S.ground, hp, ?_⟩
  intro hz
  rw [hz, mul_zero] at hp
  exact lt_irrefl _ hp

/-- The ground rate is attained at exactly the derived ground index. -/
theorem OrientedRealization.unique_ground_rate {n : ℕ} {μ : ℝ}
    {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : Fin (n + 1) → ℝ}
    (S : OrientedRealization μ W b) (i : Fin (n + 1)) : S.rates i = μ ↔ i = 0 := by
  constructor
  · intro h; exact S.simple (h.trans S.ground_rate.symm)
  · rintro rfl; exact S.ground_rate

open C145.ActualResponse C145.ObservedKernelRecovery
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- The original graph ODE, stated in vertex coordinates with its actual matrix. -/
def graphVectorField {n : ℕ} (μ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : State n)
    (f : ℝ → ℝ) (t : ℝ) (x : State n) : State n :=
  fun v => (∑ w, generator μ W v w * x w) + x v ^ 2 + b v * f t

/-- A response map satisfying the local dynamics of the given weighted graph and port. -/
def IsGraphResponse {n : ℕ} {T : ℝ} (hT : 0 < T) (μ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : State n)
    (R : Input T → Path n T) : Prop :=
  R 0 = 0 ∧ ∀ᶠ f in 𝓝 (0 : Input T),
    extendPath hT (R f) 0 = 0 ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath hT (R f))
        (graphVectorField μ W b (extendInput hT f) t (extendPath hT (R f) t))
        (Set.Icc (0 : ℝ) T) t

/-- Matrix equality transports the caller's own actual response, including its
fixed-horizon neighborhood; no existence-only replacement response is used. -/
theorem OrientedRealization.actualResponse {n : ℕ} {T : ℝ} (hT : 0 < T)
    {μ : ℝ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : State n}
    (S : OrientedRealization μ W b) (R : Input T → Path n T)
    (hR : IsGraphResponse hT μ W b R) : IsActualResponse hT S.Q S.rates b R := by
  have hv : vectorField S.Q S.rates b = graphVectorField μ W b := by
    unfold vectorField graphVectorField
    rw [S.original_generator]
  unfold IsGraphResponse at hR
  unfold IsActualResponse
  rw [hv]
  exact hR

/-- Smooth terminal ordinary J2 data identify the original connected cyclic
weighted graph against an initially unrestricted-size competitor. Modal `e`
and vertex `π` are separately derived; all rates are full decay rates. -/
theorem ordinary_C2_jets_determine_small_graph {m n : ℕ} {T : ℝ}
    (hT : 0 < T) (μ : ℝ) (hμ : 0 < μ)
    (W0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (W1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hs0 : W0.IsSymm) (hs1 : W1.IsSymm)
    (hn0 : ∀ v u, 0 ≤ W0 v u) (hn1 : ∀ v u, 0 ≤ W1 v u)
    (hc0 : (supportGraph W0 hs0).Connected) (hc1 : (supportGraph W1 hs1).Connected)
    (b0 : State m) (b1 : State n)
    (hcyc0 : KrylovCyclic (generator μ W0) b0)
    (hcyc1 : KrylovCyclic (generator μ W1) b1)
    (hm : m ≤ 4)
    (R0 : Input T → Path m T) (R1 : Input T → Path n T)
    (hR0 : IsGraphResponse hT μ W0 b0 R0) (hR1 : IsGraphResponse hT μ W1 b1 R1)
    (hC0 : ContDiffAt ℝ 2 R0 0) (hC1 : ContDiffAt ℝ 2 R1 0)
    (hFirst : ∀ (g : ℝ → ℝ) (hg : SmoothTemporalTest T g),
      rawFirst b0 R0 (restrictInput T g hg.1.continuous) (endTime T hT) =
      rawFirst b1 R1 (restrictInput T g hg.1.continuous) (endTime T hT))
    (hMixed : ∀ (g h : ℝ → ℝ) (hg : SmoothTemporalTest T g) (hh : SmoothTemporalTest T h),
      rawMixed b0 R0 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT) =
      rawMixed b1 R1 (restrictInput T g hg.1.continuous) (restrictInput T h hh.1.continuous)
          (endTime T hT)) :
    ∃ (S0 : OrientedRealization μ W0 b0) (S1 : OrientedRealization μ W1 b1)
        (e : Fin (m + 1) ≃ Fin (n + 1)),
      m = n ∧ e 0 = 0 ∧ (∀ i, S1.rates (e i) = S0.rates i) ∧
      (∀ i, C145.Pulse.modalOverlap S1.Q b1 (e i) =
        C145.Pulse.modalOverlap S0.Q b0 i) ∧
      S0.c = S1.c ∧ (∑ v, b0 v) = (∑ v, b1 v) ∧
      ∃ π : Fin (m + 1) ≃ Fin (n + 1),
        (∀ v i, S1.Q (π v) (e i) = S0.Q v i) ∧
        (∀ v u, generator μ W1 (π v) (π u) = generator μ W0 v u) ∧
        (∀ v, b1 (π v) = b0 v) ∧
        (∀ v u, laplacian W1 (π v) (π u) = laplacian W0 v u) := by
  obtain ⟨S0⟩ := connected_cyclic_graph_has_oriented_spectral_realization
    μ hμ W0 hs0 hn0 hc0 b0 hcyc0
  obtain ⟨S1⟩ := connected_cyclic_graph_has_oriented_spectral_realization
    μ hμ W1 hs1 hn1 hc1 b1 hcyc1
  obtain ⟨e, hmn, he0, hr, ha, hc, hb, π, _, hQ, hA, hport, hL⟩ :=
    C145.FixedHorizonSmallInverse.ordinary_C2_jets_determine_small_spectral_model
      hT μ S0.c S1.c hμ S0.Q S1.Q S0.rates b0 S1.rates b1
      S0.orthonormal S1.orthonormal S0.ground S1.ground S0.simple S1.simple
      S0.ground_rate S1.ground_rate S0.higher S1.higher
      S0.positive_overlap S1.positive_overlap hm R0 R1
      (S0.actualResponse hT R0 hR0) (S1.actualResponse hT R1 hR1)
      hC0 hC1 hFirst hMixed
  refine ⟨S0, S1, e, hmn, he0, hr, ha, hc, hb, π, hQ, ?_, hport, ?_⟩
  · simpa only [S0.original_generator, S1.original_generator] using hA
  · simpa only [S0.original_laplacian, S1.original_laplacian] using hL

end C145.GraphSpectralRealization

end
