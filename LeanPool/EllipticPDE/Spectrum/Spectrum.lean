/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Fredholm.Compactness
public import Mathlib.Analysis.InnerProductSpace.Spectrum


/-!
# Eigenvalue theory for the symmetric elliptic Dirichlet problem

Evans §6.5.1, Theorem 1.

For a **symmetric coercive** bilinear form `B` on `H₀¹(Ω)` we build the solution operator on
`L²(Ω)` and apply Mathlib's spectral theorem for compact self-adjoint operators to obtain a
complete orthogonal family of eigenfunctions.

* `solOp B hco := ι ∘ (B♯)⁻¹ ∘ ι†  :  L²(Ω) →L[ℝ] L²(Ω)`, where `ι = embL2 Ω` is the Rellich
  embedding and `B♯⁻¹` is the Lax-Milgram inverse of the coercive form `B`.
* `solOp_isCompact`: `solOp` is compact, because `ι` is compact (Rellich) and the rest is bounded.
* `solOp_inner_symm`: `solOp` is symmetric, because `B` is symmetric (so `B♯` and `B♯⁻¹` are).
* `solOp_inner_self_nonneg`: `solOp` is positive, from coercivity.
* `solOp_spectral`: the **spectral theorem**: the eigenspaces of `solOp` span `L²(Ω)` (their
  orthogonal complement is trivial). The eigenvalues are of finite multiplicity
  (`ContinuousLinearMap.finite_dimensional_eigenspace`) and, by `solOp_eigenvalue_nonneg`,
  nonnegative.
* `solOp_weak_eigen`: each eigenpair `solOp φ = μ φ` lifts to a weak eigenfunction `u ∈ H₀¹(Ω)`
  of the elliptic operator: `⟪u, v⟫_{L²} = μ B[u, v]` for all `v`, i.e. `B[u, v] = λ ⟪u, v⟫_{L²}`
  with the elliptic eigenvalue `λ = μ⁻¹`. Letting `μ → 0⁺` gives the Dirichlet eigenvalues
  `λ → +∞`.

Instantiated on the Dirichlet (Poisson) form `laplaceBilin`, giving the eigenvalue theory of
`-Δ` with Dirichlet boundary data (`dirichlet_spectral`). The compact embedding for bounded `Ω`
is the single analytic input, threaded as the hypothesis `IsCompactOperator (embL2 Ω)`
(Rellich-Kondrachov) exactly as in `Compactness.lean`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The **solution operator** on `L²(Ω)` of a coercive form `B`: `G = ι ∘ (B♯)⁻¹ ∘ ι†`, with
`ι = embL2 Ω` the Rellich embedding and `(B♯)⁻¹` the Lax-Milgram inverse of `B`. -/
def solOp (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) (hco : IsCoercive B) : L2D Ω →L[ℝ] L2D Ω :=
  (embL2 Ω).comp
    ((hco.continuousLinearEquivOfBilin.symm : H01 Ω →L[ℝ] H01 Ω).comp (embL2 Ω).adjoint)

variable {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-- Evaluation: `solOp B hco f = embL2 Ω ((B♯)⁻¹ ((embL2 Ω)† f))`. -/
lemma solOp_apply (hco : IsCoercive B) (f : L2D Ω) :
    solOp B hco f
      = embL2 Ω (hco.continuousLinearEquivOfBilin.symm ((embL2 Ω).adjoint f)) := by
  simp only [solOp, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-! ### `B♯` and `(B♯)⁻¹` are symmetric when `B` is -/

/-- The Riesz representative `B♯` of a symmetric form is symmetric: `⟪B♯ u, v⟫ = ⟪u, B♯ v⟫`. -/
lemma clEquiv_symm_form (hco : IsCoercive B) (hsymm : ∀ U V, B U V = B V U) (u v : H01 Ω) :
    ⟪hco.continuousLinearEquivOfBilin u, v⟫ = ⟪u, hco.continuousLinearEquivOfBilin v⟫ := by
  rw [hco.continuousLinearEquivOfBilin_apply, real_inner_comm,
    hco.continuousLinearEquivOfBilin_apply]
  exact hsymm u v

/-- The Lax-Milgram inverse `(B♯)⁻¹` of a symmetric coercive form is symmetric. -/
lemma clEquivSymm_symm_form (hco : IsCoercive B) (hsymm : ∀ U V, B U V = B V U) (u v : H01 Ω) :
    ⟪hco.continuousLinearEquivOfBilin.symm u, v⟫
      = ⟪u, hco.continuousLinearEquivOfBilin.symm v⟫ := by
  set T := hco.continuousLinearEquivOfBilin with hT
  calc ⟪T.symm u, v⟫
      = ⟪T.symm u, T (T.symm v)⟫ := by rw [ContinuousLinearEquiv.apply_symm_apply]
    _ = ⟪T (T.symm u), T.symm v⟫ := (clEquiv_symm_form hco hsymm (T.symm u) (T.symm v)).symm
    _ = ⟪u, T.symm v⟫ := by rw [ContinuousLinearEquiv.apply_symm_apply]

/-! ### Compactness, symmetry, positivity of the solution operator -/

/-- The solution operator is **compact**: it is the compact embedding `ι` postcomposed with the
bounded operator `(B♯)⁻¹ ∘ ι†`. -/
lemma solOp_isCompact (hco : IsCoercive B) (hRellich : IsCompactOperator (embL2 Ω)) :
    IsCompactOperator (solOp B hco) :=
  hRellich.comp_clm
    ((hco.continuousLinearEquivOfBilin.symm : H01 Ω →L[ℝ] H01 Ω).comp (embL2 Ω).adjoint)

/-- The solution operator is **symmetric**: `⟪G f, g⟫ = ⟪f, G g⟫`, because `(B♯)⁻¹` is symmetric
and `ι`, `ι†` are mutual adjoints. -/
lemma solOp_inner_symm (hco : IsCoercive B) (hsymm : ∀ U V, B U V = B V U) (f g : L2D Ω) :
    ⟪solOp B hco f, g⟫ = ⟪f, solOp B hco g⟫ := by
  rw [solOp_apply, solOp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (embL2 Ω)
      (hco.continuousLinearEquivOfBilin.symm ((embL2 Ω).adjoint f)) g).symm.trans
    ((clEquivSymm_symm_form hco hsymm ((embL2 Ω).adjoint f) ((embL2 Ω).adjoint g)).trans
      (ContinuousLinearMap.adjoint_inner_left (embL2 Ω)
        (hco.continuousLinearEquivOfBilin.symm ((embL2 Ω).adjoint g)) f))

/-- The solution operator is **positive**: `0 ≤ ⟪G f, f⟫`, from coercivity of `B`. -/
lemma solOp_inner_self_nonneg (hco : IsCoercive B) (f : L2D Ω) :
    0 ≤ ⟪solOp B hco f, f⟫ := by
  rw [solOp_apply, ← ContinuousLinearMap.adjoint_inner_right]
  set w := hco.continuousLinearEquivOfBilin.symm ((embL2 Ω).adjoint f) with hw
  have ha : (embL2 Ω).adjoint f = hco.continuousLinearEquivOfBilin w := by
    rw [hw, ContinuousLinearEquiv.apply_symm_apply]
  rw [ha, real_inner_comm, hco.continuousLinearEquivOfBilin_apply]
  obtain ⟨C, hC, hcoer⟩ := hco
  nlinarith [hcoer w, mul_nonneg (mul_nonneg hC.le (norm_nonneg w)) (norm_nonneg w)]

/-! ### Spectral theorem and eigenfunction correspondence -/

/-- **Spectral theorem for the symmetric elliptic Dirichlet problem** (Evans §6.5). Given the
Rellich compact embedding, the eigenspaces of the solution operator span `L²(Ω)`: their
orthogonal complement is trivial. Equivalently, `L²(Ω)` has an orthonormal basis of
eigenfunctions of the solution operator. -/
theorem solOp_spectral (hco : IsCoercive B) (hsymm : ∀ U V, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) :
    (⨆ μ : ℝ, Module.End.eigenspace (solOp B hco : Module.End ℝ (L2D Ω)) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (solOp_isCompact hco hRellich)
    (by intro x y; simpa using solOp_inner_symm hco hsymm x y)

/-- **Eigenfunction correspondence.** Each eigenpair `solOp φ = μ φ` lifts to a weak eigenfunction
`u ∈ H₀¹(Ω)` of the elliptic operator: `ι u = μ φ` and `⟪u, v⟫_{L²} = μ B[u, v]` for every
`v ∈ H₀¹(Ω)`. For `μ ≠ 0` this is the weak Dirichlet eigenvalue problem `B[u, v] = λ ⟪u, v⟫_{L²}`
with elliptic eigenvalue `λ = μ⁻¹`. -/
theorem solOp_weak_eigen (hco : IsCoercive B) {μ : ℝ} {φ : L2D Ω}
    (hφ : solOp B hco φ = μ • φ) :
    ∃ u : H01 Ω, embL2 Ω u = μ • φ ∧
      ∀ v : H01 Ω, ⟪embL2 Ω u, embL2 Ω v⟫ = μ * B u v := by
  set u := hco.continuousLinearEquivOfBilin.symm ((embL2 Ω).adjoint φ) with hu
  have hiu : embL2 Ω u = μ • φ := by rw [hu, ← solOp_apply hco]; exact hφ
  refine ⟨u, hiu, fun v => ?_⟩
  have hBuv : B u v = ⟪φ, embL2 Ω v⟫ := by
    rw [← hco.continuousLinearEquivOfBilin_apply, hu,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]
  rw [hiu, hBuv, real_inner_smul_left]

/-- The eigenvalues of the solution operator are **nonnegative** (so the elliptic eigenvalues
`λ = μ⁻¹` are positive): positivity of `G` forces `0 ≤ μ` on any nonzero eigenvector. -/
theorem solOp_eigenvalue_nonneg (hco : IsCoercive B) {μ : ℝ} {φ : L2D Ω}
    (hφ : solOp B hco φ = μ • φ) (hφ0 : φ ≠ 0) : 0 ≤ μ := by
  have h1 : 0 ≤ ⟪solOp B hco φ, φ⟫ := solOp_inner_self_nonneg hco φ
  rw [hφ, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
  have hpos : 0 < ‖φ‖ ^ 2 := by
    have := norm_pos_iff.mpr hφ0; positivity
  by_contra h
  rw [not_le] at h
  linarith [mul_neg_of_neg_of_pos h hpos]

/-! ### Instantiation at the Dirichlet (Poisson) form `-Δ` -/

/-- The bilinear form of the Laplacian is symmetric. -/
lemma laplaceBilin_symm (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    laplaceBilin Ω U V = laplaceBilin Ω V U := by
  rw [laplaceBilin_apply, laplaceBilin_apply]
  exact Finset.sum_congr rfl (fun i _ => real_inner_comm _ _)

/-- **Spectral theorem for the Dirichlet Laplacian** (`-Δ` with Dirichlet data, Evans §6.5).
Given the test-function Poincaré bound (coercivity) and the Rellich compact embedding, the
eigenfunctions of the Dirichlet solution operator form a complete orthogonal family in `L²(Ω)`. -/
theorem dirichlet_spectral (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hRellich : IsCompactOperator (embL2 Ω)) :
    (⨆ μ : ℝ, Module.End.eigenspace
        (solOp (laplaceBilin Ω) (laplaceBilin_coercive Ω CP hCP hbase)
          : Module.End ℝ (L2D Ω)) μ)ᗮ = ⊥ :=
  solOp_spectral (laplaceBilin_coercive Ω CP hCP hbase) (laplaceBilin_symm Ω) hRellich

/-! ### Instantiation at the general symmetric divergence-form operator `-Dⱼ(aᵢⱼ Dᵢ·) + c` -/

/-- The principal-part form `B_A` is symmetric when the coefficient matrix is symmetric
(`aᵢⱼ = aⱼᵢ` a.e. on `Ω`): swap the summation order and use `a` symmetry plus
commutativity of the product. -/
lemma EllipticCoeff.bilin_symm (A : EllipticCoeff d)
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hAsymm : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, A.a x i j = A.a x j i)
    (U V : H01 Ω) : A.bilin Ω U V = A.bilin Ω V U := by
  rw [EllipticCoeff.bilin_apply, EllipticCoeff.bilin_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [A.inner_actL_eq, A.inner_actL_eq]
  refine integral_congr_ae (hAsymm.mono (fun x hx => ?_))
  dsimp only
  rw [hx b a]; ring

/-- The full divergence form `B = B_A + (transport + zeroth)` is symmetric when the transport
field vanishes (`b ≡ 0`) and the matrix is symmetric: the principal part is symmetric by
`EllipticCoeff.bilin_symm`, the transport terms vanish, and the zeroth term `⟪c u₀, v₀⟫` is
symmetric. -/
private lemma FullEllipticOp.fullBilin_symm (Op : FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hAsymm : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, Op.a x i j = Op.a x j i)
    (U V : H01 Ω) :
    Op.fullBilin Ω U V = Op.fullBilin Ω V U := by
  rw [Op.fullBilin_apply, Op.fullBilin_apply]
  congr 1
  · exact Op.toEllipticCoeff.bilin_symm Ω hAsymm U V
  · rw [Op.lowerBilin_apply, Op.lowerBilin_apply]
    have hz : ∀ P Q : H01 Ω,
        (∑ i : Fin d, ⟪Op.bAct i ((P : H1amb Ω) i.succ), ((Q : H1amb Ω) 0)⟫) = 0 := by
      intro P Q
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp only [FullEllipticOp.bAct]
      rw [inner_mulCoeffL_eq]
      have hzero : ∀ᵐ x ∂(volume.restrict Ω),
          Op.b x i * ((P : H1amb Ω) i.succ x : ℝ) * ((Q : H1amb Ω) 0 x : ℝ) = 0 :=
        (hb i).mono fun x hx => by rw [hx, zero_mul, zero_mul]
      calc (∫ x in Ω, Op.b x i * ((P : H1amb Ω) i.succ x : ℝ) * ((Q : H1amb Ω) 0 x : ℝ))
          = ∫ _x in Ω, (0 : ℝ) := integral_congr_ae hzero
        _ = 0 := integral_zero _ _
    rw [hz U V, hz V U, zero_add, zero_add]
    simp only [FullEllipticOp.cAct]
    rw [inner_mulCoeffL_eq, inner_mulCoeffL_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    ring

/-- **Spectral theorem for the general symmetric divergence-form operator** `Lu = -Dⱼ(aᵢⱼ Dᵢu) + cu`
with symmetric matrix `A`, no transport (`b ≡ 0`), and `c ≥ 0` (Evans §6.5). Given the
test-function Poincaré bound and the Rellich compact embedding, the eigenfunctions of the
solution operator form a complete orthogonal family in `L²(Ω)`. -/
theorem symmetric_fullElliptic_spectral (Op : FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (hAsymm : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, Op.a x i j = Op.a x j i)
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hRellich : IsCompactOperator (embL2 Ω)) :
    (⨆ μ : ℝ, Module.End.eigenspace
        (solOp (Op.fullBilin Ω) (Op.fullBilin_coercive_of_nonneg_zeroth Ω hb hc CP hCP hbase)
          : Module.End ℝ (L2D Ω)) μ)ᗮ = ⊥ :=
  solOp_spectral _ (Op.fullBilin_symm Ω hb hAsymm) hRellich

end EllipticPdes.Sobolev
