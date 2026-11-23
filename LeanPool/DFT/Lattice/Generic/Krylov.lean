/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.HK.Basic
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Algebra.MvPolynomial
meta import Mathlib.Tactic.Push

/-!
# The Krylov criterion and generic Hohenberg–Kohn (topological version)

* `det_kry_eq_zero`: an eigenvector of a symmetric `H` vanishing on configuration `c` makes the
  Krylov matrix `[e_c, H e_c, H² e_c, …]` singular.
* `krylovPoly`: that determinant, for `H = H(v)`, is a polynomial in the potential.
* `nonUV_imp_krylov_zero`: non-unique v-representability forces a zero of some Krylov polynomial.
* `generic_hk`: if all Krylov polynomials are nonzero (hypothesis (H*)),
  non-uniquely-v-representable potentials lie in a closed set with empty interior.
-/

@[expose] public section

namespace DFT

section

open Matrix MvPolynomial

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

/-- Krylov matrix of `e_c` under `H`; column `j` is `H ^ (ord j) e_c`. -/
def kry {R : Type*} [CommRing R] (H : Matrix C C R) (c : C) (ord : C → ℕ) : Matrix C C R :=
  fun i j => (H ^ ord j) i c

lemma det_kry_eq_zero {H : Matrix C C ℝ} (hS : H.IsSymm) {ψ : C → ℝ} {E : ℝ}
    (hψ : ψ ≠ 0) (hE : H *ᵥ ψ = E • ψ) {c : C} (hc : ψ c = 0) (ord : C → ℕ) :
    (kry H c ord).det = 0 := by
  rw [← exists_vecMul_eq_zero_iff]
  refine ⟨ψ, hψ, ?_⟩
  have h1 : ψ ᵥ* H = E • ψ := by
    conv_lhs => rw [← hS.eq]
    rw [vecMul_transpose, hE]
  have hv : ∀ k : ℕ, ψ ᵥ* (H ^ k) = E ^ k • ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul, h1, smul_smul, pow_succ]
  funext j
  have := congrFun (hv (ord j)) c
  simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hc, mul_zero] at this
  simpa [vecMul, dotProduct, kry] using this

/-- The Hamiltonian with the potential as polynomial variables. -/
noncomputable def hamP (H0 : Matrix C C ℝ) (n : V → C → ℝ) : Matrix C C (MvPolynomial V ℝ) :=
  H0.map MvPolynomial.C + Matrix.diagonal (fun c => ∑ i, MvPolynomial.X i * MvPolynomial.C (n i c))

omit [Fintype C] [DecidableEq V] in
lemma hamP_eval (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) :
    (hamP H0 n).map (MvPolynomial.eval v) = hamN H0 n v := by
  ext a b
  by_cases h : a = b
  · subst h; simp [hamP, hamN, Matrix.diagonal, mul_comm]
  · simp [hamP, hamN, Matrix.diagonal, h]

/-- Krylov polynomial of configuration `c`. -/
noncomputable def krylovPoly (H0 : Matrix C C ℝ) (n : V → C → ℝ) (c : C) (ord : C → ℕ) :
    MvPolynomial V ℝ :=
  (kry (hamP H0 n) c ord).det

omit [DecidableEq V] in
lemma eval_krylovPoly (H0 : Matrix C C ℝ) (n : V → C → ℝ) (c : C) (ord : C → ℕ) (v : V → ℝ) :
    MvPolynomial.eval v (krylovPoly H0 n c ord) = (kry (hamN H0 n v) c ord).det := by
  rw [krylovPoly, RingHom.map_det, ← hamP_eval]
  congr 1
  ext i j
  have hp : ((hamP H0 n).map (MvPolynomial.eval v)) ^ ord j =
      ((hamP H0 n) ^ ord j).map (MvPolynomial.eval v) := by
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  simp only [kry, RingHom.mapMatrix_apply, Matrix.map_apply, hp]

omit [DecidableEq V] in
theorem nonUVMod_imp_krylov_zero {Tr : Set (V → ℝ)} {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm)
    {n : V → C → ℝ} (hR : RigidMod Tr n) {v : V → ℝ} (h : NonUVMod Tr H0 n v) (ord : C → ℕ) :
    ∃ c, MvPolynomial.eval v (krylovPoly H0 n c ord) = 0 := by
  obtain ⟨ψ, v', hψ, hψ', hne⟩ := h
  have hS := hamN_isSymm hH0 n v
  have hS' := hamN_isSymm hH0 n v'
  have hE := isGroundState_eigen hS hψ
  have hE' := isGroundState_eigen hS' hψ'
  -- some amplitude vanishes
  have hz : ∃ c, ψ c = 0 := by
    by_contra hall
    push Not at hall
    apply hne
    exact hR (v - v') _ fun c => potential_sub_eq_on_support hE hE' (hall c)
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, by rw [eval_krylovPoly]; exact det_kry_eq_zero hS hψ.1 hE hc ord⟩

omit [DecidableEq V] in
theorem nonUV_imp_krylov_zero {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hR : Rigid n)
    {v : V → ℝ} (h : NonUV H0 n v) (ord : C → ℕ) :
    ∃ c, MvPolynomial.eval v (krylovPoly H0 n c ord) = 0 :=
  nonUVMod_imp_krylov_zero (Tr := constPot) hH0 hR h ord

omit [Fintype V] [DecidableEq V] in
/-- A real polynomial vanishing on a nonempty open set is the zero polynomial. -/
theorem eq_zero_of_vanish_on_open [Finite V] {P : MvPolynomial V ℝ} {U : Set (V → ℝ)}
    (hU : IsOpen U)
    {z : V → ℝ} (hz : z ∈ U) (h : ∀ v ∈ U, MvPolynomial.eval v P = 0) : P = 0 := by
  let := Fintype.ofFinite V
  have han : AnalyticOnNhd ℝ (fun x : V → ℝ => MvPolynomial.eval x P) Set.univ := by
    simpa using AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℝ (V → ℝ)) P
  have hev : (fun x : V → ℝ => MvPolynomial.eval x P) =ᶠ[nhds z] 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hz) (fun x hx => h x hx)
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hev
  apply MvPolynomial.funext
  intro x
  simpa using this (Set.mem_univ x)

omit [Fintype V] [DecidableEq V] in
/-- Zero set of a nonzero polynomial: closed with empty interior. -/
theorem zeroSet_closed_nowhere [Finite V] {P : MvPolynomial V ℝ} (hP : P ≠ 0) :
    IsClosed {v : V → ℝ | MvPolynomial.eval v P = 0} ∧
      interior {v : V → ℝ | MvPolynomial.eval v P = 0} = ∅ := by
  let := Fintype.ofFinite V
  refine ⟨isClosed_eq (MvPolynomial.continuous_eval P) continuous_const, ?_⟩
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact hP (eq_zero_of_vanish_on_open isOpen_interior hz (fun v hv => interior_subset hv))

omit [DecidableEq V] in
/-- A product of Krylov polynomials vanishes on every potential shared modulo `Tr`. -/
theorem exists_krylov_certificate {Tr : Set (V → ℝ)} {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm)
    {n : V → C → ℝ} (hR : RigidMod Tr n) (ord : C → ℕ)
    (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ P : MvPolynomial V ℝ, P ≠ 0 ∧ ∀ v, NonUVMod Tr H0 n v → MvPolynomial.eval v P = 0 := by
  refine ⟨∏ c, krylovPoly H0 n c ord, Finset.prod_ne_zero_iff.mpr (fun c _ => hstar c), ?_⟩
  intro v hv
  obtain ⟨c, hc⟩ := nonUVMod_imp_krylov_zero hH0 hR hv ord
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) hc

omit [DecidableEq V] in
/-- **Generic Hohenberg–Kohn modulo trivial shifts (conditional on (H*)).** -/
theorem generic_hk_mod {Tr : Set (V → ℝ)} {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ}
    (hR : RigidMod Tr n) (ord : C → ℕ) (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ {v | NonUVMod Tr H0 n v} ⊆ Z := by
  obtain ⟨Q, hQ, hvanish⟩ := exists_krylov_certificate hH0 hR ord hstar
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  exact ⟨_, hcl, hint, hvanish⟩

omit [DecidableEq V] in
/-- **Generic Hohenberg–Kohn (conditional on (H*)).** If the occupations are rigid and, for every
configuration `c`, the Krylov polynomial is nonzero, then all non-uniquely-v-representable
potentials lie in a closed set with empty interior. -/
theorem generic_hk {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hR : Rigid n)
    (ord : C → ℕ) (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ {v | NonUV H0 n v} ⊆ Z :=
  generic_hk_mod (Tr := constPot) hH0 hR ord hstar

end

end DFT
