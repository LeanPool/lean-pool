/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GNSMatrixCoefficients
public import LeanPool.VacuumBellSeparation.Bell.HilbertSumVectorDomination
public import LeanPool.VacuumBellSeparation.Bell.NormalStateMixtures

/-!
# Normality of the actual GNS representation on positive directed suprema

Compression normality supplies the matrix-element limit on the genuine dense
cyclic orbit. The bounded monotone operator net has a strong limit; positivity
and density identify that limit with the image of the original supremum.
No normal representation, vector-state realization or VNA image is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Cache the canonical completed GNS structures locally; no extra structure
-- or hypothesis is introduced, and downstream instance search is unchanged.
/-- Normed additive group of the completed GNS Hilbert space used for directed limits. -/
abbrev gnsDirectedNormedGroup (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : NormedAddCommGroup φ.GNS := inferInstance

attribute [local instance] gnsDirectedNormedGroup

/-- The canonical `InnerProductSpace ℂ φ.GNS` instance used in the construction. -/
abbrev gnsDirectedInnerSpace (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : InnerProductSpace ℂ φ.GNS := inferInstance

attribute [local instance] gnsDirectedInnerSpace

/-- The canonical `CompleteSpace φ.GNS` instance used in the construction. -/
abbrev gnsDirectedComplete (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) : CompleteSpace φ.GNS := inferInstance

attribute [local instance] gnsDirectedComplete

/-- Generic dense quadratic-form determination, separated from the concrete
GNS elaboration so the latter only supplies its literal dense orbit. -/
private theorem operator_eq_of_le_dense_real_diagonal
    {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U V : E →L[ℂ] E) (hUV : U ≤ V) (v : I → E) (hv : DenseRange v)
    (hd : ∀ i, (inner ℂ (v i) (U (v i))).re =
      (inner ℂ (v i) (V (v i))).re) : U = V := by
  have he (y : E) : (inner ℂ y (U y)).re = (inner ℂ y (V y)).re := by
    exact hv.induction_on y
      (isClosed_eq
        (Complex.continuous_re.comp (continuous_id.inner U.continuous))
        (Complex.continuous_re.comp (continuous_id.inner V.continuous))) hd
  have hzero (y : E) : (V - U) y = 0 := by
    have hb := Gaussian.norm_apply_sq_le_norm_mul_inner (sub_nonneg.mpr hUV) y
    have hq : (inner ℂ y ((V - U) y)).re = 0 := by
      simp only [sub_apply, inner_sub_right, Complex.sub_re]
      exact sub_eq_zero.mpr (he y).symm
    rw [hq, mul_zero] at hb
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg ((V - U) y)]
  exact (sub_eq_zero.mp (ContinuousLinearMap.ext hzero)).symm

/-- A bounded monotone positive net converges strongly to an operator if the
real diagonal coefficients converge to its coefficients on a dense family. -/
theorem strong_tendsto_of_monotone_of_dense_diagonal
    {E I D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (A : I → E →L[ℂ] E) (Y : E →L[ℂ] E) (orbit : D → E) (hdense : DenseRange orbit)
    (hmono : Monotone A) (hpos : ∀ i, 0 ≤ A i) (hbound : ∀ i, A i ≤ Y)
    (hdiag : ∀ a, Tendsto (fun i => (inner ℂ (orbit a) (A i (orbit a))).re) atTop
      (𝓝 (inner ℂ (orbit a) (Y (orbit a))).re)) (x : E) :
    Tendsto (fun i => A i x) atTop (𝓝 (Y x)) := by
  obtain ⟨B, hB, _, hsup⟩ :=
    Gaussian.exists_strongLimit_of_monotone_nonneg_bounded A hmono hpos Y hbound
  have hBbound : B ≤ Y := hsup.2 (by rintro _ ⟨i, rfl⟩; exact hbound i)
  have heq : B = Y := by
    apply operator_eq_of_le_dense_real_diagonal B Y hBbound orbit hdense
    intro a
    have hvalue : Tendsto (fun i => inner ℂ (orbit a) (A i (orbit a))) atTop
        (𝓝 (inner ℂ (orbit a) (B (orbit a)))) :=
      tendsto_const_nhds.inner (hB (orbit a))
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hvalue
    exact tendsto_nhds_unique hre (hdiag a)
  exact heq ▸ hB x

theorem gns_real_diagonal_tendsto_on_cyclic_orbit (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ T ∈ s, 0 ≤ T) {X : M.toStarSubalgebra} (hX : IsLUB s X)
    (a : M.toStarSubalgebra) :
    Tendsto (fun i : s => (inner ℂ (φ.gnsStarAlgHom a (gnsUnitVector φ))
      (φ.gnsStarAlgHom i.1 (φ.gnsStarAlgHom a (gnsUnitVector φ)))).re) atTop
      (𝓝 (inner ℂ (φ.gnsStarAlgHom a (gnsUnitVector φ))
        (φ.gnsStarAlgHom X (φ.gnsStarAlgHom a (gnsUnitVector φ)))).re) := by
  simp only [gns_matrix_coefficient]
  exact positiveFunctional_real_tendsto_of_normal M (compressionFunctional φ a)
    (hn.compression a) hs hd hp hX

/-- The actual GNS image of every internal positive directed supremum is the
strong operator limit on the entire completed GNS Hilbert space. -/
theorem gns_strong_tendsto_of_isLUB_positive (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ T ∈ s, 0 ≤ T) {X : M.toStarSubalgebra} (hX : IsLUB s X)
    (x : φ.GNS) :
    Tendsto (fun i : s => φ.gnsStarAlgHom i.1 x) atTop (𝓝 (φ.gnsStarAlgHom X x)) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  let A : s → φ.GNS →L[ℂ] φ.GNS := fun i => φ.gnsStarAlgHom i.1
  let Y : φ.GNS →L[ℂ] φ.GNS := φ.gnsStarAlgHom X
  let orbit (a : M.toStarSubalgebra) : φ.GNS := φ.gnsStarAlgHom a (gnsUnitVector φ)
  exact strong_tendsto_of_monotone_of_dense_diagonal A Y orbit (gnsUnitVector_dense_orbit φ)
    (fun _ _ h => gnsStarAlgHom_monotone φ h)
    (fun i => gnsStarAlgHom_nonneg φ (hp i.1 i.2))
    (fun i => gnsStarAlgHom_monotone φ (hX.1 i.2))
    (gns_real_diagonal_tendsto_on_cyclic_orbit M φ hn hs hd hp hX) x

/-- Supremum preservation holds in the full bounded-operator order, not only
in a possibly nonclosed image subalgebra. -/
theorem gns_isLUB_image_positive (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    {s : Set M.toStarSubalgebra} (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ T ∈ s, 0 ≤ T) {X : M.toStarSubalgebra} (hX : IsLUB s X) :
    IsLUB (φ.gnsStarAlgHom '' s) (φ.gnsStarAlgHom X) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact gnsStarAlgHom_monotone φ (hX.1 hY)
  · intro Y hY
    exact Gaussian.operator_le_of_strong_tendsto
      (gns_strong_tendsto_of_isLUB_positive M φ hn hs hd hp hX)
      (fun _ => tendsto_const_nhds)
      (Eventually.of_forall fun i : s => hY ⟨i.1, i.2, rfl⟩)

/-- Every vector functional pulled back through this actual GNS representation
is order-normal for arbitrary positive directed suprema. -/
theorem gns_vectorFunctional_isNormal (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) (x : φ.GNS) :
    IsNormalFunctional M (fun X => inner ℂ x (φ.gnsStarAlgHom X x)) := by
  intro s hs hd hp X hX
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  have ht : Tendsto (fun i : s => (inner ℂ x (φ.gnsStarAlgHom i.1 x)).re) atTop
      (𝓝 (inner ℂ x (φ.gnsStarAlgHom X x)).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner (gns_strong_tendsto_of_isLUB_positive M φ hn hs hd hp hX x))
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    have h := (ContinuousLinearMap.le_def.mp
      (gnsStarAlgHom_monotone φ (hX.1 hY))).re_inner_nonneg_right x
    simpa [inner_sub_right, sub_nonneg] using h
  · intro r hr
    exact le_of_tendsto ht (Eventually.of_forall fun i : s => hr ⟨i.1, i.2, rfl⟩)

/-- GNS vector positive linear map obtained from `representationVectorPositiveLinearMap`. -/
def gnsVectorPositiveLinearMap (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (x : φ.GNS) :
    M.toStarSubalgebra →ₚ[ℂ] ℂ :=
  representationVectorPositiveLinearMap φ.gnsStarAlgHom x

theorem gns_vectorFunctional_isNormalState (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ)
    (x : φ.GNS) (hx : ‖x‖ = 1) :
    IsNormalStateFunctional M (fun X => inner ℂ x (φ.gnsStarAlgHom X x)) := by
  refine ⟨⟨gnsVectorPositiveLinearMap M φ x, ?_, fun _ => rfl⟩,
    gns_vectorFunctional_isNormal M φ hn x⟩
  change inner ℂ x (φ.gnsStarAlgHom 1 x) = 1
  have hone : φ.gnsStarAlgHom (1 : M.toStarSubalgebra) = 1 :=
    φ.gnsStarAlgHom.map_one
  rw [hone]
  change inner ℂ x x = 1
  rw [inner_self_eq_norm_sq_to_K, hx]; norm_num

end VacuumBellSeparation.Bipartite
