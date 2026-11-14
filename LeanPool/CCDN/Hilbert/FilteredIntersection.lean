/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import LeanPool.CCDN.ForMathlib.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Filtered multiples in a two-equation ideal

The intersection of the bounded-degree multiples of two coprime equations consists
exactly of bounded-degree multiples of their product.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Multiples of `f` whose multiplier has the degree allowed by cutoff `N`. -/
def filteredMultiples {K σ : Type*} [Field K] (f : MvPolynomial σ K) (N : ℕ) :
    Submodule K (MvPolynomial σ K) :=
  (restrictTotalDegree σ K (N - f.totalDegree)).map (LinearMap.mulLeft K f)

/-- `x` is a filtered multiple of `f` at level `N` if and only if `x = f * u` with `u` of total
degree at most `N - deg f`. -/
lemma mem_filteredMultiples {K σ : Type*} [Field K] (f x : MvPolynomial σ K) (N : ℕ) :
    x ∈ filteredMultiples f N ↔ ∃ u, u.totalDegree ≤ N - f.totalDegree ∧ f * u = x := by
  simp [filteredMultiples, Submodule.mem_map, mem_restrictTotalDegree, LinearMap.mulLeft_apply]

/-- If `deg f ≤ N`, the filtered multiples of `f` at level `N` have total degree at most `N`. -/
lemma filteredMultiples_le_degree {K σ : Type*} [Field K] (f : MvPolynomial σ K)
    {N : ℕ} (hN : f.totalDegree ≤ N) : filteredMultiples f N ≤ restrictTotalDegree σ K N := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (mem_filteredMultiples f x N).mp hx
  rw [mem_restrictTotalDegree]
  exact (totalDegree_mul _ _).trans (by omega)

instance filteredMultiples_finite {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial σ K) (N : ℕ) : Module.Finite K (filteredMultiples f N) := by
  unfold filteredMultiples
  infer_instance

/-- For `f ≠ 0`, the space of filtered multiples of `f` at level `N` has the dimension of the space
of polynomials of total degree at most `N - deg f`. -/
lemma filteredMultiples_finrank {K σ : Type*} [Field K] (f : MvPolynomial σ K)
    (hf : f ≠ 0) (N : ℕ) :
    Module.finrank K (filteredMultiples f N) =
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) := by
  exact (Submodule.equivMapOfInjective (LinearMap.mulLeft K f)
    (fun x y h => mul_left_cancel₀ hf h) _).finrank_eq.symm

/-- Exact intersection of the two spaces of bounded-degree multiples. -/
private theorem filteredMultiples_inf {K σ : Type*} [Field K]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    filteredMultiples f N ⊓ filteredMultiples g N = filteredMultiples (f * g) N := by
  have hg : g ≠ 0 := by intro h; exact hfg (h ▸ dvd_zero f)
  have hprod := totalDegree_mul_of_isDomain hf.ne_zero hg
  ext x
  constructor
  · rintro ⟨hxf, hxg⟩
    obtain ⟨u, hu, hux⟩ := (mem_filteredMultiples f x N).mp hxf
    obtain ⟨v, hv, hvx⟩ := (mem_filteredMultiples g x N).mp hxg
    have hdvd : f ∣ g * v := ⟨u, hux.trans hvx.symm |>.symm⟩
    obtain ⟨w, hw⟩ := (hf.dvd_or_dvd hdvd).resolve_left hfg
    have hfu : f * u = f * (g * w) := by rw [hux, ← hvx, hw]; ring
    have huw : u = g * w := mul_left_cancel₀ hf.ne_zero hfu
    apply (mem_filteredMultiples (f * g) x N).mpr
    refine ⟨w, ?_, ?_⟩
    · rw [hprod]
      by_cases hw0 : w = 0
      · simp [hw0]
      rw [hw, totalDegree_mul_of_isDomain hf.ne_zero hw0] at hv
      omega
    · rw [mul_assoc, ← huw, hux]
  · intro hx
    obtain ⟨w, hw, hwx⟩ := (mem_filteredMultiples (f * g) x N).mp hx
    rw [hprod] at hw
    constructor
    · apply (mem_filteredMultiples f x N).mpr
      refine ⟨g * w, (totalDegree_mul _ _).trans (by omega), ?_⟩
      simpa [mul_assoc] using hwx
    · apply (mem_filteredMultiples g x N).mpr
      refine ⟨f * w, (totalDegree_mul _ _).trans (by omega), ?_⟩
      simpa [mul_assoc, mul_comm, mul_left_comm] using hwx


/-- Dimension inclusion-exclusion for the bounded-degree multiples. -/
private theorem filteredMultiples_sup_finrank {K σ : Type*} [Field K] [Finite σ]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K ↥(filteredMultiples f N ⊔ filteredMultiples g N) +
      Module.finrank K (restrictTotalDegree σ K (N - (f.totalDegree + g.totalDegree))) =
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) +
      Module.finrank K (restrictTotalDegree σ K (N - g.totalDegree)) := by
  have hg : g ≠ 0 := by intro h; exact hfg (h ▸ dvd_zero f)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (filteredMultiples f N) (filteredMultiples g N)
  rw [filteredMultiples_inf hf hfg hN, filteredMultiples_finrank _ hf.ne_zero,
    filteredMultiples_finrank _ hg, filteredMultiples_finrank _ (mul_ne_zero hf.ne_zero hg),
    totalDegree_mul_of_isDomain hf.ne_zero hg] at h
  exact h

/-- A subspace known to lie in a linear map's kernel subtracts from the image dimension. -/
lemma finrank_map_add_kernel_subspace_le {K M W : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup W] [Module K W]
    (φ : M →ₗ[K] W) (V U : Submodule K M) [Module.Finite K V]
    (hUV : U ≤ V) (hUker : U ≤ φ.ker) :
    Module.finrank K (V.map φ) + Module.finrank K U ≤ Module.finrank K V := by
  have h := φ.finrank_map_add_finrank_inf_ker V
  have hle := Submodule.finrank_mono (le_inf hUV hUker)
  omega

/-- Bounded-degree polynomials in the quotient coordinate ring: the image in `K[X] ⧸ I` of the
polynomials of total degree at most `N`. For `K = ℚ` its dimension is
`CCDN.affineHilbertFunction I N`. -/
def filteredCoordinateSpace {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) : Submodule K (MvPolynomial σ K ⧸ I) :=
  (restrictTotalDegree σ K N).map (Ideal.Quotient.mkₐ K I).toLinearMap

instance filteredCoordinateSpace_finite {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) : Module.Finite K (filteredCoordinateSpace I N) := by
  unfold filteredCoordinateSpace
  infer_instance

/-- Curve degree via the filtered Hilbert function: the dimension of the bounded-degree part
of the coordinate ring is eventually `d * M + c`. Over `ℚ` with `σ = Fin n` this is
`CCDN.HasAffineCurveDegree`. -/
def HasFilteredCurveDegree {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) (d : ℕ) :
    Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M ≥ N,
    (Module.finrank K (filteredCoordinateSpace I M) : ℤ) = (d : ℤ) * M + c

/-- A lower bound along positive-step filtered pieces cannot grow faster than the
curve's eventual linear Hilbert function. -/
theorem HasFilteredCurveDegree.le_mul_of_growth {K σ : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {d r m D : ℕ} (hdegree : HasFilteredCurveDegree I d)
    (hm : 0 < m)
    (hlower : ∀ N : ℕ,
      r * (N + 1) ≤ Module.finrank K (filteredCoordinateSpace I (D + m * N))) :
    r ≤ d * m := by
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra hbad
  have hcard : d * m + 1 ≤ r := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have he := hN₀ (D + m * N) (by
    have hN : N₀ ≤ N := by dsimp [N]; omega
    nlinarith)
  push_cast at he
  have hlo : (r : ℤ) * (N + 1) ≤ (d : ℤ) * (D + m * N) + c := by
    rw [← he]
    exact_mod_cast hlower N
  have hmul : ((d : ℤ) * m + 1) * (N + 1) ≤ (r : ℤ) * (N + 1) := by
    exact_mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

/-- The filtered Koszul rank bound, before evaluating the monomial-space dimensions.
It applies to every ideal containing the two equations. -/
theorem filteredCoordinateSpace_finrank_bound {K σ : Type*} [Field K] [Finite σ]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial σ K)) (hIf : f ∈ I) (hIg : g ∈ I)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace I N) +
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) +
      Module.finrank K (restrictTotalDegree σ K (N - g.totalDegree)) ≤
      Module.finrank K (restrictTotalDegree σ K N) +
      Module.finrank K (restrictTotalDegree σ K (N - (f.totalDegree + g.totalDegree))) := by
  let φ := (Ideal.Quotient.mkₐ K I).toLinearMap
  have hker (p : MvPolynomial σ K) (hp : p ∈ I) : filteredMultiples p N ≤ φ.ker := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := (mem_filteredMultiples p x N).mp hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact I.mul_mem_right u hp
  have hbound := finrank_map_add_kernel_subspace_le φ (restrictTotalDegree σ K N)
    (filteredMultiples f N ⊔ filteredMultiples g N)
    (sup_le (filteredMultiples_le_degree f (by omega))
      (filteredMultiples_le_degree g (by omega)))
    (sup_le (hker f hIf) (hker g hIg))
  have heq := filteredMultiples_sup_finrank hf hfg hN
  change Module.finrank K (filteredCoordinateSpace I N) + _ ≤ _ at hbound
  omega

/-- Lift a basis of the filtered coordinate ring to bounded-degree polynomials. -/
theorem exists_filtered_polynomial_basis {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (D : ℕ) :
    ∃ h : Fin (Module.finrank K (filteredCoordinateSpace I D)) → MvPolynomial σ K,
      (∀ i, (h i).totalDegree ≤ D) ∧
      LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K I) (h i)) := by
  classical
  let b := Module.finBasis K (filteredCoordinateSpace I D)
  have hlift (i : Fin (Module.finrank K (filteredCoordinateSpace I D))) :
      ∃ h : MvPolynomial σ K, h.totalDegree ≤ D ∧
        (Ideal.Quotient.mkₐ K I) h = (b i).val := by
    obtain ⟨h, hh, he⟩ := Submodule.mem_map.mp (b i).property
    exact ⟨h, (mem_restrictTotalDegree _ _ _).mp hh, he⟩
  choose h hd he using hlift
  refine ⟨h, hd, ?_⟩
  simp only [he]
  exact b.linearIndependent.map' (filteredCoordinateSpace I D).subtype (Submodule.ker_subtype _)

/-- Enlarging the ideal can only shrink the filtered pieces of the coordinate ring. -/
lemma filteredCoordinateSpace_finrank_antitone_ideal
    {K σ : Type*} [Field K] [Finite σ]
    (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace J N) ≤
      Module.finrank K (filteredCoordinateSpace I N) := by
  classical
  let := Fintype.ofFinite σ
  let φ : (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
    Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J)
      (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hf))
  have hmap : (filteredCoordinateSpace I N).map φ.toLinearMap =
      filteredCoordinateSpace J N := by
    ext x
    constructor
    · rintro ⟨a, ⟨f, hf, rfl⟩, rfl⟩
      exact Submodule.mem_map.mpr ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact Submodule.mem_map.mpr ⟨Ideal.Quotient.mk I f,
        Submodule.mem_map.mpr ⟨f, hf, rfl⟩, rfl⟩
  have hh := finrank_map_add_kernel_subspace_le φ.toLinearMap
    (filteredCoordinateSpace I N) ⊥ bot_le bot_le
  rw [hmap] at hh
  simpa only [finrank_bot, add_zero] using hh

end
end CCDN
